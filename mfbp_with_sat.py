from pysat.solvers import Glucose3
from pysat.formula import CNF
from pypblib import pblib
from pypblib.pblib import PBConfig, AuxVarManager, VectorClauseDatabase, WeightedLit, PBConstraint, Pb2cnf
from inputParser import InputParser
from max_flow import calculate_max_flow
import pandas as pd
import json
import os
import timeit
import sys
import signal
import threading

# Global variables to track results
start = 0
best_solution = None
instance_name = ""

# Signal handler for graceful interruption
def handle_interrupt(signum, frame):
    print(f"\nReceived interrupt signal {signum}. Saving current solution.")
    
    if best_solution is not None:
        result = {
            'Instance': instance_name,
            'Target_Flow': best_solution.get('target_flow'),
            'Optimal_Cost': best_solution.get('blocker_cost'),
            'Runtime': timeit.default_timer() - start,
            'Status': 'TIMEOUT'
        }
        save_result_to_excel(result)
    
    sys.exit(0)

# Register signal handlers
signal.signal(signal.SIGTERM, handle_interrupt)
signal.signal(signal.SIGINT, handle_interrupt)

def save_result_to_excel(result):
    """Lưu kết quả vào file Excel"""
    excel_file = 'MFBP_SAT_Results.xlsx'
    
    try:
        if os.path.exists(excel_file):
            existing_df = pd.read_excel(excel_file)
            # Kiểm tra xem combination của Instance + Target_Flow đã tồn tại chưa
            instance_target_exists = False
            instance_idx = -1
            
            for idx, row in existing_df.iterrows():
                if row['Instance'] == result['Instance'] and row['Target_Flow'] == result['Target_Flow']:
                    instance_target_exists = True
                    instance_idx = idx
                    break
            
            if instance_target_exists:
                # Cập nhật entry đã tồn tại
                for key, value in result.items():
                    existing_df.at[instance_idx, key] = value
            else:
                # Thêm entry mới
                result_df = pd.DataFrame([result])
                existing_df = pd.concat([existing_df, result_df], ignore_index=True)
        else:
            # Tạo DataFrame mới nếu chưa có file Excel
            existing_df = pd.DataFrame([result])
        
        # Lưu file Excel
        existing_df.to_excel(excel_file, index=False)
        
    except Exception as e:
        print(f"Error saving to Excel: {str(e)}")

class MFBPwithSAT:
    """Maximum Flow Blocker Problem solver using SAT encoding."""

    def __init__(self, verbose=True, save_to_excel=True, timeout=600, per_iteration_timeout=30):
        """
        Initialize SAT solver for MFBP
        
        Args:
            verbose (bool): If True, print debug information
            save_to_excel (bool): If True, save results to Excel
            timeout (int): Overall timeout in seconds (default 600s = 10 minutes)
            per_iteration_timeout (int): Timeout per solver iteration in seconds (default 30s)
        """
        self.solver = Glucose3()
        self.cnf = CNF()
        self.solution = None
        self.nodes = []
        self.links = {}
        self.capacities = {}
        self.blocker_costs = {}
        self.source = None
        self.destination = None
        self.block_vars = {}
        self.mc_vars = {}
        self.source_vars = {}
        self.next_aux_var = 1
        self.target_flow = None
        self.duality_vars = {}
        self.verbose = verbose
        self.save_to_excel = save_to_excel
        self.timeout = timeout
        self.per_iteration_timeout = per_iteration_timeout  # 🔧 Per-iteration timeout
        self.start_time = None
        
    def set_next_aux_var(self, next_var):
        """Set the next auxiliary variable ID."""
        self.next_aux_var = next_var

    def allocate_variables(self, count):
        start = self.next_aux_var
        self.next_aux_var += count
        return start
    
    def create_variables(self):
        """Create SAT variables for blocking decisions, min cut, and source side."""
        # Blocking variables
        for (head, tail) in self.links:
            var = self.allocate_variables(1)
            self.block_vars[(head, tail)] = var
            if head == self.source or tail == self.destination:
                self.cnf.append([-var])  # Force blocking variable to be fail (link cannot be blocked)
        
        # Minimum cut variables
        for (head, tail) in self.links:
            var = self.allocate_variables(1)
            self.mc_vars[(head, tail)] = var
            if head == self.source or tail == self.destination:
                self.cnf.append([-var])  # Force min cut variable to be fail (link cannot be in min cut)
        
        # Source side variables
        for node in self.nodes:
            var = self.allocate_variables(1)
            self.source_vars[node] = var
        
        if self.verbose:
            print(f"[Variables] Total variables created: {self.next_aux_var - 1}")
            print(f"[Clauses] After variable creation: {len(self.cnf.clauses)}")

    def create_flow_conservation_constraints(self):
        #Create constraints: source_vars[source] = 1, source_vars[sink] = 0
        self.cnf.append([-self.source_vars[self.source]])  # source_vars[source] = 1
        self.cnf.append([self.source_vars[self.destination]])  # source_vars[sink]
        
        #create duality variable for each tail of each link
        for (head, tail) in self.links:
            if tail not in self.duality_vars:
                var = self.allocate_variables(1)
                self.duality_vars[tail] = var
                #Create constraint for duality variable of source: 
                #Exactly one between duality_vars and source_vars of the tail of each link must be true
                self.cnf.append([self.source_vars[tail], self.duality_vars[tail]])
                self.cnf.append([-self.source_vars[tail], -self.duality_vars[tail]])
        
        #Create constriants for each link: 
        # mc_var + block_var + source_var(head) + duality_var(tail) >= 1 (at least one is true)
        for (head, tail) in self.links:
            self.cnf.append([self.mc_vars[(head, tail)], self.block_vars[(head, tail)], self.source_vars[head], self.duality_vars[tail]])
        
        if self.verbose:
            print(f"[Variables] After flow conservation: {self.next_aux_var - 1}")
            print(f"[Clauses] After flow conservation: {len(self.cnf.clauses)}")
    
    def create_target_flow_constraint(self):
        """Create the target flow constraint using a pseudo-Boolean constraint."""
        # Create a pseudo-Boolean constraint for the target flow
        config = PBConfig()
        aux_var_manager = AuxVarManager(self.next_aux_var)
        clause_database = VectorClauseDatabase(config)
        weight_literals = []
        
        for (head, tail) in self.links:
            if head == self.source or tail == self.destination:
                continue  # Skip links with infinite capacity
            var = self.mc_vars[(head, tail)]
            capacity = self.capacities[(head, tail)]
            weight_literals.append(WeightedLit(var, capacity))
            
        constraint = PBConstraint(weight_literals, pblib.LEQ , self.target_flow)
        
        # Encode the pseudo-Boolean constraint to CNF
        pb2cnf = Pb2cnf(config)
        pb2cnf.encode(constraint, clause_database, aux_var_manager)
        
        # Add the generated clauses to the CNF formula
        for clause in clause_database.get_clauses():
            self.cnf.append(clause)
        
        # Update the next auxiliary variable ID
        self.next_aux_var = aux_var_manager.get_biggest_returned_auxvar() + 1
        
        if self.verbose:
            print(f"[Variables] After target flow constraint: {self.next_aux_var - 1}")
            print(f"[Clauses] After target flow constraint: {len(self.cnf.clauses)}")
        
    def create_objective_constraint(self, budget):
        """Create the budget constraint using a pseudo-Boolean constraint."""
        # Create a pseudo-Boolean constraint for the budget
        config = PBConfig()
        aux_var_manager = AuxVarManager(self.next_aux_var)
        clause_database = VectorClauseDatabase(config)
        weight_literals = []
        
        for (head, tail) in self.links:
            if head == self.source or tail == self.destination:
                continue  # Skip links with infinite blocker cost
            var = self.block_vars[(head, tail)]
            cost = self.blocker_costs[(head, tail)]
            weight_literals.append(WeightedLit(var, cost))
            
        constraint = PBConstraint(weight_literals, pblib.LEQ, budget)
        
        # Encode the pseudo-Boolean constraint to CNF
        pb2cnf = Pb2cnf(config)
        pb2cnf.encode(constraint, clause_database, aux_var_manager)
        
        # Add the generated clauses to the CNF formula
        for clause in clause_database.get_clauses():
            self.cnf.append(clause)
        
        # Update the next auxiliary variable ID
        self.next_aux_var = aux_var_manager.get_biggest_returned_auxvar() + 1
        
        if self.verbose:
            print(f"[Variables] After objective constraint (budget={budget}): {self.next_aux_var - 1}")
            print(f"[Clauses] After objective constraint: {len(self.cnf.clauses)}")

    def solve_with_binary_search(self):
        """Solve the MFBP using binary search for optimal budget."""
        if self.verbose:
            print("Starting SAT solver with binary search...")
        
        self.start_time = timeit.default_timer()
        # Set parameters
        self.set_next_aux_var(1)
        
        # Calculate the possible range of budget
        c_min = 0
        c_max = sum(self.blocker_costs[(head, tail)] for (head, tail) in self.links 
                    if head != self.source and tail != self.destination)
        c_optimal = 0
        
        # Create variables and fixed constraints
        if self.verbose:
            print("Creating variables and fixed constraints...")
        self.create_variables()
        self.create_flow_conservation_constraints()
        self.create_target_flow_constraint()
        
        # Store the number of clauses after fixed constraints
        fixed_clause_count = len(self.cnf.clauses)
        
        # Binary search for minimum budget
        iteration = 0
        while c_min <= c_max:
            iteration += 1
            elapsed = timeit.default_timer() - self.start_time
            if elapsed > self.timeout:
                if self.verbose:
                    print(f"Overall timeout reached after {elapsed:.2f}s during binary search.")
                break
                
            c_mid = (c_min + c_max) // 2
            if self.verbose:
                print(f"[Iteration {iteration}] Trying budget: {c_mid} (range: {c_min} - {c_max})")
            
            # Reset CNF to fixed clauses
            self.cnf.clauses = self.cnf.clauses[:fixed_clause_count]
            self.create_objective_constraint(c_mid)
            self.solver.append_formula(self.cnf)
            
            if self.verbose:
                print(f"  [SAT] Variables: {self.next_aux_var - 1}, Clauses: {len(self.cnf.clauses)}")
            
            try:
                # 🔧 Use per-iteration timeout
                solve_timeout = min(self.per_iteration_timeout, self.timeout - elapsed)
                if solve_timeout <= 0:
                    if self.verbose:
                        print("Overall time expired.")
                    break
                
                # 🔧 Try to solve with timeout handling
                solve_start = timeit.default_timer()
                if self.verbose:
                    print(f"  [Solver] Starting solve with {solve_timeout:.1f}s timeout...")
                
                # Call solve and capture result
                solve_result = self.solver.solve()
                
                solve_elapsed = timeit.default_timer() - solve_start
                if self.verbose:
                    print(f"  [Solver] Completed in {solve_elapsed:.2f}s. Result: {solve_result}")
                
                if solve_result:
                    result = self.solver.get_model()
                    blocked_links = [(head, tail) for (head, tail), var in self.block_vars.items() if var in result]
                    blocker_cost = sum(self.blocker_costs[(head, tail)] for (head, tail) in blocked_links)
                
                    self.solution = result
                    c_optimal = c_mid
                    
                    if self.verbose:
                        print(f"  ✓ Found solution. Cost: {blocker_cost}")
                    
                    # Try to find smaller budget
                    c_max = c_mid - 1
                else:
                    if self.verbose:
                        print(f"  ✗ No solution (budget too small)")
                    # Budget is too small, try larger
                    c_min = c_mid + 1
                
                if c_min <= c_max:
                    if self.verbose:
                        print(f"  Resetting solver for next iteration...\n")
                    self.solver.delete()
                    self.solver = Glucose3()
                    
            except Exception as e:
                if self.verbose:
                    print(f"  [ERROR] {str(e)}")
                # If solver fails, try larger budget
                c_min = c_mid + 1
                try:
                    self.solver.delete()
                except:
                    pass
                self.solver = Glucose3()
        
        # Return the best solution found
        if self.solution is not None:
            blocked_links = [(head, tail) for (head, tail), var in self.block_vars.items() if var in self.solution]
            blocker_cost = sum(self.blocker_costs[(head, tail)] for (head, tail) in blocked_links)
            
            if self.verbose:
                print(f"\n✓ Optimal blocker cost: {blocker_cost} (budget: {c_optimal})\n")
            
            return blocked_links, blocker_cost
        else:
            if self.verbose:
                print(f"\n✗ No solution found within timeout.\n")
            
            return None

def solve_mfbp(folder_path):
    """Main function to solve MFBP from input files."""
    global start, instance_name
    
    parser = InputParser(folder_path)
    data = parser.parse_all()
        
    nodes = data['nodes']
    links = data['links']
    capacities = data['capacities']
    blocker_costs = data['blocker_costs']
    source = data['source']
    destination = data['destination']
    
    # Lấy tên instance từ folder_path
    instance_name = folder_path.split('/')[-1]
        
    # Calculate maximum flow
    max_flow_value, flow_dict = calculate_max_flow(folder_path)
    print(f"Maximum flow in the original network: {max_flow_value}")
    
    # Define target flow ratios to try
    target_flow_ratios = [0.6, 0.9]
    
    # Try each target flow ratio
    for ratio in target_flow_ratios:
        # Initialize MFBP solver for each target flow
        # 🔧 Set timeout=120 (2 minutes overall), per_iteration_timeout=20 (20 seconds per iteration)
        mfbp_solver = MFBPwithSAT(
            verbose=True, 
            save_to_excel=True, 
            timeout=120,
            per_iteration_timeout=20
        )
        mfbp_solver.nodes = nodes
        mfbp_solver.links = links
        mfbp_solver.capacities = capacities
        mfbp_solver.blocker_costs = blocker_costs
        mfbp_solver.source = source
        mfbp_solver.destination = destination
        mfbp_solver.target_flow = int(max_flow_value * ratio)
        
        print(f"\n{'='*60}")
        print(f"Solving with target flow: {mfbp_solver.target_flow} ({ratio*100}% of max flow)")
        print(f"{'='*60}")
        
        # Start timer AFTER initialization
        start = timeit.default_timer()
        
        # Solve MFBP using binary search
        result = mfbp_solver.solve_with_binary_search()
        
        runtime = timeit.default_timer() - start
        
        # Only save to Excel if flag is True
        if mfbp_solver.save_to_excel:
            if result is not None:
                blocked_links, blocker_cost = result
                excel_result = {
                    'Instance': instance_name,
                    'Target_Flow': mfbp_solver.target_flow,
                    'Target_Flow_Ratio': f"{ratio*100}%",
                    'Max_Flow_Original': max_flow_value,
                    'Optimal_Cost': blocker_cost,
                    'Runtime': runtime,
                    'Links_Blocked': len(blocked_links),
                    'Status': 'COMPLETE'
                }
            else:
                excel_result = {
                    'Instance': instance_name,
                    'Target_Flow': mfbp_solver.target_flow,
                    'Target_Flow_Ratio': f"{ratio*100}%",
                    'Max_Flow_Original': max_flow_value,
                    'Optimal_Cost': None,
                    'Runtime': runtime,
                    'Links_Blocked': 0,
                    'Status': 'TIMEOUT/NO_SOLUTION'
                }
            
            save_result_to_excel(excel_result)
        
        print(f"Runtime: {runtime:.4f}s")
    
    return None

if __name__ == "__main__":
    #input_folder = "input/Not/RANDOM_40_0.6_3_0"
    input_folder = "input/NETWORKS/B/MDVADB1_B1"
    solve_mfbp(input_folder)