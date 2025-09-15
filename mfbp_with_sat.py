from pysat.solvers import Glucose3
from pysat.formula import CNF
from pypblib import pblib
from pypblib.pblib import PBConfig, AuxVarManager, VectorClauseDatabase, WeightedLit, PBConstraint, Pb2cnf
from inputParser import InputParser

class MFBPwithSAT:
    """Maximum Flow Blocker Problem solver using SAT encoding."""
    
    def __init__(self):
        self.solver = Glucose3()
        self.cnf = CNF()
        self.solution = None
        self.nodes = [] # List to store node IDs
        self.links = {} # List of (head, tail) tuples
        self.capacities = {} # (head, tail) -> capacity
        self.blocker_costs = {} # (head, tail) -> blocker cost
        self.source = None # Source node ID
        self.destination = None # Destination node ID
        self.block_vars = {} # (head, tail) -> blocking variable, = 1 if link is blocked
        self.mc_vars = {} # (head, tail) -> minimum cut variable, = 1 if link is in min cut
        self.source_vars = {} # (node_id) -> source side variable, = 1 if node is in source side
        self.next_aux_var = 1 # Counter for auxiliary variables
        self.target_flow = None # threshold that the max flow should not exceed
        self.duality_vars = {} # (node_id) -> dual variable for node
        
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
        
        # Minimum cut variables
        for (head, tail) in self.links:
            var = self.allocate_variables(1)
            self.mc_vars[(head, tail)] = var
        
        # Source side variables
        for node in self.nodes:
            var = self.allocate_variables(1)
            self.source_vars[node] = var

    def create_flow_conservation_constraints(self):
        #Create constraints: source_vars[source] = 1, source_vars[sink] = 0
        self.cnf.append([self.source_vars[self.source]])  # source_vars[source] = 1
        self.cnf.append([-self.source_vars[self.destination]])  # source_vars[sink]
        
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
    
    def create_target_flow_constraint(self):
        """Create the target flow constraint using a pseudo-Boolean constraint."""
        # Create a pseudo-Boolean constraint for the target flow
        config = PBConfig()
        aux_var_manager = AuxVarManager(self.next_aux_var)
        clause_database = VectorClauseDatabase(config)
        weight_literals = []
        
        for (head, tail) in self.links:
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
        
    def create_objective_constraint(self, budget):
        """Create the budget constraint using a pseudo-Boolean constraint."""
        # Create a pseudo-Boolean constraint for the budget
        config = PBConfig()
        aux_var_manager = AuxVarManager(self.next_aux_var)
        clause_database = VectorClauseDatabase(config)
        weight_literals = []
        
        for (head, tail) in self.links:
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
        
    def solve_with_binary_search(self):
        """Solve the MFBP using binary search"""
        print("Starting SAT solver...")
        
        #Set parameters
        self.set_next_aux_var(1)
        
        #Calculate the possible range of budget
        c_min = 0
        c_max = sum(self.blocker_costs.values())

        #Create variables and fixed constraints
        print("Creating variables and fixed constraints...")
        self.create_variables()
        self.create_flow_conservation_constraints()
        self.create_target_flow_constraint()
        
        # Store the number of clauses after fixed constraints
        fixed_clause_count = len(self.cnf.clauses)
        
        while c_min < c_max:
            c_mid = (c_min + c_max) // 2
            print(f"Trying budget: {c_mid}")
            # Reset CNF to fixed clauses
            self.cnf.clauses = self.cnf.clauses[:fixed_clause_count]
            self.create_objective_constraint(c_mid)
            self.solver.append_formula(self.cnf)
            
            if self.solver.solve():
                print(f"Found solution for blocker cost: {c_mid}")
                c_max = c_mid
                self.solution = self.solver.get_model()
            else:
                print(f"No solution for blocker cost: {c_mid}")
                c_min = c_mid + 1
                
            if (c_min < c_max):
                print("Resetting solver for next iteration...")
                self.solver.delete()
                self.solver = Glucose3()
                
        if self.solution is not None:
            print(f"Optimal blocker cost found: {c_max}")
            blocked_links = [(head, tail) for (head, tail), var in self.block_vars.items() if var in self.solution]
            print(f"Links to block: {blocked_links}")
            return blocked_links, c_max
        else:
            print("No solution found within the given budget.")
            return None
        
def solve_mfbp(folder_path):
    """Main function to solve MFBP from input files."""
    parser = InputParser(folder_path)
    data = parser.parse_all()
        
    nodes = data['nodes']
    links = data['links']
    capacities = data['capacities']
    blocker_costs = data['blocker_costs']
    source = data['source']
    destination = data['destination']
        
    # Initialize MFBP solver
    mfbp_solver = MFBPwithSAT()
    mfbp_solver.nodes = nodes
    mfbp_solver.links = links
    mfbp_solver.capacities = capacities
    mfbp_solver.blocker_costs = blocker_costs
    mfbp_solver.source = source
    mfbp_solver.destination = destination
        
    # Set target flow (for example, 0 to completely block the flow)
    mfbp_solver.target_flow = 0
        
    # Solve MFBP using binary search
    blocked_links, optimal_cost = mfbp_solver.solve_with_binary_search()
        
    return blocked_links, optimal_cost

if __name__ == "__main__":
    input_folder = "input/Example"  # Folder containing input data
    blocked_links, optimal_cost = solve_mfbp(input_folder)
    print(f"Blocked links: {blocked_links}")
    print(f"Optimal blocker cost: {optimal_cost}")
        