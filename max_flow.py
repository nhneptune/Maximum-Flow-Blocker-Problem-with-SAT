import networkx as nx
from inputParser import InputParser

def calculate_max_flow(folder_path):
    """Calculate maximum flow in the network using NetworkX"""
    
    # Parse input data
    parser = InputParser(folder_path)
    data = parser.parse_all()
    parser.print_summary()
    
    # Create directed graph
    G = nx.DiGraph()
    
    # Define infinite capacity value from input files
    INFINITE_CAPACITY = 50000000
    
    # Add edges with capacities
    for (head, tail) in data['links']:
        capacity = data['capacities'][(head, tail)]
        # Chỉ xét các cạnh có capacity hữu hạn
        if capacity < INFINITE_CAPACITY:
            G.add_edge(head, tail, capacity=capacity)
        else:
            # Với cạnh có capacity vô cùng, sử dụng một giá trị đủ lớn
            large_capacity = sum(
                cap for cap in data['capacities'].values() 
                if cap < INFINITE_CAPACITY
            )
            G.add_edge(head, tail, capacity=large_capacity)
    
    # Calculate maximum flow
    max_flow_value, flow_dict = nx.maximum_flow(
        G,
        data['source'],
        data['destination']
    )
    
    # Print results
    print(f"\nMaximum flow value: {max_flow_value}")
    print("\nFlow on each edge:")
    for (head, tail) in data['links']:
        flow = flow_dict[head][tail]
        # In thêm thông tin về capacity của cạnh
        capacity = data['capacities'][(head, tail)]
        inf_mark = " (infinite)" if capacity >= INFINITE_CAPACITY else ""
        print(f"Edge ({head}, {tail}): flow = {flow}, capacity = {capacity}{inf_mark}")
    
    return max_flow_value, flow_dict

if __name__ == "__main__":
    # Test with example input
    input_folder = "input/RANDOM_20_0.4_3_0"
    #input_folder = "input/Example"
    max_flow_value, flow_dict = calculate_max_flow(input_folder)