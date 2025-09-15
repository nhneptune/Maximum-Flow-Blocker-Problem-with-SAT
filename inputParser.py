# node.csv file contains a single column that lists the ID of each node
# link.csv file reports all information related to the links in the network. Each row corresponds to a link and includes the link ID, the node ID of the head and an associated integer value, the node ID of the tail and another associated integer value, the capacity of the link, and the blocker cost of each link.
# service.txt file consists of a single line with two numbers separated by a semicolon ;. The first number represents the node ID of the source, and the second number represents the node ID of the destination.

import csv
import os

class InputParser:
    def __init__(self, input_folder_path):
        self.input_folder_path = input_folder_path
        self.nodes = [] # list of node IDs
        self.links = [] # List of (head, tail) tuples
        self.capacities = {} # (head, tail) -> capacity
        self.blocker_costs = {} # (head, tail) -> blocker cost
        self.source = None # Source node ID
        self.destination = None # Destination node ID
    
    def parse_nodes(self):
        """Parse node.csv file to get list of node IDs"""
        node_file_path = os.path.join(self.input_folder_path, 'node.csv')
        
        with open(node_file_path, 'r') as file:
            csv_reader = csv.reader(file)
            # Skip header
            next(csv_reader)
            
            for row in csv_reader:
                node_id = int(row[0])
                self.nodes.append(node_id)
        
        return self.nodes
    
    def parse_links(self):
        """Parse link.csv file to get link information"""
        link_file_path = os.path.join(self.input_folder_path, 'link.csv')
        
        with open(link_file_path, 'r') as file:
            csv_reader = csv.DictReader(file)
            # Skip header
            next(csv_reader)
            
            for row in csv_reader:
                link_id = int(row['LinkId'])
                head_node_id = int(row['srcNodeId'])
                head_value = int(row['srcIntfId'])
                tail_node_id = int(row['dstNodeId'])
                tail_value = int(row['dstIntfId'])
                capacity = int(row['bandwidth'])
                blocker_cost = int(row['cost'])
                
                self.links.append((head_node_id, tail_node_id))
                self.capacities[(head_node_id, tail_node_id)] = capacity
                self.blocker_costs[(head_node_id, tail_node_id)] = blocker_cost

        return True

    def parse_service(self):
        """Parse service.txt file to get source and destination"""
        service_file_path = os.path.join(self.input_folder_path, 'service.txt')
        
        with open(service_file_path, 'r') as file:
            line = file.readline().strip()
            source_dest = line.split(';')
            self.source = int(source_dest[0])
            self.destination = int(source_dest[1])
        
        return self.source, self.destination
    
    def parse_all(self):
        """Parse all input files"""
        self.parse_nodes()
        self.parse_links()
        self.parse_service()
        
        return {
            'nodes': self.nodes,
            'links': self.links,
            'capacities': self.capacities,
            'blocker_costs': self.blocker_costs,
            'source': self.source,
            'destination': self.destination
        }
    
    
    def print_summary(self):
        """Print summary of parsed data"""
        print(f"Number of nodes: {len(self.nodes)}")
        print(f"Number of links: {len(self.links)}")
        print(f"Source node: {self.source}")
        print(f"Destination node: {self.destination}")
        print(f"Nodes: {self.nodes}")
        print("Links summary:")
        for link in self.links:
            print(f"  Link {link['link_id']}: {link['head_node_id']} -> {link['tail_node_id']} (capacity: {link['capacity']}, cost: {link['blocker_cost']})")