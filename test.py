import z3
import matplotlib.pyplot as plt
import sys

from constraints import *

# Reading graphs for individual automata in the hybrid system
files = ["benchmarks/test/test"]
config = "benchmarks/test/config.txt"

try:
	n = int(sys.argv[1])
	T = int(sys.argv[2])
except:
  print("Please enter the depth of BMC and time horizon as command line arguments.")
  exit(0)

graphs = []
for i in files:
	graphs.append(read_graph(i+".txt"))

automata = []
for i in files:
	automata.append(read_automata(i))

# Creating a single solver for the entire system
S = z3.Solver()
total = 0 # total number of paths

# Generating the constraints for a run of the SAT solver
for depth in range(1, n+1):
	for i in range(len(files)):
		S = generate_constraints(graphs[i], S, depth, files[i]+".cfg")

	stutter, shared, local = get_all_vars(graphs, files, S, depth) # Get all variable names
	S = pruning_constraints(graphs, files, S, stutter, shared, local, depth)

	# Getting and printing the model for the run
	paths = []
	count = 0
	while str(S.check()) == "sat":
		m = S.model()
		negation(S, m, paths)
		aut_path = retrieve_path(graphs, files, paths[count], depth)
		print(aut_path)
		check_feasibility(aut_path, graphs, automata, files, config, T, shared, depth)
		count = count+1
		break
	total = total + count
	S.reset()

print(f"Number of paths checked = {total}.")