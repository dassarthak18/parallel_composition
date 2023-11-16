import z3
import matplotlib.pyplot as plt
import sys

from constraints import *

# Reading graphs for individual automata in the hybrid system
#files = ["benchmarks/nuclear_reactor/rod_1","benchmarks/nuclear_reactor/rod_2","benchmarks/nuclear_reactor/controller"]
files = ["benchmarks/nuclear_reactor/controller"]

try:
	n = int(sys.argv[1])
	opt = int(sys.argv[2])
except:
  print("Please enter the depth of BMC and whether to set path pruning-based opimization as command line arguments.")
  exit(0)

graphs = []
for i in files:
	graphs.append(read_graph(i+".txt"))

automata = []
for i in files:
	automata.append(read_automata(i))
print(automata)

# Creating a single solver for the entire system
S = z3.Solver()
total = 0 # total number of paths

# Generating the constraints for a run of the SAT solver
for depth in range(1, n+1):
	for i in range(len(files)):
		S = generate_constraints(graphs[i], S, depth, files[i]+".cfg")

	if opt == 1:
		stutter, shared, local = get_all_vars(graphs, files, S, depth) # Get all variable names
		S = pruning_constraints(graphs, files, S, stutter, shared, local, depth)

	# Getting and printing the model for the run
	paths = []
	count = 0
	if str(S.check()) == "sat":
		print(f"Depth = {depth}.")
	while str(S.check()) == "sat":
		m = S.model()
		negation(S, m, paths)
		print(f"Retrieved path {count+1}:", paths[count])
		#print(f"\nRetrieved path {count+1}.")
		#print_path(graphs, files, paths[count], depth)
		#print()
		count = count+1
	total = total + count
	S.reset()

print(f"\nTotal number of paths = {total}.")