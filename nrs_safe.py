import z3
import sys

from constraints import *

# Reading graphs for individual automata in the hybrid system
files = ["benchmarks/nrs_5_safe/rod_1","benchmarks/nrs_5_safe/rod_2","benchmarks/nrs_5_safe/rod_3",
		"benchmarks/nrs_5_safe/rod_4","benchmarks/nrs_5_safe/rod_5","benchmarks/nrs_5_safe/controller"]
config = "benchmarks/nrs_5_safe/config.txt"

try:
	n = int(sys.argv[1])
	T = float(sys.argv[2])
	var = str(sys.argv[3])
except:
	print(sys.argv) # for debug
	print("Please enter the depth of BMC, time horizon and variable for plotting as command line arguments.")
	exit(0)

graphs = []
for i in files:
	graphs.append(read_graph(i+".txt"))

automata = []
for i in files:
	automata.append(read_automata(i))

# Creating a single solver for the entire system
total = 0 # total number of paths
counterexample = []

# Generating the constraints for a run of the SAT solver
for depth in range(1, n+1):
	S = z3.Solver()
	print(f"Checking depth {depth}.")
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
		#print("Retrieved path:", aut_path)
		#for i in aut_path:
		#	print(f"{i}: {aut_path[i]}")
		check = check_feasibility(aut_path, graphs, automata, files, config, T, shared, ["x"], depth)
		count = count+1
		if counterexample != []:
			break
	total = total + count
	if counterexample != []:
		break

if counterexample == []:
    print("Safe.")

print(f"Number of paths checked = {total}.")
