import z3
import sys

from constraints import *

# Reading graphs for individual automata in the hybrid system
try:
	string = str(sys.argv[1])
	n = int(sys.argv[2])
	T = float(sys.argv[3])
	var = str(sys.argv[4])
	config = f"benchmarks/{string}/config.txt"
	if "fddi_5" in string: 
		files = [f"benchmarks/{string}/p1",f"benchmarks/{string}/p2",f"benchmarks/{string}/p3",
		f"benchmarks/{string}/p4",f"benchmarks/{string}/p5"]
		var_names = ["x","y","z"]
	elif "fischer_4" in string:
		files = [f"benchmarks/{string}/p1",f"benchmarks/{string}/p2",f"benchmarks/{string}/p3",f"benchmarks/{string}/p4"]
		var_names = ["x", "svl", "svr"]
	elif "nrs" in string:
		files = [f"benchmarks/{string}/rod_1",f"benchmarks/{string}/rod_2",f"benchmarks/{string}/rod_3",
		f"benchmarks/{string}/rod_4",f"benchmarks/{string}/rod_5",f"benchmarks/{string}/controller"]
		var_names = ["x"]
except:
	print(sys.argv) # for debug
	print("Please enter the name of the benchmark, depth of BMC, time horizon and variable for plotting as command line arguments.")
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
	#S = pruning_constraints(graphs, files, S, stutter, shared, local, depth)

	# Getting and printing the model for the run
	paths = []
	count = 0
	while str(S.check()) == "sat":
		m = S.model()
		negation(S, m, paths)
		aut_path = retrieve_path(graphs, files, paths[count], depth)
		print("Retrieved path:", aut_path)
		#for i in aut_path:
		#	print(f"{i}: {aut_path[i]}")
		counterexample = check_feasibility(aut_path, graphs, automata, files, config, T, shared, var_names, depth)
		count = count+1
		if counterexample != []:
			break
	total = total + count
	if counterexample != []:
		break

if counterexample == []:
    print("Safe.")
else:
	stutter_free_path = stutter_free(aut_path)
	#for d in counterexample.decls():
	#	print(f"{d.name()} = {counterexample[d]}")
	plot_CE(graphs, automata, counterexample, var, config, stutter_free_path)

print(f"Number of paths checked = {total}.")
