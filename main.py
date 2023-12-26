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
	if "fischer_4" in string:
		files = [f"benchmarks/{string}/aut1",f"benchmarks/{string}/aut2",f"benchmarks/{string}/aut3",f"benchmarks/{string}/aut4"]
		global_vars = []
		local_vars = ["x0"]
	elif "nrs" in string:
		files = [f"benchmarks/{string}/rod_1",f"benchmarks/{string}/rod_2",f"benchmarks/{string}/rod_3",
		f"benchmarks/{string}/rod_4",f"benchmarks/{string}/rod_5",f"benchmarks/{string}/controller"]
		global_vars = []
		local_vars = ["x"]
	elif "tank" in string:
		files = [f"benchmarks/{string}/tank",f"benchmarks/{string}/burner",f"benchmarks/{string}/thermometer"]
		global_vars = ["x"]
		local_vars = ["y","z"]
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
for depth in range(1,n+1):
	S = z3.Solver()
	print(f"Checking depth {depth}.")
	for i in range(len(files)):
		S = generate_constraints(graphs[i], S, depth, files[i]+".cfg")

	stutter, shared, local = get_all_vars(graphs, files, S, depth) # Get all variable names
	#S = pruning_constraints(graphs, files, S, stutter, shared, local, depth)

	# Getting and printing the model for the run
	paths = []
	count = 0
	counterexample = []
	while str(S.check()) == "sat":
		m = S.model()
		negation(S, m, paths)
		aut_path = retrieve_path(graphs, files, paths[count], depth)
		stutter_free_path = stutter_free(aut_path)
		print("Retrieved path:", stutter_free_path)
		#for i in aut_path:
		#	print(f"{i}: {aut_path[i]}")
		#counterexample = check_feasibility(aut_path, graphs, automata, files, config, T, shared, global_vars, local_vars, depth)
		count = count+1
		if counterexample != []:
			break
	total = total + count
	if counterexample != []:
		break

if counterexample == []:
    print("Safe.")
else:
	for d in counterexample.decls():
		print(f"{d.name()} = {counterexample[d]}")
	plot_CE(graphs, automata, counterexample, var, config, stutter_free_path)

	'''
	for n in range(depth+1):
		for i in counterexample.decls():
			if f"_{n}" in str(i):
				print(f"{i} = {counterexample[i]}")
	'''

print(f"Number of paths checked = {total}.")
