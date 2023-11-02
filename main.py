import z3
import matplotlib.pyplot as plt
import sys

from constraints import *

# Reading graphs for individual automata in the hybrid system
files = ["benchmarks/nuclear_reactor/rod_1","benchmarks/nuclear_reactor/rod_2","benchmarks/nuclear_reactor/controller"]

try:
	depth = int(sys.argv[1])
except:
  print("Please enter the depth of BMC as a command line argument.")
  exit(0)

#files = ["rod_1"]
graphs = []
for i in files:
	graphs.append(read_graph(i+".txt"))

# Creating a single solver for the entire system
S = z3.Solver()

# Generating the constraints for a run of the SAT solver
for i in range(len(files)):
	S = generate_constraints(graphs[i], S, depth, files[i]+".cfg")
	#print(S.check())
#S = exclude(graphs, S, depth)

stutter, shared, local = get_all_vars(graphs, files, S, depth) # Get all variable names
#print(stutter)
#print(shared)
#print(local)
#exit(0)
S = pruning_constraints(graphs, files, S, stutter, shared, local, depth)

# Getting and printing the model for the run
#print(str(S.check()))
paths = []
count = 0
while str(S.check()) == "sat":
	#S.check()
	m = S.model()
	negation(S, m, paths)
	#print(f"Retrieved path {count+1}:", paths[count])
	print(f"\nRetrieved path {count+1}.")
	print_path(graphs, files, paths[count], depth)
	count = count+1
	#for d in m.decls():
	#	if m[d] == True:
	#	    print ("%s = %s" % (d.name(), m[d]))
#print(paths)
print(f"\nNo. of paths retrieved: {count}.")