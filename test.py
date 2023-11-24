import z3
import itertools

from constraints import *

# Function to perform Xor operation
def Xor(a, b):
	return z3.Or(z3.And(z3.Not(a), b), z3.And(z3.Not(b), a))

# Function to get all stuttered paths from a given stutter-free path
def get_all_stutter_perms(lst1, stutters, n):
	k = n - len(lst1)
	perms = [p for p in itertools.product(stutters, repeat=k)]
	permutations = []
	for lst2 in perms:
		for locations in itertools.combinations(range(len(lst1) + len(lst2)), len(lst2)):
			result = lst1[:]
			for location, element in zip(locations, lst2):
				result.insert(location, element)
				string = str('","'.join(map(str, result)))
				if string.count(',') == n-1:
					exec(f'permutations.append(["{string}"])')
	return permutations

# Function to negate a stutter-free path
def stutter_free_negation(graphs, files, S, model, paths, count, depth):
	# Getting the model for this run
	trues = []
	for d in model.decls():
		if model[d] == True:
			trues.append(d.name())

	P = {}
	for j in trues:
		x = j.split('_')
		n = len(x[-1])
		if int(x[-1]) not in P:
			P[int(x[-1])] = [j[:-n-1]]
		else:
			P[int(x[-1])].append(j[:-n-1])
	keys = list(P.keys())
	keys.sort()
	P = {i: P[i] for i in keys}
	paths.append(P)

	'''
	# Negating the stuttered model
	exp = z3.Bool("exp")
	exp = False
	for i in trues:
		if exp == False:
			exp = z3.Bool(i)
		else:
			exp = z3.And(exp,z3.Bool(i))
	S.add(z3.Not(exp))
	'''

	# Negating the stutter-free version of the model
	aut_path = retrieve_path(graphs, files, paths[count], depth)
	#print(f"Stuttered Path: {aut_path}")
	stutter_free_path = stutter_free(aut_path)
	print(f"Stutter-free Path: {stutter_free_path}")
	possible_stutter_paths = {}
	for i in stutter_free_path:
		possible_stutter_paths[i] = get_all_stutter_perms(stutter_free_path[i], stutters, depth)

	for i in possible_stutter_paths:
		for j in possible_stutter_paths[i]:
			num = 1
			exp = z3.Bool("exp")
			exp = False
			for k in j:
				if exp == False:
					exp = z3.Bool(f"{k}_{num}")
				else:
					exp = z3.And(exp,z3.Bool(f"{k}_{num}"))
				num = num+1
			S.add(z3.Not(exp))

	return S

# Reading graphs for individual automata in the hybrid system
files = ["benchmarks/nrs_2/rod_1","benchmarks/nrs_2/rod_2","benchmarks/nrs_2/controller"]
config = "benchmarks/nrs_2/config.txt"

try:
	depth = int(sys.argv[1])
except:
  print("Please enter the depth of BMC as command line argument.")
  exit(0)

graphs = []
for i in files:
	graphs.append(read_graph(i+".txt"))

# Creating a single solver for the entire system
S = z3.Solver()
print(f"Checking depth {depth}.")
for i in range(len(files)):
	S = generate_constraints(graphs[i], S, depth, files[i]+".cfg")
stutter, shared, local = get_all_vars(graphs, files, S, depth) # Get all variable names
stutters = return_depth_free(stutter, depth)
#print(stutters, others)
#S = pruning_constraints(graphs, files, S, stutter, shared, local, depth)

# Getting and printing the model for the run
paths = []
count = 0
while str(S.check()) == "sat":
	m = S.model()
	#negation(S, m, paths)
	#aut_path = retrieve_path(graphs, files, paths[count], depth)
	#print(f"Stuttered Path: {aut_path}")
	#stutter_free_path = stutter_free(aut_path)
	#print(f"Stutter-free Path: {stutter_free_path}")
	stutter_free_negation(graphs, files, S, m, paths, count, depth)
	count = count+1	

print(f"Number of paths checked = {count}.")