import z3
import re
import itertools
import networkx as nx
import numpy as np
import matplotlib.pyplot as plt
import sympy as sp

# Function to read graph from file and store as a networkx graph
def read_graph(filename):
	graph = open(filename, 'r')

	G = nx.MultiDiGraph()
	for line in graph.readlines():
		arr = line.strip().split()
		G.add_edge(arr[0], arr[1], transition=arr[2])

	indices = []
	for i, j in enumerate(filename):
		if j == "/":
			indices.append(i)
	if len(indices) > 0:
		name = filename[indices[-1]+1:-4]
	else:
		name = filename[:-4]

	i = 0
	for n in G.nodes():
		G.add_edge(n,n, transition=f'{name}_stutter_{i}')
		i = i+1

	return G

# Function to read automata specs from file and store as a 2-tuple dictionary
def read_automata(filename):
	locs = open(filename+"_locations.txt", 'r')
	locations = {}
	for line in locs.readlines():
		arr = line.strip().split()
		locations[arr[0]] = [arr[1], arr[2]] # {location: [flow, invariant]}

	trans = open(filename+"_transitions.txt", 'r')
	transitions = {}
	for line in trans.readlines():
		arr = line.strip().split()
		transitions[arr[0]] = [arr[1], arr[2]] # {transition: [guard, reset]}

	return (locations, transitions)

# Function to generate constraints from graph
def generate_constraints(G, S, k, filename):
	clause = open(filename, 'r')
	i = 0
	for line in clause.readlines():
		if i == 0:
			init = line.strip().split() # initial state
			i = i+1
		else:
			dest = line.strip().split() # forbidden state
			i = i+1

	''' INIT Constraints: 
		for all initial states, must include
		either of the outgoing edges in depth 1
	'''
	for n in init:
		exp1 = z3.Bool("exp1")
		exp1 = False
		for i in G.edges(init):
			trans = G[i[0]][i[1]][0]["transition"] # name of the transition
			if exp1 == False:
				exp1 = z3.Bool(f"{trans}_1")
			else:
				exp1 = z3.Or(exp1,z3.Bool(f"{trans}_1"))
		S.add(exp1)

	''' EXCLUDE Constraints: 
		if one edge is active at a given depth,
		no other edge can be active at that depth
	'''
	
	transitions = set()
	for i in G.edges():
		transitions.add(G[i[0]][i[1]][0]["transition"])
	transitions = list(transitions) # list of all transitions in the graph
	for n in range(k):
		for i in transitions:
			exp2a = z3.Bool("exp2a")
			exp2a = False
			for j in transitions:
				if j != i:
					if exp2a == False:
						exp2a = z3.Bool(f"{j}_{n+1}")
					else:
						exp2a = z3.Or(exp2a,z3.Bool(f"{j}_{n+1}"))
			S.add(z3.Implies(z3.Bool(f"{i}_{n+1}"),z3.Not(exp2a)))

	''' NEXT Constraints: 
		if an edge is active at a given depth,
		must include either of the outgoing edges
		from that location in the next depth
	'''
	products = [] # list of all pairs of edges that can occur in a path
	for i in G.nodes():
		in_edges = []
		out_edges = []
		for j in G.in_edges(i):
			in_edges.append(G[j[0]][j[1]][0]["transition"])
		for j in G.out_edges(i):
			out_edges.append(G[j[0]][j[1]][0]["transition"])
		prod = list(itertools.product(in_edges,out_edges))
		products.extend(prod)
	adjacency_dict = {} # adjacency list for products array
	for i in products:
		u, v = i
		if u in adjacency_dict:
			adjacency_dict[u].append(v)
		else:
			adjacency_dict[u] = [v]
	for n in range(k-1):
		for i, j in adjacency_dict.items():
			exp3a = z3.Bool("exp3a")
			exp3a = False
			for x in j:
				if exp3a == False:
					exp3a = z3.Bool(f"{x}_{n+2}")
				else:
					exp3a = z3.Or(exp3a,z3.Bool(f"{x}_{n+2}"))
			S.add(z3.Implies(z3.Bool(f"{i}_{n+1}"),exp3a))

	''' DEST Constraints: 
		at depth k, the edge must be
		an incoming edge of the location
	'''
	dest_edges = set()
	for n in dest:
		for i in G.in_edges(n):
			dest_edges.add(G[i[0]][i[1]][0]["transition"])
	dest_edges = list(dest_edges) # list of all destination edges
	exp4 = z3.Bool("exp4")
	exp4 = False
	for i in dest_edges:
		if exp4 == False:
			exp4 = z3.Bool(f"{i}_{k}")
		else:
			exp4 = z3.Or(exp4,z3.Bool(f"{i}_{k}"))
	S.add(exp4)

	return S

# Function to retrieve all variable names from an expression
def get_vars(expr, var):
	if z3.is_const(expr):
		if expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
			var.add(expr.decl().name())
	else:
		for sub_expr in expr.children():
			get_vars(sub_expr, var)

# Function to retrieve all variable names from a SAT solver
def get_all_vars(graphs, files, S, k):
	var = set()
	for expr in S.assertions():
		get_vars(expr, var)

	stutter = []
	local = []

	for i in var:
		if "stutter" in i:
			stutter.append(i)
		else:
			local.append(i)

	dic ={}
	for i in local:
		dic[i] = 0
	shared = []
	n = len(str(k))
	for i in dic:
		name = i[:-n-1]
		for j in graphs:
			for x in j.edges.data():
				if x[2]['transition'] == name:
					dic[i] = dic[i] + 1
	for i in dic:
		if dic[i] > 1:
			shared.append(i)
			local.remove(i)

	return stutter, shared, local

# Function to generate constraints for path-pruning based optimization
def pruning_constraints(graphs, files, S, stutter, shared, local, k):

	arr = []
	for i in range(k):
		n = len(str(i+1))
		for j in stutter:
			if j[len(j)-n:] == str(i+1):
				arr.append(j[:len(j)-n-1])
	
	stutter_dic = {}
	for i in arr:
		n = i.find("stutter")
		if i[:n-1] in stutter_dic:
			if i not in stutter_dic[i[:n-1]]:
				stutter_dic[i[:n-1]].append(i)
		else:
			stutter_dic[i[:n-1]] = []
	
	shared_dic = {}
	n = len(str(k))
	for i in shared:
		shared_dic[i[:-n-1]] = []
	for i in range(len((graphs))):
		indices = []
		for j, l in enumerate(files[i]):
			if l == "/":
				indices.append(j)
		if len(indices) > 0:
			name = files[i][indices[-1]+1:]
		else:
			name = files[i]
		for j in shared_dic:
			for l in graphs[i].edges.data():
				if l[2]['transition'] == j:
					shared_dic[j].append(name)
					break
	local_dic = {}
	for i in stutter_dic:
		local_dic[i] = set()
	
	for i in range(len(graphs)):
		indices = []
		for j, l in enumerate(files[i]):
			if l == "/":
				indices.append(j)
		if len(indices) > 0:
			name = files[i][indices[-1]+1:]
		else:
			name = files[i]
		for j in local:
			for l in graphs[i].edges.data():
				if l[2]['transition'] in j:
					local_dic[name].add(l[2]['transition'])
					break
	
	''' GLOBAL WAITING
	all member automata are not allowed
	to enable the stutter transition simultaneously
	'''
	glob = list(itertools.product(*stutter_dic.values()))
	for i in range(k):
		for j in glob:
			exp1a = z3.Bool("exp1a")
			exp1a = False
			for x in j:
				if exp1a == False:
					exp1a = z3.Bool(f"{x}_{i+1}")
				else:
					exp1a = z3.And(exp1a, z3.Bool(f"{x}_{i+1}"))
			S.add(z3.Not(exp1a))

	''' REPEATED WAITING FOR SHARED LABELS
	all member automata with this specific shared label are not allowed
	to enable the stutter transition simultaneously
	'''
	for i in range(2, k):
		for j in shared_dic:
			exp2a = z3.Bool("exp2a")
			exp2a = False
			for graph in shared_dic[j]:
				for x in stutter_dic[graph]:
					if exp2a == False:
						exp2a = z3.Not(z3.Bool(f"{x}_{i-1}"))
					else:
						exp2a = z3.Or(exp2a, z3.Not(z3.Bool(f"{x}_{i-1}")))
			S.add(z3.Implies(z3.Bool(f"{j}_{i}"), exp2a))

	'''RANDOM WAITING
	for each member automaton, a stutter transition is allowed,
	if and only if its next label is a shared label or a stutter
	'''
	for i in local_dic:
		for j in local_dic[i]:
			for n in range(2, k):
				exp3a = z3.Bool("exp3a")
				exp3a = False
				for l in stutter_dic[i]:
					if exp3a == False:
						exp3a = z3.Bool(f"{l}_{n-1}")
					else:
						exp3a = z3.Or(exp3a, z3.Bool(f"{l}_{n-1}"))
				S.add(z3.Implies(z3.Bool(f"{j}_{n}"), z3.Not(exp3a)))

	return S

# Function to negate an already retrieved path
def negation(S, model, paths):
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

	# Negating the model
	exp = z3.Bool("exp")
	exp = False
	for i in trues:
		if exp == False:
			exp = z3.Bool(i)
		else:
			exp = z3.And(exp,z3.Bool(i))

	S.add(z3.Not(exp))
	return S

# Function to retrieve the path from returned SAT model
def retrieve_path(graphs, files, p, k):
	aut_path = {}
	for i in range(len(graphs)): # Iterate over every graph
		filename = files[i]
		G = graphs[i]
		indices = []
		for i, j in enumerate(filename):
			if j == "/":
				indices.append(i)
		if len(indices) > 0:
			name = filename[indices[-1]+1:]
		else:
			name = filename
		aut_path[name] = []
		for i in p:
			for j in p[i]:
				for x in G.edges.data():
					if j == x[2]['transition']:
						aut_path[name].append(j)
						break
	return aut_path

# Function to extract coefficients from flow equation
def extract_flow_coefficients(input_string):
	cleaned_string = input_string.replace(' ', '')
	parts = cleaned_string.split('=')
	expression = parts[1]
	matches = re.findall(r'[+-]?\s*\d+\.?\d*|[a-zA-Z]+', expression)
	if len(matches) == 0:
		a = 0
		b = 0
	if len(matches) == 1:
		a = 0
		b = matches[0]
	if len(matches) == 2:
		a = matches[0]
		b = 0
	if len(matches) == 3:
		a = matches[0]
		b = matches[2]
	return str(a), str(b)

# Function to check infeasibility of a retrieved path
def check_feasibility(aut_path, graphs, automata, files, config, T, shared, depth):
	S = z3.Solver()
	shared_dic = {}
	n = len(str(depth))
	for i in shared:
		shared_dic[i[:-n-1]] = []
	for i in range(len((graphs))):
		indices = []
		for j, l in enumerate(files[i]):
			if l == "/":
				indices.append(j)
		if len(indices) > 0:
			name = files[i][indices[-1]+1:]
		else:
			name = files[i]
		for j in shared_dic:
			for l in graphs[i].edges.data():
				if l[2]['transition'] == j:
					shared_dic[j].append(name)
					break

	'''INITIAL CONDITIONS AND
	DWELLING IN FORBIDDEN LOCATION:
	(Assuming that there is a single variable x.)
	'''
	config_file = open(config, 'r')
	count = 0
	for line in config_file.readlines():
		if count == 0:
			init = line.strip().split('&')
		else:
			forbidden = line.strip().split('&')
		count = count+1
	arr = []
	for i in init:
		if "x" not in i:
			j = re.split('(\D)',i)
			j1 = []
			for k in j:
				if k != "":
					j1.append(k)
			var = z3.Real(f"{j1[0]}")
			exec(f"S.add(var{''.join(j1[1:])})")
		else:
			arr.append(i)
	init = arr

	stutter_free_path = {}
	for i in aut_path:
		path = []
		for j in aut_path[i]:
			if "stutter" not in j:
				path.append(j)
		stutter_free_path[i] = path

	for i in stutter_free_path:
		path = stutter_free_path[i]
		n = list(stutter_free_path).index(i)
		G = graphs[n]
		for j in init:
			x = z3.Real(f"{i}_x_0")
			exec(f"S.add({''.join(j)})")
		for j in forbidden:
			if j!="true":
				x = z3.Real(f"{i}_dx_{len(path)}")
				exec(f"S.add({''.join(j)})")
		for j in G.edges.data():
			if (stutter_free_path == j[2]['transition']):
				loc = j[1]
				flow = automata[n][0][loc][0].split("&")
				for f in flow:
					a1, b1 = extract_flow_coefficients(f)
					if not re.match(r"\d+\.*\d*", a1):
						a = z3.Real(f"{a1}")
					else:
						a = float(a1)
					if not re.match(r"\d+\.*\d*", b1):
						b = z3.Real(f"{b1}")
					else:
						b = float(b1)
					x = z3.Real(f"{i}_dx_{len(path)}")
					x_0 = z3.Real(f"{i}_x_{len(path)}")
					t = z3.Real(f"{i}_t_{len(path)+1}")
					S.add(t >= 0, t <= T)
					if a != 0: # Affine ODE
						e = np.exp(1)
						S.add(x == ((a*x_0 + b)*e**(a*t) - b)/a)
					else: # Linear ODE
						S.add(x == x_0 + b*t)
				invariant_1 = automata[n][0][loc][1].split("&")
				invariant = []
				for inv in invariant_1:
					if inv != "true":
						invariant.append(inv)
				x = z3.Real(f"{i}_x_{len(path)}")
				for inv in invariant:
					exec(f"S.add({''.join(inv)})")
				x = z3.Real(f"{i}_dx_{len(path)}")
				for inv in invariant:
					exec(f"S.add({''.join(inv)})")
				break

		''' LOCATION:
		Must satisfy the flow.
		Must satisfy the invariant.
		(Assuming that there is a single variable x.)
		'''
		k = 0
		for j in path:
			for l in G.edges.data():
				if l[2]['transition'] in j:
					loc = l[0]
					break
			flow = automata[n][0][loc][0].split("&")
			for f in flow:
				a1, b1 = extract_flow_coefficients(f)
				if not re.match(r"\d+\.*\d*", a1):
					a = z3.Real(f"{a1}")
				else:
					a = float(a1)
				if not re.match(r"\d+\.*\d*", b1):
					b = z3.Real(f"{b1}")
				else:
					b = float(b1)
				x = z3.Real(f"{i}_dx_{k}")
				x_0 = z3.Real(f"{i}_x_{k}")
				t = z3.Real(f"{i}_t_{k+1}")
				S.add(t >= 0, t <= T)
				if a != 0: # Affine ODE
					e = np.exp(1)
					S.add(x == ((a*x_0 + b)*e**(a*t) - b)/a)
				else: # Linear ODE
					S.add(x == x_0 + b*t)

			invariant_1 = automata[n][0][loc][1].split("&")
			invariant = []
			for inv in invariant_1:
				if inv != "true":
					invariant.append(inv)
			x = z3.Real(f"{i}_x_{k}")
			for inv in invariant:
				exec(f"S.add({''.join(inv)})")
			x = z3.Real(f"{i}_dx_{k}")
			for inv in invariant:
				exec(f"S.add({''.join(inv)})")

			k = k+1

		''' TRANSITION:
		Must satisfy the guard.
		Must satisfy the assignment.
		(Assuming that there is a single variable x.)
		'''
		k = 0
		for j in path:
			guard_1 = automata[n][1][j][0].split("&")
			guard = []
			for g in guard_1:
				if g != "true":
					guard.append(g)
			x = z3.Real(f"{i}_dx_{k}")
			for g in guard:
				exec(f"S.add({''.join(g)})")

			assignments = automata[n][1][j][1].split("&")
			for asgn in assignments:
				if asgn == "true":
					assignment = z3.Real(f"{i}_dx_{k}")
				else:
					assignment = asgn.split("=")[1]
				x = z3.Real(f"{i}_x_{k+1}")
				S.add(x == assignment)

			k = k+1

	''' SYNCHRONIZATION:
		Given depth $j$ of $G_1$ where a transition is shared with components $G_2$ at depth $j'$,
		we have $\sum_{n=0}^{j-1}{t_n^{G_1}} = \sum_{n=0}^{j'-1}{t_n^{G_2}}$
	'''

	if str(S.check()) == "sat":
		print("The path is feasible.")
		#m = S.model()
		#for x in m.decls():
		#	print(f"{x.name()} = {m[x]}")
		return 0
	else:
		print("The path is infeasible.")
	return 1