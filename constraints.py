import z3
import re
import itertools
import networkx as nx
import numpy as np
import matplotlib.pyplot as plt
import sys
from copy import deepcopy

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
				#print(exp2a)
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
			#print(exp3a)
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
		#print(exp4)
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

# Function to return all transition names from a list irrespective of depth
def return_depth_free(trans, k):
	arr = []
	for i in range(k):
		n = len(str(i+1))
		for j in trans:
			if j[len(j)-n:] == str(i+1):
				arr.append(j[:len(j)-n-1])
	transitions = list(set(arr))
	return transitions

# Function to generate constraints for path-pruning based optimization
def pruning_constraints(graphs, files, S, stutter, shared, local, k):

	arr = return_depth_free(stutter, k)
	
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

# Function to get stutter-free path
def stutter_free(aut_path):
	stutter_free_path = {}
	for i in aut_path:
		path = []
		for j in aut_path[i]:
			if "stutter" not in j:
				path.append(j)
		stutter_free_path[i] = path
	return stutter_free_path

# Function to check infeasibility of a retrieved path
def check_feasibility(aut_path, graphs, automata, files, config, T, shared, var_names, depth):
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
		if not any(var in i for var in var_names):
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

	stutter_free_path = stutter_free(aut_path)

	for i in stutter_free_path:
		path = stutter_free_path[i]
		n = list(stutter_free_path).index(i)
		G = graphs[n]
		for j in init:
			matching_element = [var for var in var_names if var in j]
			x = z3.Real(f'{i}_{matching_element[0]}_0')
			j = j.replace(matching_element[0], "x")
			exec(f"S.add({''.join(j)})")
		for j in forbidden:
			if j!="true":
				matching_element = [var for var in var_names if var in j]
				x = z3.Real(f'{i}_d{matching_element[0]}_{len(path)}')
				j = j.replace(matching_element[0], "x")
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
					matching_element = [var for var in var_names if var in f]
					x = z3.Real(f"{i}_d{matching_element[0]}_{len(path)}")
					x_0 = z3.Real(f"{i}_{matching_element[0]}_{len(path)}")
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
				for inv in invariant:
					matching_element = [var for var in var_names if var in inv]
					x = z3.Real(f"{i}_{matching_element[0]}_{len(path)}")
					inv = inv.replace(matching_element[0], "x")
					exec(f"S.add({''.join(inv)})")
				for inv in invariant:
					matching_element = [var for var in var_names if var in inv]
					x = z3.Real(f"{i}_d{matching_element[0]}_{len(path)}")
					inv = inv.replace(matching_element[0], "x")
					exec(f"S.add({''.join(inv)})")
				break

		''' LOCATION:
		Must satisfy the flow.
		Must satisfy the invariant.
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
				matching_element = [var for var in var_names if var in f]
				x = z3.Real(f"{i}_d{matching_element[0]}_{k}")
				x_0 = z3.Real(f"{i}_{matching_element[0]}_{k}")
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
			for inv in invariant:
				matching_element = [var for var in var_names if var in inv]
				x = z3.Real(f"{i}_{matching_element[0]}_{k}")
				inv = inv.replace(matching_element[0], "x")
				exec(f"S.add({''.join(inv)})")
			for inv in invariant:
				matching_element = [var for var in var_names if var in inv]
				x = z3.Real(f"{i}_d{matching_element[0]}_{k}")
				inv = inv.replace(matching_element[0], "x")
				exec(f"S.add({''.join(inv)})")

			k = k+1

		''' TRANSITION:
		Must satisfy the guard.
		Must satisfy the assignment.
		'''
		k = 0
		for j in path:
			guard_1 = automata[n][1][j][0].split("&")
			guard = []
			for g in guard_1:
				if g != "true":
					guard.append(g)
			for g in guard:
				matching_element = [var for var in var_names if var in g]
				x = z3.Real(f"{i}_d{matching_element[0]}_{k}")
				g = g.replace(matching_element[0], "x")
				exec(f"S.add({''.join(g)})")

			assignments = automata[n][1][j][1].split("&")
			marked = []
			for asgn in assignments:
				if asgn == "true":
					for v in var_names:
						assignment = z3.Real(f"{i}_d{v}_{k}")
						x = z3.Real(f"{i}_{v}_{k+1}")
						S.add(x == assignment)
						marked.append(v)
				else:
					arr = asgn.split("=")
					assignment = arr[1]
					x = z3.Real(f"{i}_{arr[0]}_{k+1}")
					S.add(x == assignment)
					marked.append(arr[0])
			if len(marked) < len(var_names):
				for a in var_names:
					if not a in marked:
						assignment = z3.Real(f"{i}_d{a}_{k}")
						x = z3.Real(f"{i}_{a}_{k+1}")
						S.add(x == assignment)
			k = k+1

		''' SYNCHRONIZATION:
		Given depth $j$ of $G_1$ where a transition is shared with components $G_2$ at depth $j'$,
		we have $\sum_{n=0}^{j-1}{t_n^{G_1}} = \sum_{n=0}^{j'-1}{t_n^{G_2}}$
		'''
		path = deepcopy(stutter_free_path)
		counters = {}
		for i in path:
			counters[i] = 0

		while len(path) > 0:
			trans = {}
			for i in path:
				trans[i] = path[i][counters[i]]
			
			sync_trans = {}
			for key, value in trans.items():
				if value in sync_trans:
					sync_trans[value].append(key)
				else:
					sync_trans[value] = [key]
			sync_trans_filtered = {key: value for key, value in sync_trans.items() if len(value) > 1}
			
			for i in sync_trans_filtered:
				summ = []
				for j in sync_trans_filtered[i]:
					arr = []
					for k in range(counters[j]+1):
						t_var = z3.Real(f"{j}_t_{k+1}")
						arr.append(t_var)
					summ.append(arr)

				string_summ = []
				for a1 in range(len(summ)):
					string = ""
					for b1 in range(len(summ[a1])):
						if b1 == len(summ[a1])-1:
							string += f"summ[{a1}][{b1}]"
						else:
							string += f"summ[{a1}][{b1}]+"
					string_summ.append(string)
				for a1 in range(len(string_summ)-1):
					exec(f"S.add({string_summ[a1]}=={string_summ[a1+1]})")
			for i in sync_trans_filtered:
				for j in sync_trans_filtered[i]:
					counters[j] += 1
			
			temp_counters = deepcopy(counters)
			temp_path = deepcopy(path)
			for i in path:
				if counters[i] == len(path[i]):
					temp_counters.pop(i)
					temp_path.pop(i)
			counters = temp_counters
			path = temp_path

	if str(S.check()) == "sat":
		print("Unsafe. Found a counterexample.")
		return S.model()
	return []

def compute_flow(flow, x_0, t):
	a1, b1 = extract_flow_coefficients(flow)
	a = float(a1)
	b = float(b1)
	if a != 0: # Affine ODE
		e = np.exp(1)
		val = ((a*x_0 + b)*e**(a*t) - b)/a
	else: # Linear ODE
		val = x_0 + b*t
	return val

def plot_CE(graphs, automata, m, x, config, stutter_free_path):
	# Setting the parameters
	arr = x.split('_')
	var = arr[len(arr)-1]
	arr.remove(var)
	name = '_'.join(arr)

	k = len(stutter_free_path[name])
	var_name = f"{name}_{var}"
	dvar_name = f"{name}_d{var}"
	tvar_name = f"{name}_t"

	# Retrieving the CE
	x_arr = []
	dx_arr = []
	t_arr = [0]
	for i in range(k):
		xx = var_name + "_" + str(i)
		dx = dvar_name + "_" + str(i)
		t = tvar_name + "_" + str(i+1)
		x_arr.append(float(m[z3.Real(xx)].as_decimal(sys.maxsize)))
		dx_arr.append(float(m[z3.Real(dx)].as_decimal(sys.maxsize)))
		t_val = float(m[z3.Real(t)].as_decimal(sys.maxsize))
		t_arr.append(float(t_arr[len(t_arr)-1]+t_val))
	xx = var_name + "_" + str(k)
	x_arr.append(float(m[z3.Real(xx)].as_decimal(sys.maxsize)))

	# Getting the flow for precise plotting
	path = stutter_free_path[name]
	n = list(stutter_free_path).index(name)
	G = graphs[n]
	flows = []
	for j in path:
		for l in G.edges.data():
			if l[2]['transition'] in j:
				loc = l[0]
				break
		flow_arr = automata[n][0][loc][0].split("&")
		for i in flow_arr:
			if f"{var}'" in i:
				flow = i
				break
		c = "na"
		if 'c' in flow: # Assuming naming convention c for x'=ax+c such that c is a range
			c = float(m[z3.Real("c")].as_decimal(sys.maxsize))
		flows.append(flow.replace("c", str(c)))
	j = path[len(path)-1]
	for l in G.edges.data():
		if l[2]['transition'] in j:
			forbidden = l[1]
			break
	flow_arr = automata[n][0][forbidden][0].split("&")
	for i in flow_arr:
		if f"{var}'" in i:
			flow = i
			break
	c = "na"
	if 'c' in flow:
		c = float(m[z3.Real("c")].as_decimal(sys.maxsize))
	flows.append(flow.replace("c", str(c)))

	# Generate flow points
	for i in range(len(t_arr)-1):
		X_arr = [x_arr[i]]
		T_arr = [t_arr[i]]
		dx = x_arr[i]
		dt = t_arr[i]
		del_t = float((t_arr[i+1] - t_arr[i])/100)

		for _ in range(100):
			dt = dt + del_t
			dx = compute_flow(flows[i], x_arr[i], dt - t_arr[i])
			X_arr.append(dx)
			T_arr.append(dt)

		X_arr.append(dx_arr[i])
		T_arr.append(t_arr[i+1])
		plt.plot(T_arr, X_arr, color='blue', linestyle='-')
		plt.plot(T_arr[0], X_arr[0], color='blue', marker='.')
		plt.plot(T_arr[len(T_arr)-1], X_arr[len(T_arr)-1], color='blue', marker='.')
		plt.plot([t_arr[i+1],t_arr[i+1]], [dx_arr[i], x_arr[i+1]], color='blue', linestyle='--')

	# Mark the forbidden location with red colour
	config_file = open(config, 'r')
	count = 0
	for line in config_file.readlines():
		if count == 0:
			init = line.strip().split('&')
		else:
			forbidden = line.strip().split('&')
		count = count+1
	if forbidden == ["true"]:
		plt.plot([t_arr[len(t_arr)-1]], [x_arr[len(x_arr)-1]], 'ro')
	# TODO: Else mark the forbidden region with red colour

	# Plotting the CE outline
	plt.show()
	# TODO: Mark the forbidden region with a box (if applicable) else mark the forbidden location with red colour

	# Plotting the CE outline
	plt.show()
