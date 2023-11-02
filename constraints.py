import z3
import itertools
import networkx as nx
import matplotlib.pyplot as plt

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

	#nx.draw(G,pos=nx.spring_layout(G))
	#plt.show()
	return G

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
	#print(init,dest)

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
		#print(exp1)

	''' EXCLUDE Constraints: 
		if one edge is active at a given depth,
		no other edge can be active at that depth
	'''
	
	transitions = set()
	for i in G.edges():
		transitions.add(G[i[0]][i[1]][0]["transition"])
	transitions = list(transitions) # list of all transitions in the graph
	#print(transitions)
	for n in range(k):
		for i in transitions:
			exp2a = z3.Bool("exp2a")
			exp2a = False
			#print()
			#print(i)
			#print()
			for j in transitions:
				if j != i:
					#print(j)
					if exp2a == False:
						exp2a = z3.Bool(f"{j}_{n+1}")
					else:
						exp2a = z3.Or(exp2a,z3.Bool(f"{j}_{n+1}"))
			#print(exp2a)
			S.add(z3.Implies(z3.Bool(f"{i}_{n+1}"),z3.Not(exp2a)))
			#print(z3.Implies(z3.Bool(f"{i}_{n+1}"),z3.Not(exp2a)))
	#print(exp2)

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
		#print(i,in_edges,out_edges)
		prod = list(itertools.product(in_edges,out_edges))
		products.extend(prod)
		#print(prod)
	#for i in products:
	#	print(i)
	adjacency_dict = {} # adjacency list for products array
	for i in products:
		u, v = i
		if u in adjacency_dict:
			adjacency_dict[u].append(v)
		else:
			adjacency_dict[u] = [v]
	#print(adjacency_dict)
	for n in range(k-1):
		for i, j in adjacency_dict.items():
			exp3a = z3.Bool("exp3a")
			exp3a = False
			for x in j:
				if exp3a == False:
					exp3a = z3.Bool(f"{x}_{n+2}")
				else:
					exp3a = z3.Or(exp3a,z3.Bool(f"{x}_{n+2}"))
			#print(f"{i}_{n+1}",exp3a)
			S.add(z3.Implies(z3.Bool(f"{i}_{n+1}"),exp3a))
	#print(exp3)

	''' DEST Constraints: 
		at depth k, the edge must be
		an incoming edge of the location
	'''
	dest_edges = set()
	for n in dest:
		for i in G.in_edges(n):
			dest_edges.add(G[i[0]][i[1]][0]["transition"])
	dest_edges = list(dest_edges) # list of all destination edges
	#print(dest_edges)
	exp4 = z3.Bool("exp4")
	exp4 = False
	for i in dest_edges:
		if exp4 == False:
			exp4 = z3.Bool(f"{i}_{k}")
		else:
			exp4 = z3.Or(exp4,z3.Bool(f"{i}_{k}"))
	S.add(exp4)
	#print(exp4)

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
	#print(stutter, local)

	dic ={}
	for i in local:
		dic[i] = 0
	#print(dic)
	shared = []
	n = len(str(k))
	for i in dic:
		name = i[:-n-1]
		for j in graphs:
			for x in j.edges.data():
				if x[2]['transition'] == name:
					dic[i] = dic[i] + 1
	#print(dic)
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
		#arr.append([])
		for j in stutter:
			if j[len(j)-n:] == str(i+1):
				arr.append(j[:len(j)-n-1])
	#print(arr)

	stutter_dic = {}
	for i in arr:
		n = i.find("stutter")
		#print(j[:n-1])
		if i[:n-1] in stutter_dic:
			if i not in stutter_dic[i[:n-1]]:
				stutter_dic[i[:n-1]].append(i)
		else:
			stutter_dic[i[:n-1]] = []
	#print(stutter_dic)

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
	#print(shared_dic)

	local_dic = {}
	for i in stutter_dic:
		local_dic[i] = set()
	#print(local_dic)

	for i in range(len(graphs)):
		indices = []
		for j, l in enumerate(files[i]):
			if l == "/":
				indices.append(j)
		if len(indices) > 0:
			name = files[i][indices[-1]+1:]
		else:
			name = files[i]
		#print(name)
		for j in local:
			for l in graphs[i].edges.data():
				if l[2]['transition'] in j:
					#print(j)
					local_dic[name].add(l[2]['transition'])
					break
	#print(local_dic)

	''' GLOBAL WAITING
	all member automata are not allowed
	to enable the stutter transition simultaneously
	'''
	glob = list(itertools.product(*stutter_dic.values()))
	#print(all_combinations)
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
			#print(exp1a)

	''' REPEATED WAITING FOR SHARED LABELS
	all member automata with this specific shared label are not allowed
	to enable the stutter transition simultaneously
	'''
	for i in range(2, k):
		for j in shared_dic:
			exp2a = z3.Bool("exp2a")
			exp2a = False
			#print(f"{j}_{i}", end=" => NOT ")
			#print(shared_dic[j])
			for graph in shared_dic[j]:
				#print(graph)
				for x in stutter_dic[graph]:
					#print(f"{x}_{i-1}", end=" & ")
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
			#print(j)
			for n in range(2, k):
				exp3a = z3.Bool("exp3a")
				exp3a = False
				for l in stutter_dic[i]:
					if exp3a == False:
						exp3a = z3.Bool(f"{l}_{n-1}")
					else:
						exp3a = z3.Or(exp3a, z3.Bool(f"{l}_{n-1}"))
				#print(z3.Implies(z3.Bool(f"{j}_{n}"), z3.Not(exp3a)))
				S.add(z3.Implies(z3.Bool(f"{j}_{n}"), z3.Not(exp3a)))

	return S

# Function to negate an already retrieved path
def negation(S, model, paths):
	# Getting the model for this run
	trues = []
	for d in model.decls():
		if model[d] == True:
			#print(d.name())
			trues.append(d.name())
	#print(trues)

	P = {}
	#print(i)
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
	#print(P)
	paths.append(P)

	# Negating the model
	exp = z3.Bool("exp")
	exp = False
	for i in trues:
		#print(type(i))
		if exp == False:
			exp = z3.Bool(i)
		else:
			exp = z3.And(exp,z3.Bool(i))

	S.add(z3.Not(exp))
	return S

# Function to pretty print a retrieved path
def print_path(graphs, files, p, k):
	#print(p)
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
		print(name+": ", end="")
		for i in p:
			for j in p[i]:
				for x in G.edges.data():
					if j == x[2]['transition']:
						if i == k:
							print(j)
						else:
							print(j, end=" -> ")
						break