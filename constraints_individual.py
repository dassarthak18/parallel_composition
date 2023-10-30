import z3
import itertools
import networkx as nx
import matplotlib.pyplot as plt

from constraints import *

if __name__ == "__main__":
	# Reading graphs for individual automata in the hybrid system
	G = read_graph("rod_1.txt")
	H = read_graph("controller.txt")

	# Creating a single solver for the entire system
	S = z3.Solver()

	# Generating the constraints for a run of the SAT solver
	S = generate_constraints(G, S, 3, "rod_1.cfg")
	#print(S)
	#S = generate_constraints(H, S, 3, "controller.cfg")
	#print(S)

	# Getting and printing the model for the run
	while str(S.check()) == "sat":
		m = S.model()
		negation(S,m)