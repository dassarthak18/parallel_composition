import numpy as np
import z3

t = float(input("Enter the time horizon : "))
e = np.exp(1) # Euler number
#time_step = input("Enter the time step size : ")
#no_of_steps = int(t/time_step)

# Consider an affine DE of the form x' = ax + b
a = float(input("Enter the value of a : "))
b = float(input("Enter the value of b : "))
print(f"The differential equation is x' = {a}x + {b}.")

x_0 = float(input("Enter the initial value of x : "))

# Solution: x_t = ((a*x_0 + b)*e^(a*t) - b)/a
x_t = ((a*x_0 + b)*np.exp(a*t) - b)/a
print(f"Definite Integral: x_{t} = {x_t}")

# SAT Solving
S = z3.Solver()
S.add(z3.Real(f"x_{t}") == ((a*x_0 + b)*e**(a*t) - b)/a)

if S.check() == z3.sat:
	model = S.model()
	for d in model.decls():
		if d.name() == f"x_{t}":
			expr = str(model[d])
			break

x_sat = eval(expr)
print(f"SAT Solving: x_{t} = {x_sat}")
