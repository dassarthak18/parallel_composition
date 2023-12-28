import z3

path = {'tank': ['On'], 'burner': ['TurnOn', 'On'], 'thermometer': ['UP95', 'UP95']}
print(path)

S = z3.Solver()

sync_trans = {}
for i in path:
	for j in path[i]:
		if j not in sync_trans:
			sync_trans[j] = set([i])
		else:
			sync_trans[j].add(i)
sync_trans_filtered = {key: value for key, value in sync_trans.items() if len(value) > 1}
print(sync_trans_filtered)

for i in sync_trans_filtered:
	summ = []
	for j in sync_trans_filtered[i]:
		arr = []
		counter = path[j].index(i)
		for k in range(counter+1):
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
		print(S.assertions()[-1])