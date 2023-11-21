import copy
import z3

path = {"rod_1":["add_1","remove_1"], "rod_2":["add_2","remove_2"], "controller":["add_1","remove_1","add_2","remove_2"]}
S = z3.Solver()

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
				arr.append(z3.Real(f"{j}_t_{k+1}"))
			summ.append(arr)
		
		string_summ = []
		for a in range(len(summ)):
			string = ""
			for b in range(len(summ[a])):
				if b == len(summ[a])-1:
					string += f"summ[{a}][{b}]"
				else:
					string += f"summ[{a}][{b}] + "
			string_summ.append(string)
		for a in range(len(string_summ)-1):
			exec(f"S.add({string_summ[a]} == {string_summ[a+1]})")
	for i in sync_trans_filtered:
		for j in sync_trans_filtered[i]:
			counters[j] += 1
	
	temp_counters = copy.deepcopy(counters)
	temp_path = copy.deepcopy(path)
	for i in path:
		if counters[i] == len(path[i]):
			temp_counters.pop(i)
			temp_path.pop(i)
	counters = temp_counters
	path = temp_path

print(S)