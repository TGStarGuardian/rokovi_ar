N = [['nx1', 'ny1'], ['nx2', 'ny2'], ['nx3', 'ny3'], ['nx4', 'ny4']]
Q = [['qx1', 'qy1'], ['qx2', 'qy2'], ['qx3', 'qy3'], ['qx4', 'qy4']]

## za svakog konja, proveravamo da li je u dometu drugog konja
for i in range(len(N)):
	for j in range(i + 1, len(N)):
		## proveravamo da li je i u dometu j
		print('(distinct_pairs (+ ' + N[j][0] + ' 1) ' + '(+ ' + N[j][1] + ' 2) ' + N[i][0] + ' ' + N[i][1] + ')')
		print('(distinct_pairs (+ ' + N[j][0] + ' 1) ' + '(- ' + N[j][1] + ' 2) ' + N[i][0] + ' ' + N[i][1] + ')')
		print('(distinct_pairs (- ' + N[j][0] + ' 1) ' + '(+ ' + N[j][1] + ' 2) ' + N[i][0] + ' ' + N[i][1] + ')')
		print('(distinct_pairs (- ' + N[j][0] + ' 1) ' + '(- ' + N[j][1] + ' 2) ' + N[i][0] + ' ' + N[i][1] + ')')
		print('(distinct_pairs (+ ' + N[j][0] + ' 2) ' + '(+ ' + N[j][1] + ' 1) ' + N[i][0] + ' ' + N[i][1] + ')')
		print('(distinct_pairs (+ ' + N[j][0] + ' 2) ' + '(- ' + N[j][1] + ' 1) ' + N[i][0] + ' ' + N[i][1] + ')')
		print('(distinct_pairs (- ' + N[j][0] + ' 2) ' + '(+ ' + N[j][1] + ' 1) ' + N[i][0] + ' ' + N[i][1] + ')')
		print('(distinct_pairs (- ' + N[j][0] + ' 2) ' + '(- ' + N[j][1] + ' 1) ' + N[i][0] + ' ' + N[i][1] + ')')
		print('(distinct_pairs ' + N[j][0] + ' ' + ' ' + N[j][1] + '  ' + N[i][0] + ' ' + N[i][1] + ')')
		
		
		
## za svaku damu, proveravamo da li je u dometu nekog konja

for i in range(len(Q)):
	for j in range(len(N)):
		print('(distinct_pairs (+ ' + N[j][0] + ' 1) ' + '(+ ' + N[j][1] + ' 2) ' + Q[i][0] + ' ' + Q[i][1] + ')')
		print('(distinct_pairs (+ ' + N[j][0] + ' 1) ' + '(- ' + N[j][1] + ' 2) ' + Q[i][0] + ' ' + Q[i][1] + ')')
		print('(distinct_pairs (- ' + N[j][0] + ' 1) ' + '(+ ' + N[j][1] + ' 2) ' + Q[i][0] + ' ' + Q[i][1] + ')')
		print('(distinct_pairs (- ' + N[j][0] + ' 1) ' + '(- ' + N[j][1] + ' 2) ' + Q[i][0] + ' ' + Q[i][1] + ')')
		print('(distinct_pairs (+ ' + N[j][0] + ' 2) ' + '(+ ' + N[j][1] + ' 1) ' + Q[i][0] + ' ' + Q[i][1] + ')')
		print('(distinct_pairs (+ ' + N[j][0] + ' 2) ' + '(- ' + N[j][1] + ' 1) ' + Q[i][0] + ' ' + Q[i][1] + ')')
		print('(distinct_pairs (- ' + N[j][0] + ' 2) ' + '(+ ' + N[j][1] + ' 1) ' + Q[i][0] + ' ' + Q[i][1] + ')')
		print('(distinct_pairs (- ' + N[j][0] + ' 2) ' + '(- ' + N[j][1] + ' 1) ' + Q[i][0] + ' ' + Q[i][1] + ')')
