import os
os.system('mkdir -p LOG')
n = [16, 32, 64, 128, 256]
n = [128]
for xn in n:
	# os.system('./main_zk mat_' + str(xn) + '_circuit.txt' + ' mat_' + str(xn) + '_meta.txt LOG/mat_' + str(xn) + '.txt')
	os.system('./main mat_' + str(xn) + '_circuit.txt' + ' mat_' + str(xn) + '_meta.txt LOG/mat_' + str(xn) + '.txt')
