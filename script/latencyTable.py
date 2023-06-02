#!/usr/bin/env python3
from tool import *
import sys
import numpy as np
import pandas as pd

# We consider 5 different secret committee sizes : 8 16 32 64 128
m = 5

data = read_datafile("./data/F3B_records_new.csv")
df = pd.DataFrame(data)
dfList = []

# First we separate the rows of the data corresponding to a specific number of nodes
# We have a dataframe for each n
for i in range(m):
    thisDf = df.loc[df[0] == 2**(3+i)]
	# Get average over all the data, ms to s
    thisDf = thisDf.mean(axis=0) / 1000
    dfList.append(thisDf)

meanDf = pd.DataFrame(dfList)


# Recieving shares time for batchsize 1
rST1 = meanDf[1]
# Decryption time for batchsize 1
dT1 = meanDf[2]
# Recieving shares time for batchsize 2
rST2 = meanDf[3]
# Decryption time for batchsize 2
dT2  = meanDf[4]
# Recieving shares time for batchsize 4
rST4 = meanDf[5]
# Decryption time for batchsize 4
dT4  = meanDf[6]
# Latency of writing a new transaction to etherume


receivingSharesTime = np.minimum(rST1 , rST2 , rST4)
decryptionTime = np.minimum(dT1 , dT2, dT4)

# overal latency
latency = receivingSharesTime + decryptionTime

confirmations = [64]
sizes = [8, 16, 32, 64, 128]
destination = "../resources/"
sys.stdout = open(destination + 'latencyTableDela_new.tex','wt')

print("\\begin{table}[t]")
print("\\centering ")
print("\\caption{Latency Overhead for Ethereum Blockchain}")
print("\\label{tab:latency} ")
print("\\begin{tabular}{cccccc}")
print("\\toprule")
print("& \\multicolumn{5}{c}{Latency Overhead for different size of SMC} \\\\ \\cmidrule{2-6}")
print("Confirmations & "+str(sizes[0])+" & "+str(sizes[1])+" & "+str(sizes[2])+" & "+str(sizes[3])+" & "+str(sizes[4])+"  \\\\ ")
print("                   \\midrule")
for confirmation in confirmations:
	time = confirmation * 12
	for i in range(len(sizes)):
		overhead = (latency[i]) / time
		print('{:.2f}'.format(overhead*100) + "\\%  ",end='')
		if i != len(sizes)-1:
			print("& ",end='')
	print("\\\\ ")
print("\\bottomrule")
print("\\end{tabular} ")
print("\\end{table}")
