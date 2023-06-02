#!/usr/bin/env python3
import matplotlib as mpl
import numpy as np
import matplotlib.pyplot as plt
from numpy import genfromtxt
from tool import *
import csv
import pandas as pd

# Ethereum confirmation time
conf = 12*64
# We consider 5 different secret committee sizes : 8 16 32 64 128
m = 5

data = read_datafile(".\\data\\F3B_records.csv")
df = pd.DataFrame(data)
dfList = []
# First we separate the rows of the data corresponding to a specific number of nodes
# We have a dataframe for each n
for i in range(m):
    thisDf = df.loc[df[0] == 2**(3+i)]
    thisDf = thisDf.mean(axis=0) / 1000
    dfList.append(thisDf)

# Get average over all the available data
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

# Sometimes the latency of batchsize 1 is more than larger batchsiezes, this is very surprising 
# As a quick hack we get the minimum over batchsize 1,2,4 
receivingSharesTime = np.minimum(rST1 , rST2 , rST4)
decryptionTime = np.minimum(dT1 , dT2, dT4)

# overal latency
latency = receivingSharesTime + decryptionTime
latency = [0 , conf] + latency.values.tolist()

ethLatency = [conf] * (m+2)

ind = np.arange(len(latency))  # the x locations for the groups
width = 0.3      # the width of the bars

fig, ax = plt.subplots()
rects1 = ax.bar(ind + width, ethLatency, width, color=green[1], edgecolor=green[0])
rects2 = ax.bar(ind + width*2, latency, width, color=red[1], edgecolor=red[0])

# add some text for labels, title and axes ticks
ax.set_yscale('log')
ax.set_ylim(0.01,1000)
ax.set_ylabel('Latency(sec)', fontsize=fs_label*1.2)
ax.set_xlabel('Mitigation Method', fontsize=fs_label*1.2)
ax.set_xticks(ind + width)
ax.set_xticklabels(("Baseline   ","Strawman","F3B-8","F3B-16","F3B-32","F3B-64","F3B-128"),fontsize=12)

ax.yaxis.grid(linestyle='--')
ax.yaxis.set_major_formatter(plt.FuncFormatter(format_func))

for label in ( ax.get_yticklabels()):
    label.set_fontsize(fs_axis)

ax.legend((rects1[0], rects2[0]), ('Round 1(Commit)','Round 2(Reveal)'), loc=1,fontsize=1*fs_label)
plt.tight_layout()
destination = "../resources/"
save_pdf("latencyComparisonDela_new.pdf")
