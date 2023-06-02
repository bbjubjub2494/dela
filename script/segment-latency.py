#!/usr/bin/env python3
import matplotlib as mpl
import numpy as np
import matplotlib.pyplot as plt
from numpy import genfromtxt
from tool import *
import pandas as pd
# We consider 5 different secret committee sizes : 8 16 32 64 128
m = 5

data = read_datafile(".\\data\\F3B_records_new.csv")
df = pd.DataFrame(data)
dfList = []
# Get the mean over all the available data for each n
for i in range(m):
    thisDf = df.loc[df[0] == 2**(3+i)]
    # convert ms to s
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
eth = [0.001] * m

# Sometimes the latency of batchsize 1 is more than larger batchsiezes, this is very surprising 
# As a quick hack we get the minimum over batchsize 1,2,4 
receivingSharesTime = np.minimum(rST1 , rST2 , rST4)
decryptionTime = np.minimum(dT1 , dT2, dT4)


ind = np.arange(m)  # the x locations for the groups
width = 0.3      # the width of the bars

fig, ax = plt.subplots()


rects1 = ax.bar(ind + 1*width, receivingSharesTime, width, color=red[1], edgecolor=red[0])
rects2 = ax.bar(ind + 2*width, decryptionTime, width, color=green[1], edgecolor=green[0])
rects3 = ax.bar(ind + 3*width, eth, width, color=yellow[1], edgecolor=yellow[0])

# add some text for labels, title and axes ticks
ax.set_yscale('log')
ax.set_ylim(0,1)
ax.set_ylabel('Latency(sec)', fontsize=fs_label*1.2)
ax.set_xlabel('Size of Secret-management Committee', fontsize=fs_label*1.2)
ax.set_xticks(ind + width)
ax.set_xticklabels(("8","16","32","64","128"),fontsize=15)
ax.yaxis.grid(linestyle='--')
ax.yaxis.set_major_formatter(plt.FuncFormatter(format_func))

for label in (ax.get_xticklabels() + ax.get_yticklabels()):
    label.set_fontsize(1.2*fs_axis)

ax.legend((rects1[0], rects2[0] , rects3[0]), ('Shares Preparation and Communication','Key Reconstruction' , "Decryption and Execution"), loc=1,fontsize=0.9*fs_label)
plt.tight_layout()
destination = "../resources/"
save_pdf("segment-latency-new-mid.pdf")
