#!/usr/bin/env python3
import matplotlib as mpl
import numpy as np
import matplotlib.pyplot as plt
from numpy import genfromtxt
from tool import *
import pandas as pd
# We consider 5 different secret committee sizes : 8 16 32 64 128
m = 5

data = read_datafile(".\\data\\PVSS_records.csv")
df = pd.DataFrame(data)
dfList = []
# Get the mean over all the available data for each n
for i in range(m):
    thisDf = df.loc[df[0] == 2**(3+i)]
    # convert ms to s
    thisDf = thisDf.mean(axis=0) / 1000
    dfList.append(thisDf)

meanDf = pd.DataFrame(dfList)

# encrypting shares time 
eST = meanDf[1]
# Recieving shares time 
rST = meanDf[2]
# Decryption time 
dT = meanDf[3]
eth = [0.001] * m

encryptSharesTime = eST
receivingSharesTime = rST
decryptionTime = dT


ind = np.arange(m)  # the x locations for the groups
width = 0.2      # the width of the bars

fig, ax = plt.subplots()

rects0 = ax.bar(ind + 1*width, encryptSharesTime, width, color=purple[1], edgecolor=purple[0])
rects1 = ax.bar(ind + 2*width, receivingSharesTime, width, color=red[1], edgecolor=red[0])
rects2 = ax.bar(ind + 3*width, decryptionTime, width, color=green[1], edgecolor=green[0])
rects3 = ax.bar(ind + 4*width, eth, width, color=yellow[1], edgecolor=yellow[0])

# add some text for labels, title and axes ticks
ax.set_yscale('log')
ax.set_ylim(0,10)
ax.set_ylabel('Latency(sec)', fontsize=fs_label*1.2)
ax.set_xlabel('Size of Secret-management Committee', fontsize=fs_label*1.2)
ax.set_xticks(ind + width)
ax.set_xticklabels(("8","16","32","64","128"),fontsize=15)
ax.yaxis.grid(linestyle='--')
ax.yaxis.set_major_formatter(plt.FuncFormatter(format_func))

for label in (ax.get_xticklabels() + ax.get_yticklabels()):
    label.set_fontsize(1.2*fs_axis)

ax.legend((rects0[0], rects1[0], rects2[0] , rects3[0]), ('Shares Generation','Shares Decryption and Communication','Key Reconstruction' , "Decryption and Execution"), loc=1,fontsize=0.9*fs_label)
plt.tight_layout()
destination = "../resources/"
save_pdf("pvss-latency-mid.pdf")
