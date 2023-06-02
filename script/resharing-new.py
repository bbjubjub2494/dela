#!/usr/bin/env python3
import matplotlib as mpl
import numpy as np
import matplotlib.pyplot as plt
from numpy import genfromtxt
from tool import *
import csv
import pandas as pd
# We consider 5 different secret committee sizes : 8 16 32 64 128
m = 5

data = read_datafile(".\\data\\resharing_records-new.csv")
df = pd.DataFrame(data ,   columns=['nOld','nCommon' , 'nNew' ,
                      'setupTime','resharingTime'])
dfList = []
# First we separate the rows of the data corresponding to a specific number of nodes
# We have a dataframe for each n
for i in range(m):
    dfList.append(df.loc[(df['nOld'] == 2**(3+i))])

setupTimeList = []
noNewReshTime = []
oneNewReshTime = []
oneThirdNewReshTime = []

# Now we separate the columns, we get the minimum over all the possible data
for i in range(m):
    n = 2**(3+i)
    # Get the data frame for each n
    thisDf = dfList[i]
    # Get the mean over all the data available for setup time 
    setupTimeList.append(np.mean(thisDf['setupTime'])/1000) 
    # Get the mean over all the data available for resharing among the same set of nodes
    noNewReshTime.append(np.mean(thisDf.loc[thisDf['nNew'] == 0]['resharingTime'])/1000) 
    # Get the mean over all the data available for resharing with one new node
    oneNewReshTime.append(np.mean(thisDf.loc[thisDf['nCommon'] == n - 1]['resharingTime'])/1000) 
    # Get the mean over all the data available for resharing with n/3 nodes
    oneThirdNewReshTime.append(np.mean(thisDf.loc[(thisDf["nNew"] > 1) & (df["nCommon"] < n), 'resharingTime'])/1000)
   

ind = np.arange(m)  # the x locations for the groups
width = 0.3      # the width of the bars

fig, ax1 = plt.subplots()

rects1 = ax1.plot(ind + width, setupTimeList, color='#B22222', marker=".")
rects2 = ax1.plot(ind + width, noNewReshTime, color='#228B22', marker="o")
rects3 = ax1.plot(ind + width, oneNewReshTime, color='#CDAD00', marker="*")
rects4 = ax1.plot(ind + width, oneThirdNewReshTime, color='#8B3A62', marker="x")


ax1.set_yscale('log')
ax1.set_ylim(0.1,1000)
ax1.set_ylabel('Latency(sec)', fontsize=fs_label*1.2)

ax1.set_xlabel('Size of Secret-management Committee', fontsize=fs_label*1)
ax1.set_xticks(ind + width)
ax1.set_xticklabels(("8","16","32","64","128"),fontsize=1.2*fs_label)
ax1.yaxis.grid(linestyle='--')
ax1.yaxis.set_major_formatter(plt.FuncFormatter(format_func))

for label in ( ax1.get_yticklabels()):
    label.set_fontsize(1*fs_axis)

ax1.legend((rects1[0], rects2[0] , rects3[0] , rects4[0]), ('DKG Setup', 'Resharing, No new trustee' , 
'Resharing, Replacing one trustee', 'Resharing, Replacing one third of the trustees'), loc=2,fontsize=0.9*fs_label)
plt.tight_layout()
#plt.title('Performance for varying batching size with 32 nodes on Simnet',fontsize=0.6*fs_label)
save_pdf("resharing-latency-AFT23.pdf")