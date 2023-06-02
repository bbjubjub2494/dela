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

data = read_datafile(".\\data\\F3B_records_new_thru.csv")
df = pd.DataFrame(data)
# We only need the data for n = 128
df = df.loc[df[0] == 128]

latency = []
throughput = []
for i in range(int(len(df.columns)/2)):
    # Add the receive shares delay to decryption delay and get the mean iver all the data rows
    # In our new definition of latency, we do not consider the time for receiving shares, but a 100ms communication delay
    # that we have gathered for n = 128 
    # t = np.mean(df[1+2*i] + df[2+2*i])/1000
    t = np.mean(100 + df[2+2*i])/1000
    latency.append(t)
    # Batchsize is 2**i. throughput is batchsize/latency
    throughput.append((2**i)/t)

# print the throughput and latency for batchsize 1 and 512 1024
print("Throughput for batchsize 1: ", throughput[0])
print("Latency for batchsize 1: ", latency[0])
print("Throughput for batchsize 512: ", throughput[-3])
print("Latency for batchsize 512: ", latency[-3])
print("Throughput for batchsize 1024: ", throughput[-2])
print("Latency for batchsize 1024: ", latency[-2])
print("Throughput for batchsize 2048: ", throughput[-1])
print("Latency for batchsize 2048: ", latency[-1])
ind = np.arange(len(throughput))  # the x locations for the groups
width = 0.3      # the width of the bars

fig, ax1 = plt.subplots()
ax2 = ax1.twinx()

rects1 = ax1.bar(ind + width, throughput, width, color=green[1], edgecolor=green[0], linestyle="--")
rects2 = ax2.plot(ind + width, latency, color=red[0], marker="x")


# add some text for labels, title and axes ticks
ax2.set_yscale('linear')
ax2.set_ylim(0,10)
ax2.set_ylabel('Latency(sec)', fontsize=fs_label*1.2)

ax1.set_yscale('linear')
ax1.set_ylim(0,210)
ax1.set_ylabel('Throughput(tx/sec)', fontsize=fs_label*1.2)


ax1.set_xlabel('Varying batching size with 128 trustees', fontsize=fs_label*1.0)
ax1.set_xticks(ind + width)
ax1.set_xticklabels(("1","2","4","8","16","32","64","128", "256" , "512" , " 1024", "    2048"),fontsize=0.72*fs_label)
ax1.yaxis.grid(linestyle='--')
ax1.yaxis.set_major_formatter(plt.FuncFormatter(format_func))
ax2.yaxis.set_major_formatter(plt.FuncFormatter(format_func))

for label in (ax1.get_yticklabels()):
    label.set_fontsize(1*fs_axis)
for label in (ax2.get_yticklabels()):
    label.set_fontsize(1*fs_axis)

ax1.legend((rects1[0], rects2[0]), ('Throughput', 'Latency'), loc=2,fontsize=1*fs_label)
plt.tight_layout()
save_pdf("throughput-minogrpc-aft23-0521.pdf")


