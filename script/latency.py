#!/usr/bin/env python3
import matplotlib as mpl
import numpy as np
import matplotlib.pyplot as plt
from numpy import genfromtxt
from tool import *
import csv

data = read_datafile('./data/IBE_records.csv')

x= data[:,0]
y1= data[:,1]
y2= data[:,2]
y3= data[:,3]


ind = np.arange(len(x))  # the x locations for the groups
width = 0.3      # the width of the bars

fig, ax = plt.subplots()
rects1 = ax.plot(ind + width, y1, color=red[0], marker=".")
rects2 = ax.bar(ind + width, y2, width, color=purple[1], edgecolor=purple[0])
rects3 = ax.bar(ind + 2*width, y3, width, color=yellow[1], edgecolor=yellow[0])

# add some text for labels, title and axes ticks
ax.set_yscale('log')
ax.set_ylim(0.01,1000)
ax.set_ylabel('Latency(sec)', fontsize=fs_label)
ax.set_xlabel('Size of Secret-management Committee', fontsize=fs_label)
ax.set_xticks(ind + width)
ax.set_xticklabels(("8","16","32","64","128"),fontsize=fs_label)
ax.yaxis.grid(linestyle='--')
ax.yaxis.set_major_formatter(plt.FuncFormatter(format_func))

for label in (ax.get_xticklabels() + ax.get_yticklabels()):
    label.set_fontsize(0.8*fs_axis)

ax.legend((rects1[0], rects2[0],rects3[0]), ('DKG Setup','Write Transaction','Key Reconstruction'), loc=2,fontsize=0.8*fs_label)
plt.tight_layout()
save_pdf("IBE_latency.pdf")
