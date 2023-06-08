#!/usr/bin/env python3
import matplotlib as mpl
import numpy as np
import matplotlib.pyplot as plt
from numpy import genfromtxt
from tool import *
import csv

data1 = read_datafile("data/IBE_records.csv")
data2 = read_datafile("data/latency.csv")

x= data1[:,0]
y1= data1[:,1]
y2= data2[:,1]


ind = np.arange(len(x))  # the x locations for the groups
width = 0.3      # the width of the bars

fig, ax = plt.subplots()
rects1 = ax.plot(ind + width, y1, color=red[0], marker=".")
rects2 = ax.plot(ind + width, y2, color=purple[0], marker=".")

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

ax.legend((rects1[0], rects2[0]), ('IBE','TDH2'), loc=2,fontsize=0.8*fs_label)
plt.tight_layout()
save_pdf("IBE_latency.pdf")
