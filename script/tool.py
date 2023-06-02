import matplotlib.pyplot as plt
from numpy import genfromtxt
import os
import sys

destination = "../resources/"
show = True

os.environ["LC_ALL"] = "en_US.UTF-8"
os.environ["LANG"] = "en_US.UTF-8"

green = ["#557555", "#C5E1C5", "s", 10]
yellow = ["#8f8a5a", "#fffaca", "v", 11]
red = ["#8f5252", "#ffc2c2", "D", 9]
purple = ["#52528f", "#c2c2ff", "o", 10]

fs_label = 15
fs_axis = 15

ax = plt.subplot()
for label in (ax.get_xticklabels() + ax.get_yticklabels()):
    label.set_fontsize(fs_axis)

def plot(x, y, linestyle, label, color):
    plt.plot(x,y,linestyle,label= label, color=color[0], mfc=color[1],
             marker=color[2], markersize=color[3])

def save(name):
    plt.savefig(destination + name, format='eps', dpi=1000)
    if show:
        plt.show()

def save_pdf(name):
    plt.savefig(destination + name, format='pdf', bbox_inches='tight', dpi=1000)
    if show:
        plt.show()

def read_datafile(file_name):
    data = genfromtxt(file_name, delimiter=',',skip_header=1)
    return data

def format_func(value, tick_number):
    if value < 1:
        return "{0}".format(value)
    else:
        return "%d" % value

if len(sys.argv) > 1 and sys.argv[1] == "noshow":
    show = False
