from colored import fg,bg,attr

# function to add ansi colour sequence to 'text'
recs=[]
# n is an integer in the following list:
# 0 - normal colour
recs.append([]) # it'll just get returned as is
# 1 - header/summary/important
recs.append([27,0,0]) # dodger_blue2
# 2 - good performance
recs.append([46,0,0]) # green_1
# 3 - average performance
recs.append([4,0,0]) # blue
# 4 - poor performance
recs.append([9,0,0]) # light_red
# 5 - highlight colour a
recs.append([163,233,0]) # some colour
# 6 - highlight colour b
recs.append([243,0,0]) # some other colour
# 7 - highlight colour c
recs.append([27,0,0])
# 8 - highlight d?
recs.append([9,0,0])
# todays date
recs.append([47,0,0])
# appointment date
recs.append([196,0,0])
# blank days
recs.append([255,0,0])
# first d/o/m
recs.append([226,0,0])
# grey for separators
recs.append([252,0,0])

# generate table with:
# output = tabulate(testtab,headers="firstrow",tablefmt="pretty"))
# provided the headers are the first row, of course

# using colored - https://pypi.org/project/colored/

def header(text):
    global recs
    return fg(recs[1][0])+str(text)+attr(recs[1][2])
def good(text):
    global recs
    return fg(recs[2][0])+str(text)+attr(recs[2][2])
def avg(text):
    global recs
    return fg(recs[3][0])+str(text)+attr(recs[3][2])
def poor(text):
    global recs
    return fg(recs[4][0])+str(text)+attr(recs[4][2])
def hl1(text):
    global recs
    return fg(recs[5][0])+str(text)+attr(recs[5][2])
def hl2(text):
    global recs
    return fg(recs[6][0])+str(text)+attr(recs[6][2])
def hl3(text):
    global recs
    return fg(recs[7][0])+str(text)+attr(recs[7][2])
def hl4(text):
    global recs
    return fg(recs[8][0])+str(text)+attr(recs[8][2])
def tday(text):
    global recs
    return fg(recs[9][0])+str(text)+attr(recs[9][2])
def appt(text):
    global recs
    return fg(recs[10][0])+str(text)+attr(recs[10][2])
def blnk(text):
    global recs
    return fg(recs[11][0])+str(text)+attr(recs[11][2])
def dfom(text):
    global recs
    return fg(recs[12][0])+str(text)+attr(recs[12][2])
def grey(text):
    global recs
    return fg(recs[13][0])+str(text)+attr(recs[13][2])
    
