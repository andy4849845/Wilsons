#!/usr/bin/env python3

# note - to keep notes...

import sys
import os.path
import shutil
from os import path
from datetime import date
from datetime import datetime
from datetime import timedelta
import textwrap
import getpass

# Locations
username=getpass.getuser()
root='/home/'+username+"/"
notefile=root+"Work/andys.notes"

possible=['-h', '-t', '-f', '-or']

options=[]
infile=''
try:
    for i in range(len(sys.argv)-1):
        if '-f' == sys.argv[i+1]:
            try:
                infile=sys.argv[i+2]
            except:
                pass
        options.append(sys.argv[i+1].lower())
except:
    pass

argies=[]
for op in options:
    if op not in possible:
        # if it's not a documented option, then just treat it as a search term
        argies.append(op)
        
if '-or' in options:
    sor=True
else:
    sor=False
    
if len(options) == 0:
    # call with no arguments to be asked for a new note to add
    test=open(notefile,"a")
    stamp = datetime.now().strftime("%d%m%y %H%M%S")
    fl=input("Type note: ")
    test.write(stamp+" | "+fl.strip()+"\n")
    # written in format '251221 121532 | Note text', for 25th dec 2021 @12:15:32pm
    test.close()
    quit()
elif '-h' in options:
    # help option
    print("Call with no argument to add a new note\n")
    print("Call with search terms to filter:")
    print(" - text (in '' quotes if needed, e.g. if searching for hashtags)")
    print(" - date[-date] - format ddmm or ddmmyy")
    print(" - +n{dw} - n is number of days/weeks to look back")
    print("            e.g. +1d will show all matching notes added today & yesterday")
    print("Shows all notes matching the given dates")
    print("-or - if multiple search terms, match any of them.  Matching all is the default")
    print("-h  - print this help text")
    print("-t  - print all hashtags")
    print("-f 'file' - imports notes from text file, line by line")
    quit()
elif '-f' in options and len(infile)>0:
    news=open(infile,"r")
    test=open(notefile,"a")
    stamp = datetime.now().strftime("%d%m%y %H%M%S")
    for line in news:
        if len(line)>1:
            test.write(stamp+" | "+line.strip()+"\n")
    # written in format '251221 121532 | Note text', for 25th dec 2021 @12:15:32pm
    test.close()
    news.close()
    quit()

def colors(text,color_):
    # converts text to different colour, color_ is number from 0 to 255
    num1 = str(color_)
    return(f"\033[38;5;{num1}m{text}\033[0;0m")

def dates(dt):
    text=dt.strftime("%d %b %y")
    #return text
    return colors(text,10)
def times(tm):
    text=tm.strftime(" %H:%M")
    #return text
    return colors(text,8)
def searches(text):
    return colors(text,26)
def htags(text):
    return colors(text,196)

def dark(text):
    return colors(text,17)

def printout(results,wrapresults,lens,width,desc):
    # takes search results, list of hashtags and search terms, and prints script output
    # colour date, time, hashtags, search terms, numbers(?), email addresses, links
    dt=''
    #print(desc)
    for i in range(len(results)):
        line=results[i]
        empty=" "*9
        wraplines=wrapresults[i]
        if line[1] == dt:
            datie=empty
        else:
            print("-"*(notewidth+20))
            dt=line[1]
            datie=line[1]
        
        ln=(width-lens[i][0])*" "
        print(datie+line[2]+" | "+wrapresults[i][0]+ln+" |")
        
        if len(wraplines)>1:
            for j in range(len(wrapresults[i])-1):
                ln=(width-lens[i][j+1])*" "
                print(empty+"      "+" | "+wrapresults[i][j+1]+ln+" |")

# if we've got to here then we need to open and read in the existing file
nf=open(notefile,"r")
lines=nf.readlines()
nf.close()

size=os.get_terminal_size()
height=size[1]
width=int(size[0]*0.8)
    
notewidth=min(max(width-21,30),width)

splits=[]
wraps=[]
lns=[]
for entry in lines:
    # just ignores any line in the wrong format
    # convert date/time to coloured here?
    if entry[0:6].isnumeric() and entry[7:13].isnumeric():
        dtt=datetime.strptime(entry[0:13],'%d%m%y %H%M%S')
        dt=datetime.strptime(entry[0:6],'%d%m%y').date()
        splits.append([dt,dates(dtt),times(dtt),entry[16:len(entry)-1]+" "])
        wraps.append(textwrap.wrap(splits[-1][3],width=notewidth, initial_indent='', subsequent_indent='', expand_tabs=True, replace_whitespace=True, fix_sentence_endings=False, break_long_words=True, drop_whitespace=True, break_on_hyphens=True, tabsize=8, max_lines=None))
        lns.append([])
        for i in range(len(wraps[-1])):
            lns[-1].append(len(wraps[-1][i]))

tags=[]
# search for and populate the list of hashtags
for stuff in splits:
    hashes=stuff[3].split('#')
    if len(hashes)>1:
        # if there are some hashes in there, ignore the first bit, since it won't have a hash before it
        for i in range(len(hashes)-1):
            j=hashes[i+1].find(' ')
            tag="#"+hashes[i+1][0:j]
            if tag not in tags:
                tags.append(tag)

tags.sort()

if '-t' in options:
    # if '-t' option is passed
    for t in tags:
        print(t)
    quit()

# so if we've got this far, then searching is on
if len(argies) == 0:
    quit() # can't search without search terms, knobend.
else:
    dates=[] # list of dates to look for
    texts=[] # list of texts to search for, including hashtags (with #)
    descdates=[]
    for a in argies:
        a+="   "
        textinstead=0
        if a[0:1] == "+":
            # start date arguments with '+'
            if a[1:5].isnumeric():
                if a[1:7].isnumeric() == False:
                    d1=datetime.strptime(a[1:5]+date.today().strftime("%y"),"%d%m%y")
                    j=6
                else:
                    d1=datetime.strptime(a[1:7],"%d%m%y")
                    j=8
                d2=d1
                if a[j-1:j] == '-' and a[j:j+4].isnumeric() == True:
                    # we have a second date
                    if a[j:j+6].isnumeric() == False:
                        d2=datetime.strptime(a[j:j+4]+date.today().strftime("%y"),"%d%m%y")
                    else:
                        d2=datetime.strptime(a[j:j+6],"%d%m%y")
                elif a[j-1] != ' ':
                    # if not space after the date, then treat it as a text search term instead
                    # do something here
                    textinstead=1
                    texts.append(a.strip())
            elif a[-4].lower() in ['d', 'w'] and a[1:len(a)-4].isnumeric():
                if a[-4].lower() == 'w':
                    recent=7*int(a[1:len(a)-4])
                else:
                    recent=int(a[1:len(a)-4])
                d2=date.today()
                d1=d2-recent*timedelta(days=1)
            else:
                textinstead=1
                texts.append(a.strip())
            if textinstead ==0:
                delta=timedelta(days=1)
                d=d1
                while d<=d2:
                    if d not in dates:
                        dates.append(d)
                        descdates.append(d.strftime('%d-%b, '))
                    d+=delta
        else:
            texts.append(a.strip().lower())

# dates[] and texts[] are now populated with the required search terms.

outlines=[]
outwraps=[]
#firstlines=[]
lls=[]

for i in range(len(splits)):
    line=splits[i]
    wrapline=wraps[i]
    # store original first lines separately, since textwrap gets confused with the
    # ansi colour coding
    firstline=wraps[i][0]
    fd=0
    # search for dates
    if line[0] in dates or len(dates)==0:
        fd=1
        # now search for search terms, and colour them
        each=[0]*len(texts)
        yes=0
        if fd == 1 and len(texts)>0:
            for v in range(len(texts)):
                t=texts[v]
                for n in range(len(wraps[i])):
                    segment=wraps[i][n]
                    j=0
                    k=0
                    out=""
                    while k>-1:
                        k=segment[j:len(segment)].lower().find(t)
                        if k>-1:
                            out+=segment[j:j+k]+searches(segment[j+k:j+k+len(t)])
                            j+=k+len(t)
                            each[v]=1
                            yes=1
                        else:
                            out+=segment[j:len(segment)]            
                    wraps[i][n]=out
        if (sor == False and sum(each) == len(texts)) or (sor == True and yes==1) or (len(texts) == 0 and fd == 1):
            # if date matches and search term(s) found
            # or if date matches and no search terms
            outlines.append(line)
            outwraps.append(wraps[i])
            lls.append(lns[i])
            #firstlines.append(firstline)
        
for i in range(len(outlines)):
    line=outlines[i]
    #wrapline=outwraps[i]
    # then search through for hashtags, but only colour those which aren't a search term
    try:
        for t in tags:
            if t not in texts and t[1:len(t)] not in texts:
                for n in range(len(outwraps[i])):
                    segment=outwraps[i][n]
                    j=0
                    k=0
                    out=""
                    while k>-1:
                        k=segment[j:len(segment)].lower().find(t)
                        if k>-1:
                            out+=segment[j:j+k]+htags(segment[j+k:j+k+len(t)])
                            j+=k+len(t)
                        else:
                            out+=segment[j:len(segment)]                        
                    outwraps[i][n]=out
    except:
        pass

if len(descdates)==0:
    description="Searching all dates, for: "
else:
    description="Searching dates "
    for ds in descdates:
        description+=ds
    description+="for: "
for ds in texts:
    description+=ds+", "

printout(outlines,outwraps,lls,notewidth,description)
