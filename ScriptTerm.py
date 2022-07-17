#!/usr/bin/env python3

import re
import sys
import csv
import subprocess
import os.path
import shutil
from os import path
from subprocess import run
import datetime
from datetime import date
from datetime import datetime
from datetime import timedelta
import smtplib
from email.message import EmailMessage
from email.utils import formataddr
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.mime.application import MIMEApplication
import textwrap
import getpass
from progress.bar import Bar
from tabulate import tabulate
from colored import fg,bg,attr
import cl # my color module
from colorama import init
init()
import markdown
import calendar
from dateutil.relativedelta import *

#######################################################################
# line 682 - where row[9] is used to extract postcode from appts csv file
# change appts report to included 'parts needed' from eworks
# then change datachew function so postcode is extracted from row[8] of products report instead
########################################################################


###########################################################
# Todo:
#
#   Keep tweaking/improving the turntablehtml() report so that it's as
#   helpful as possible, and minimises corrections needed
#
#   Tagging suggestions - scans job description and picks out key
#   words, comparing against job tags, and suggests accordingly?
#   Could look for Sika, scaffold, tower, ooh, etc.
###########################################################

####################################################################
# Locations
####################################################################
username=getpass.getuser()
root='/home/'+username+"/"
dataroot='DataCentre/'
jobsfolder=dataroot+'Jobs/'
reportsfolder=dataroot+'Eworks/'
photosfolder='Photos/'
emailfiles='ReceivedFiles/'
####################################################################

if os.path.ismount(root+dataroot) == False:
    print("DataCentre drive not accessible - can't do anything")
    quit()

photosdo=0
foldersdo=0
reports=0

recenthistory=42 # default age of quotes to look back at

###########################################################################################
# various statuses / names to use from eworks
###########################################################################################
# job completion statuses
jcs = ['Authorised', 'Invoiced']
# job abandoned statuses
jas = ['Abandoned', 'Cancelled', 'On Hold']
# engineer names to indicate subcontracted appts
subs  = ['Subcontractor']
# engineer names to signify use of picker
#truck = ['37m EN68 OPS']
truck=['test']
# additional statuses to check for for job reports
jcs2= ['Completed', 'Abandoned', 'Cancelled'] 
# jas - jobs active status
jact = ['Appointed', 'Unassigned', 'In Progress', 'Action Required', 'Completed']
# acs - appointment completion statuses
acs = ['Completed', 'On Site', 'On Route', 'Not Dispatched', 'Awaiting', 'Accepted']
# aws - appointment warning status
aws = ['Cancelled','Abandoned','Declined']
# qsc - quotes status list
qsc = ['Processed','Rejected','Converted To Job', 'Accepted']
# jcs3 - statuses to check for completion & generation of sign off report
jcs3 =['Completed']
# jtypes, for signoff reporting
jtypes = ['Contract Works', 'Reactive Callout']
# nominal amount recorded against truck usage, per appointment
truckcharge=650
# job type(s) classed as contract, from point of view of recent function
# any other job, with a value, is classed as callout
jcon = ['Contract Works']
jtru = ['Truck']
joth = ['Recall FOC','Survey FOC','Reactive Callout']
jabbrev = ['R','S','C']
# tags used to indicate time needed for jobs
timetags=[['1day','2day','multiday','halfday'],[1,2,0,1]]
# aos - appointment ongoing status
aos = ['Appointed','Not Dispatched','Awaiting','Accepted']
############################################################################################
# various function definitions - try to make as much of this as possible
# and at some point, these blocks of functions will need ordering & commenting themselves
############################################################################################

#def (text):
#    output=emailsubsection(text)
#    return output

#def (text):
#    global logtime
#    return "--> "+str(int((datetime.now()-logtime).total_seconds()))+"s "+text+"\n"

#def (text):
#    global logtime
#    return "!!! "+str(int((datetime.now()-logtime).total_seconds()))+"s "+text+" !!!\n"

def ongoing(n,incall,textwidth):
    global tjobs
    global jact
    global jcs3
    global jcon
    global jtru
    global joth
    global jabbrev
    global timetags

    # - Move the tag detection information from the tagsuggest
    # - function to a separate file, easier to edit

    # tags that are looked for and listed next to job, on the detail lines
    tagslook=[['Sika','Sika',0],['Truck','37m',1],['Subd',"Sub?",4],
              ['Scaffold','Scaf',1],['OOH','OH',3],['1day','1d',2],['2day','2d',2],
              ['multiday','mday',2], ['halfday','hdalfd',2],['Tower','Tow',1]]
    # there are 5 types of tag - access, sika, time, ooh, subd
    # the numbers indicate column number for that tag

    # n is number of weeks to look ahead
    # tags is list of tags to filter by, if wanted
    # tagsexc is list of tags to exclude (trumped by main tags list)
    # incall is 1 or 0, whether to include all jobs, regardless of age or labour
    
    [nothing,tagrep,tagissues]=tagsuggest()
    # list of form [ref, custsite, suggestions, existing tags, whys]
    # where the last 3 are just strings
    ti=[]
    # generate list of just the job refs with tag issues
    for issue in tagissues:
        ti.append(issue[0])

    # planner section width is 2+n*2
    # tickbox bits add 6 to end of line
    # tags section needs 30, plus couple for gap
    # mwref takes up 10
    # so textwidth-48-2n needs to be big enough the the customer/site stuff
    # min 21, for 8 customer and 12 site

    tagwidth=2
    maxtags=5
    tagtext=maxtags*(tagwidth+1)+1

    reftext=11 # (t mw00000: )

    plantext=n+2 # ' =-==--- '
    ticktext=4 # ( [ ])
    tick=cl.grey("[ ]")
    
    if textwidth-tagtext-reftext-plantext-ticktext<21:
        return
    else:
        custsitew=textwidth-tagtext-reftext-plantext-ticktext
        custw=int((custsitew-1)/3)-2
        sitew=int(2*(custsitew-1)/3)-3
        
    # hack to ensure at least 3 entries per line on shortlists
    slw=min(sitew,int((textwidth-4)/3)-14)-1
        
    # generate base list of dates for each week we're looking at
    weeks=[]
    for r in range(n):
        weeks.append(reportdates(0,r))

    jjs=[] # contract work jobs
    jjsquick=[] # list of the callouts, surveys, recalls
    jjsc=[]
    jjss=[] # non-exceptional subd jobs
    # just generate a list of form [age, cust/site/calendar]

    # add some colour to the weeks with appointments - same colour for all
    # separate callouts/surveys, list all those first, then contract jobs

    odd=1
    excluded=[]
    newuns=[]
    
    # contract, truck, recall, survey, callout    
    # alarm points for job types, based on age
    alarms=[60,60,7,7,3]
    mins = [3,3,1,1,1]
    # ages at which unassigned jobs become a concern
    unassalarm = [7,2,2,1,1]

    # counters to jobs
    # total, unassigned, aged, unplanned
    counts=[0,0,0,0]

    for job in tjobs:
        stop=0
        c=0
        f=0
        # get age of job
        age=job[10]

        if job[18] not in jact:
            # only considering live jobs
            stop=1
        elif job[18] in jcs3:
            # if it's a 'completed' job
            c=1
        if stop==0:
            if c==0:
                # add to total of live jobs
                counts[0]+=1

            # get age of job
            age=job[10]
            # get list of appointments in form [date, name]
            appts=job[24]

            # job type
            jtype=job[12]
            if jtype in jcon:
                jt=1 # contract
            elif jtype in jtru:
                jt=2 # truck
            else:
                try:
                    jt=joth.index(jtype)+3
                except:
                    jt=-1
                # 3 recall, 4 survey, 5 callout

            if jt>-1:
                jalarm=alarms[jt-1]
                jmin=mins[jt-1]
                junass=unassalarm[jt-1]
            else:
                jalarm=0
                jmin=0
                junass=0

            tstrlist=['--','--','--','--','--']
            # look for key job tags
            # plus search for time tag
            for t in tagslook:
                if t[0] in job[16]:
                    if tstrlist[t[2]]=='--':
                        tstrlist[t[2]]=t[1][0:2]
                    #tstring.append(t[1][0:2])
            ts=" ".join(tstrlist)

            tagdlen=-1
            for t in timetags[0]:
                if t in job[16]:
                    tagdlen=timetags[1][timetags[0].index(t)]
                    
            # generate the ref custsite string
            # customer is job[1]
            # site is job[2]
            if job[0] in ti:
                tt='t '
                where=ti.index(job[0])
                suggs=tagissues[where][1]
                whys=tagissues[where][3]
            else:
                tt='  '
                suggs=''
                whys=''
            custsite= (tt+job[0]+": "+job[1][0:custw].ljust(custw)+"/"+job[2][0:sitew].ljust(sitew,"-")).ljust(reftext+custsitew,"-")+ts.rjust(tagtext,"-")
            
            appdates=[]
            # get just the unique dates, don't care about names
            for a in appts:
                if a[0] not in appdates:
                    appdates.append(a[0])

            # now sort the dates
            appdates.sort()
            # num days planned
            ndp=len(appdates)

            sep=""
            j0=cl.appt("<")
            j1=cl.appt("=")
            j2=cl.appt(">")
            j3=cl.appt("=")
            
            # then check which week each one's in
            string=" "
            something=0
            for i in range(n):
                stub=''
                try:
                    if appdates[0] in weeks[i] and appdates[-1] in weeks[i]:
                        stub=j1+sep
                    elif appdates[0] in weeks[i]:
                        stub=j0+sep
                    elif appdates[-1] in weeks[i]:
                        stub=j2+sep
                    else:
                        for j in range(len(appdates)):
                            if appdates[j] in weeks[i]:
                                stub=j3+sep
                                break
                except:
                    pass
                if stub=='':
                    stub=cl.grey("-")+sep
                else:
                    something=1
                string+=stub
            try:
                # to judge if job is projected to finish too late
                agelast=1+(appdates[-1]-date.today()).days
            except:
                agelast=0
            if something==0 and c == 0:
                #if age>=junass:
                # if no appointments, then flag accordingly
                counts[1]+=1
                custsite=cl.hl4(custsite)
            elif age+agelast>=jalarm and c==0:
                # aged
                counts[2]+=1
                custsite=cl.hl3(custsite)
            string+= " "+tick
            # and generate the display list accordingly
            if c == 0:
                if jtype in jcon or jtype in jtru:
                    # check for job cost stuff - if job not older than
                    # jalarm, and planned appointments appear to cover
                    # all labour charge, then ignore
                    flagj=0
                    tagflag=0
                    if tagdlen>0 and ndp<tagdlen:
                        flagj=1
                    else:
                        lab =job[22][4] # labour on job
                        left=job[22][7] # estimated cost left
                        if lab>0 and left>0:
                            flagj=1
                    if 'Subd' in job[16]:
                        # don't tag timing issues for subd jobs
                        flagj=0
                    if job[0] in ti:
                        tagflag=1
                    if age+agelast>=jalarm or (flagj==1 and age>=junass) or incall==1 or tagflag==1:
                        if flagj==1:
                            counts[3]+=1
                        jjs.append([age,custsite+string,suggs,whys])
                    else:
                        if something==0 and age<junass:
                            # very new but unassigned
                            newuns.append(cl.hl4(job[0])+": "+job[2][0:slw].ljust(slw))
                        elif 'Subd' in job[16]:
                            if something==0:
                                jjs.append([age,custsite+string,suggs,whys])
                            else:
                                # if a subd job, that's assigned, and not too old, then it'll be listed separately
                                jjss.append("("+str(agelast).rjust(3)+") "+cl.header(job[0])+": "+job[2][0:slw].ljust(slw))
                        else:
                            if something==0:
                                # if there are no appointments, for a job that isn't complete, then question why
                                jjs.append([age,custsite+string,suggs,whys])
                            else:
                                # if excluded 
                                excluded.append("("+str(agelast).rjust(2)+") "+cl.header(job[0])+": "+job[2][0:slw].ljust(slw))
                else:
                    if age+agelast>=jalarm or something==0 or job[22][4]>0:
                        if job[22][4]>0:
                            string+=" *"
                        jjsquick.append([age,custsite+string])
                    else:
                        excluded.append("("+str(agelast).rjust(2)+") "+cl.header(job[0])+": "+job[2][0:slw].ljust(slw))
            else:
                jjsc.append(cl.header(job[0])+": "+job[2][0:slw].ljust(slw))
    jjs.sort()
    jjs.reverse()
    jjsquick.sort()
    jjsquick.reverse()
    excd=""
    one=0
    if incall==1:
        incd="All jobs, regardless of planning"
        incd2=incd
    else:
        incd="Oldest jobs listed first.  't' for jobs with tags suggested, or over timescale, or may not have enough appointments booked"
        incd2="Oldest jobs listed first.  't' for jobs with tags suggested, or "+cl.hl3("over timescale")+",\nor may not have enough "+cl.hl4("appointments")+" booked."

    lllen=len(incd)
    output=incd2+"\n\n"
    if len(jjsquick)>0:
        output+='Callouts / Surveys / Recalls:\n\n'
        for j in jjsquick:
            output+=j[1]+"\n"
    if len(jjs)>0:
        output+='\nOngoing jobs: (tag columns {sika,access,time,ooh,subd})'
        output+="\n\n"
        for j in jjs:
            output+=j[1]+"\n"
#            if j[2]!='':
#                output+="    Suggested: "+",".join(j[2])+"\n"
    output+="\f"
    if len(jjsc)>0:
        output+="\nCompleted jobs - have these been signed off & reports sent?\n\n"
        try:
            output+="\n".join(reflistsplit(jjsc,reftext-2+slw,textwidth," | ",1))
        except:
            output+=cl.hl4("--none--")
    output+="\n\nFairly new jobs, but still unassigned:\n\n"
    try:
        output+="\n".join(reflistsplit(newuns,reftext-2+slw,textwidth," | ",1))
    except:
        output+=cl.hl4("--none--")

    output+="\n\nNumbers in brackets below indicate time until last appointment\nAll jobs listed with oldest first.\n"
    output+="\nOther sub'd jobs:\n\n"
    try:
        output+="\n".join(reflistsplit(jjss,reftext-1+slw,textwidth," | ",0))
    except:
        output+="--none--"

    # change this so that jobs are ordered by date(s) planned in, and
    # showing age of job, so can judge whether anything needs bringing
    # forward
    output+="\n\nJobs that appear to be sufficiently planned in:\n\n"
    try:
        output+="\n".join(reflistsplit(excluded,reftext-1+slw,textwidth," | ",0))
    except:
        output+="--none--"

    etext ='Job tagging & planning documents:\n\n'
    etext+='[ ] Work through each job in Job Tag attachment\n'
    etext+='    [ ] Review tags for each job\n'
    etext+='[ ] Review UAP document\n'
    etext+='    [ ] Jobs in red are still unassigned - plan in\n'
    etext+='    [ ] Jobs in blue may be too old - why?\n'
    etext+='    [ ] Other jobs listed have some appointments planned in, but are there enough?\n'
    etext+='[ ] Review the newer unassigned jobs\n'
    etext+="[ ] Are the planned sub'd jobs ok?\n"
    etext+='[ ] Are the recently completed jobs complete, and is the report sent and job signed off?\n'
    #etext='Summary of live jobs:\n\n'
    #etext+=str(counts[0]).rjust(3)+" - Total\n"
    #etext+=str(counts[1]).rjust(3)+" - Unassigned\n"
    #etext+=str(counts[2]).rjust(3)+" - Aged\n"
    #etext+=str(counts[3]).rjust(3)+" - Check appts.\n"
    return [output+"\n\n"+tagrep,etext,tagrep]

def reflistsplit(list,slen,twidth,ind,ticks):
    # give it a list of strings, all no longer than slen
    # twidth is width of page
    # returns list of strings of form
    # ind list1, list2
    # etc, no wider than page width

    if ticks==1:
        tick=cl.grey("[ ]")
    else:
        tick=''
    numperline=int((twidth-len(ind))/(slen+4))
    output=[]
    l=0
    p=0

    for item in list:
        if p == 0:
            output.append(ind)
        output[l]+=(tick+" "+item.ljust(slen)+" ")
        p+=1
        if p==numperline:
            p=0
            l+=1
    return output
                   
def tagsuggest():
    global tjobs
    global jact
    global jcs3
    global timetags
    # works through tjobs, doing the following:
    #
    # - Isolate active jobs
    # - Look through description, searching for key words that may relate to
    #   a tag that would be useful in eworks
    # - Check the tags already set
    # - Suggest accordingly

    searchlist=[]
    # list of lists of format: [tagname, [search terms], [killers], [internals search], [internals killers]]
    # [killers] are those terms which we dont want - e.g. scaffold
    # won't be suggested if tower is in the description
    # do it all lower case
    searchlist.append([
        'ooh', # tag name we're checking for
        # terms to search for in job description
        ['out of hours','weekend','ooh'],
        # terms to avoid in job description
        [],
        # terms to search for in internal notes
        [],
        # terms to avoid in internal notes
        []
        # the 'avoid' terms override any finding of the search terms, all case-insensitive
    ])
    searchlist.append(['sika',['sika','decothane'],[],[],[]])
    searchlist.append(['lrs',['lrs','coating'],[],[],[]])
    searchlist.append(['scaffold',['scaffold','scaffolding'],['tower'],[],[]])
    searchlist.append(['PO-check',['scaffold','scaffolding'],['tower'],[],[]])
    searchlist.append(['truck',['37m','platform','truck','cherry'],['57m','ext.truck'],[],[]])
    searchlist.append(['ext.truck',['57m','ext. truck'],[],[],[]])
    searchlist.append(['PO-check',['57m','ext. truck'],[],[],[]])
    searchlist.append(['PO-check',['subd'],[],[],[]])
    searchlist.append(['tower',['tower'],['fixed','scaffolding','towers'],[],[]])
    searchlist.append(['1day',['1 day','2m1d','2 men one day','one day','1day'],['days','multiday'],[],['2day','multiday']])
    searchlist.append(['2day',['2m2d','2 days','2days'],['1/2 day','multiday'],[],['1day','multiday']])
    searchlist.append(['pointing',['pointing','repoint'],['points','tarmac'],[],[]])
    searchlist.append(['pitch',['tile','tiles','slates','slate','batten','felt','ridge','ridges'],['felt roof', 'felt flat roof', 'felt gutter','floor','flooring','carpet','coating','sika','grout'],[],[]])
    searchlist.append(['chimney',['hornch', 'haunch','flaunch'],[],[],[]])
    searchlist.append(['multiday',['days'],['2m2d','2m1d','1 day','one day','2 days','two days','2days','1day'],[],['2m2d','2m1d','1 day','one day','2 days','two days','2days','1day','2day']])
    searchlist.append(['halfday',['half day','1/2 day'],['half days'],[],['half days','multiday']])
    searchlist.append(['plastering',['plaster','plastering'],[],[],[]])
    searchlist.append(['fence',['fence','fencing'],[],[],[]])
    searchlist.append(['paving',['paving','flags'],[],[],[]])
    searchlist.append(['roof-investigation',['investigate','quote','survey'],['quoted'],[],['quote','survey','paving','tarmac','quoted']])   
    searchlist.append(['flooring',['tiling'],[],['tiling'],[]])
    searchlist.append(['permit',['permit','lane closure','road closure'],[],[],[]])
    #searchlist.append(['',[],[],[],[]])

    # sets of tags, at least one of which should be present.
    # mainly to make sure every job is flagged with time needed
    # format [setname, [tags to search for],[killers]]
    reqsets=[['time',timetags[0],['Subd']]]

    output=[['Job ref','Site','Suggested tags','Words/terms found']]
    output2=[]
    
    for job in tjobs:
        tags=[]
        try:
            for t in job[16]:
                tags.append(t.lower())
        except:
            pass
        if job[18] in jact and job[18] not in jcs3 and job[12] == 'Contract Works':
            # if job is still live, and is contract works
            ref=job[0]
            custsite=job[1][0:16]+"\\\n"+job[2][0:24]
            desc=job[23].lower()+(", ".join(job[16])).lower()
            internals=job[17].lower()+(", ".join(job[16])).lower()
            #name=job[1][0:12]+":"+job[2][0:16]
            sugg=[]
            whys=[]

            # update this to include searching separately through description and internal notes

            # if description contains search term(s) from s[1] - include
            # or if internals contain search term(s) from s[3] - include
            # but if description contains terms from s[2], or internals contain terms from s[4], then ignore

            for s in searchlist:
                exc=1
                w=''
                for term in s[1]:# description search terms
                    if term.lower() in desc:
                        exc=0
                        w=term
                        break
                if w=='': # no point checking internals if description already matched
                    # if no internals search terms specified, then just use the descripton ones
                    if len(s[3])==0:
                        ints=s[1]
                    else:
                        ints=s[3]
                    for term in ints:# internals search terms
                        if term.lower() in internals:
                            exc=0
                            w=term
                            break
                for term in s[2]:# description killer terms
                    if term.lower() in desc:
                        exc=1
                        break
                for term in s[4]:# internals killer terms
                    if term.lower() in internals:
                        exc=1
                        break
                if s[0].lower() not in tags and s[0] not in sugg and exc==0:
                    whys.append(w)
                    sugg.append(s[0])

            for s in reqsets:
                reqf=0
                for t in s[1]:
                    # try to find at least one of the tags in the
                    # reqsets list
                    if t in tags:
                        reqf=1
                        break
                if reqf==0:
                    killed=0
                    for k in s[2]:
                        if k.lower() in tags:
                            killed=1
                    if killed==0:
                        # if none found, then flag the job accordingly
                        sugg.append("{"+s[0]+"}")
                        whys.append("-"+s[0]+"- tag missing")
                    
            if len(sugg)>0 or len(tags) == 0:
                if len(tags)==0:
                    tags.append('-- none yet --')
                    sugg.append('- none set yet -')
                out1=textwrap.wrap(", ".join(sugg),width=25, initial_indent='', subsequent_indent='', expand_tabs=True, replace_whitespace=True, fix_sentence_endings=False, break_long_words=True, drop_whitespace=True, break_on_hyphens=True, tabsize=8, max_lines=None)
                out2=textwrap.wrap(", ".join(tags),width=45, initial_indent='', subsequent_indent='', expand_tabs=True, replace_whitespace=True, fix_sentence_endings=False, break_long_words=True, drop_whitespace=True, break_on_hyphens=True, tabsize=8, max_lines=None)
                out3=textwrap.wrap(", ".join(whys),width=25, initial_indent='', subsequent_indent='', expand_tabs=True, replace_whitespace=True, fix_sentence_endings=False, break_long_words=True, drop_whitespace=True, break_on_hyphens=True, tabsize=8, max_lines=None)
                #output.append([ref,custsite,'\n'.join(out1),"\n".join(out2),"\n".join(out3)])
                output.append([ref,custsite,'\n'.join(out1),"\n".join(out3)])
                output2.append([ref,sugg,tags,whys])

    return [output,"Job tag suggestions\n===================\n\nThe below are suggestions only - make sure you look at each job\n\n"+tabulate(output,headers="firstrow",tablefmt="grid"),output2]

def findmw(text):
    # searches for mw job ref in given text, and returns position if it's there
    text=text.lower()
    out=[]
    try:
        mwpos=text.index('mw')
        #print(isnumeric(text[mwpos+2:mwpos+7]))
        if text[mwpos+2:mwpos+7].isnumeric():
            out.append(text[mwpos:mwpos+7])
            out.append(text[0:mwpos]+text[mwpos+7:len(text)])
            return out
    except:
        pass
    return out

def padbar(text):
    return text+(30-len(text))*" "

def finddate(text):
    # searches for something that could possibly be a date in the text
    # looks for:
    # 6 digits together
    # 8 digits together
    # 3 pairs of 2 digits, separated by a single character
    out=[]
    d=''
    m=''
    y=''
    for j in range(len(text)):
        if text[j:j+2].isnumeric():
            if text[j+2:j+4].isnumeric():
                if text[j:j+8].isnumeric(): # if 8 digit number
                    out.append(testdate(text[j:j+8]))
                    out.append(text[0:j]+text[j+8:len(text)])
                    return out
                elif text[j:j+6].isnumeric(): # if 6 digit number
                    out.append(testdate(text[j:j+6]))
                    out.append(text[0:j]+text[j+6:len(text)])
                    return out
                elif text[j+5:j+7].isnumeric() and text[j+8:j+10].isnumeric():
                    # if of form nnnn-nn-nn        
                    out.append(testdate(text[j+8:j+10]+text[j+5:j+7]+text[j:j+4]))
                    out.append(text[0:j]+text[j+10:len(text)])
                    return out
            elif text[j+3:j+5].isnumeric() and text[j+6:j+8].isnumeric():
                # if we have a string like nn.nn.nn
                out.append(testdate(text[j:j+2]+text[j+3:j+5]+text[j+6:j+8]))
                out.append(text[0:j]+text[j+8:len(text)])
                return out
    return out

def testdate(d):
    # takes a string of 6 or 8 digits, and tries to best-guess what date format it is, and returns the datetime
    # format
    if len(d) == 6:
        # unless we've become american, a 6 digit should be in form ddmmyy
        try:
            dated=datetime.strptime(d,'%d%m%y')
        except:
            dated=d
    elif len(d) == 8:
        d1=datetime.strptime(d,'%d%m%Y')
        try:
            d2=datetime.strptime(d,'%Y%m%d')
        except:
            d2=''
        if len(d2)>0:
            if (date.today()-d1).days<(date.today()-d2).days:
                dated=d1
            else:
                dated=d2
        else:
            dated=d1
    else:
        return ''
    return dated

def emailer(to, subject, body, attach):
    # just a function to send an email message, e.g. log files
    # sends multiformat message, html part optional
    # attach is a list of the form [name, body], [name, body], ...

    email = 'andy.swallow@michaelwilsonandson.co.uk'
    password = 'Rosie.01.12.21'
    #email='admin@michaelwilsonandson.co.uk'
    cc='andy.swallow@michaelwilsonandson.co.uk'
    #password='Myson001ADM'

    emailmessage=MIMEMultipart('alternative')

    server=smtplib.SMTP('smtp.office365.com', 587)
    server.starttls() # Use TLS
    server.login(email, password) # Login to the email server

    emailmessage['Subject'] = subject
    emailmessage['From'] = formataddr(('Michael Wilson & Son', 'admin@michaelwilsonandson.co.uk'))
    emailmessage['To'] = to

    emailmessage.attach(MIMEText(body, 'html', 'utf-8')) # main body of email

    if len(attach)>0:
        for att in attach:
            attachment = MIMEApplication(att[1])
            attachment.add_header('Content-Disposition', 'attachment', filename=att[0]+'.html')
            emailmessage.attach(attachment)

    server.send_message(emailmessage)
    server.quit()

def formatter(row,i):
    # function to tidy up format of various information imported from csv files
    # 'row' is the list
    # 'i' indicates the type of list - 0 jobs, 1 appointments, 2 quotes

    global hf # external variable with the specific header titles
    global ht

    # formats to change:
    #   1 Date - change to internal date/time format
    #   2 MW refs - ensure all upper case
    #   3 Costs - convert cash string to 2 digit float number
    #   0 Anything else - strip unwanted characters, including unbreakable space
    #   Any of the 1,2,3 format, apply 0 to them first
    #   -1 Leave it exactly as it comes...

    output=[]
    for j in range(len(row)):
        if ht[i][j] != -1:
            # strip out leading/trailing space
            # plus remove unbreakable spaces
            well=row[j].replace('\xc2\xa0',' ').strip()
            if ht[i][j] != 1:
                well=well.replace('/','-')
            #output.append(row[j].replace('\xc2\xa0',' ').strip())
            if ht[i][j] == 1:
                # if it's a date format
                # try converting to datetime format, based on expected format
                if len(well) > 12:
                    try:
                        output.append(datetime.strptime(well,'%d/%m/%Y %H:%M'))
                    except:
                        output.append(well)
                else:
                    try:
                        output.append(datetime.strptime(well,'%d/%m/%Y'))
                    except:
                        output.append(well)
            elif ht[i][j] == 2:
                # if it's an MW ref, ensure upper case
                output.append(well.upper())
            elif ht[i][j] == 3:
                # if it's a cost, then convert from string to float
                try:
                    # products report, jobs with no products cause this to fail, hence 'try'
                    output.append(float(well))
                except:
                    pass
            else:
                output.append(well)
        else:
            # for those fields we don't touch at all
            output.append(row[j])

    return output

def jrgen(jlist,jlinks,st,fn,dail):
    # update to include marker for incomplete jobs
    # and option whether or not to include them
    # default should be completed jobs only
    
    # takes the tdays[] format list, processes through all of it, and
    # returns a list of the form [mwref, text, text2] where text is the job
    # report, including total times, text2 without totals
    # tdays=[]
    # turnover daily data = [ date, [ [engineer
    # name, job ref, notes, recommendations, start, end] ], [ callouts
    # £, contract £, subcontract £, truck £, total £ ] ]
    
    # parameter jlist is a list of job refs to build reports for
    # (generated by the photosfolder function, at least currently)

    # potentially expand the list of reports that are needed, to
    # include future or ongoing jobs.  For the incomplete jobs, just
    # generate header, without costs, but including description and
    # any notes/photos so far, plus a summary of timings - start date,
    # number of days planned, number of days estimated, and a calendar
    # printout showing what days have been planned in

    # st and fn are the day offsets to look at e.g. st=-1000, fn=0 for
    # everything, or st=-2,fn=-2 for 2 days ago

    # dail=1 to include job descriptions more often
    
    # n is the number of days to restrict to, e.g. 2 for the past 2
    # days appts only
    
    global tday2
    global tjobs
    global jcs3
    global jtypes
    full=[]
    output=[]
    refslist=[]
    timeslist=[]
    slist=[]
    plist=[[],[],[],[]]
    prevdays=[[],[],[],[]]
    # timeslist can be the record of time spent on job by each engineer.  Format:
    # [job ref, [[name, time (seconds?), photos link html]]]
    bar = Bar(padbar('Generating job reports'), max=len(tday2))

    for day in tday2:
        age=(day[0]-date.today()).days
        for appt in day[1]:
            if appt[1] in jlist and age>=st and age<=fn:# and len(appt[2])>5:
                j=-1
                # first find if the job has already been started
                #try:
                if appt[1] in refslist:
                    j=refslist.index(appt[1])
                else:
                    refslist.append(appt[1])
                    timeslist.append([appt[1],[]])
                    cust=''
                    site=''
                    signoff=0
                    for job in tjobs:
                        if appt[1] == job[0]:
                            #print(appt[1])
                            cust=job[1]
                            site=job[2]
                            desc='Short:\n'+str(job[15])+"\n\nFull:\n"+str(job[23])
                            #short=job[15]
                            # test if job itself is actually complete,
                            # then can generate the separate report to
                            # email for job sign off
                            if (job[18] in jcs3 or fn>0) and job[12] in ['Contract Works']:
                                signoff=1
                                slist.append(1)
                            else:
                                slist.append(0)
                            break
                    output.append([appt[1]+"-"+site,jrheader(appt[1],cust,site,''),'',''])
                    d=''
                    if dail==1:
                        d=cl.poor("Job Descriptions:")+"\n"+desc
                    full.append(jrheader(appt[1],cust,site,d))
                    
                    output[j][1]+="\n"+cl.good("Description:")+"\n"+desc+"\n\n"
                    if signoff == 1:
                        output[j][3] = "The photos link takes you to the Site folder, you will need to be signed in to your @michaelwilsonandson.co.uk account to access this.  There should be folders for each date the job was attended, each with engineer folders containing their photos.\nPlease review the job, and 'Reply All' with any comments and/or approval\n"
                        output[j][3] += jrheader(appt[1],cust,site,'')
                        output[j][3]+="\n"+cl.good("Description:")+"\n"+desc+"\n\n"
                    wh=-1
                    for jj in range(len(jlinks)):
                        if appt[1] == jlinks[jj][0]:
                            wh=jj
                            break
                    if wh>-1:
                        output[j][2]=jlinks[wh][1]+" \n\n"
                    #except:
                    #    refslist.append(appt[1])
                    #    output.append([appt[1],''])
                if (datetime.now()-appt[5]).days>=0: # if there's a finish time, i.e. the appointment has happened
                    applen=(appt[5]-appt[4]).seconds
                    eng=-1
                    if len(timeslist[j][1])>0:
                        for i in range(len(timeslist[j][1])):
                            if appt[0] == timeslist[j][1][i][0]:
                                eng=i
                                break
                    if eng == -1:
                        timeslist[j][1].append([appt[0],0,0])
                    timeslist[j][1][eng][1]+=applen # add this appt time to total for that engineer for this job
                    output[j][1]+=jrdate(appt[4],appt[5],appt[0],timeslist[j][1][eng][1])+"\n"
                    full[j]+=jrdate(appt[4],appt[5],appt[0],-1)+"\n"
                    
                    if slist[j] == 1:
                        # no time totals on the sign off reports
                        output[j][3]+=jrdate(appt[4],appt[5],appt[0],0)+"\n"

                    if len(appt[2])>20: # 20 characters is enough to cut out the 'see name's pda' comments
                        output[j][1]+=jrnotes(appt[2],0)+"\n"
                        full[j]+=jrnotes(appt[2],0)+"\n"
                        if slist[j] == 1:
                            output[j][3]+=jrnotes(appt[2],0)+"\n"
                    if len(appt[3])>0:
                        output[j][1]+=jrrecs(appt[3],0)+"\n"
                        full[j]+=jrrecs(appt[3],0)+"\n"
                        if slist[j] == 1:
                            output[j][3]+=jrrecs(appt[3],0)+"\n"
                    # parts needed bit
                    if len(appt[8])>0:
                        output[j][1]+=jrparts(appt[8],0)+"\n"
                        full[j]+=jrparts(appt[8],0)+"\n"
                        if slist[j] == 1:
                            output[j][3]+=jrparts(appt[8],0)+"\n"
                else:
                    applen=(appt[5]-appt[4]).seconds
                    eng=-1
                    if len(timeslist[j][1])>0:
                        for i in range(len(timeslist[j][1])):
                            if appt[0] == timeslist[j][1][i][0]:
                                eng=i
                                break
                    if eng == -1:
                        timeslist[j][1].append([appt[0],0,0])
                    timeslist[j][1][eng][1]+=applen # add this appt time to total for that engineer for this job
                    output[j][1]+=jrdate(appt[4],appt[5],appt[0],timeslist[j][1][eng][1])+"\n"
                    full[j]+=jrdate(appt[4],appt[5],appt[0],-1)+"\n"
                    
                    if slist[j] == 1:
                        # no time totals on the sign off reports
                        output[j][3]+=jrdate(appt[4],appt[5],appt[0],0)+"\n"

        bar.next()
    bar.finish()
    return [output,full]

def photofoldertree(where,rootflag):
    # function to process through old folders and suggest formatted names for jobs
    # could possibly be removed?
    
    # currently just works through and prints suggested name formats.
    # need it to be a function to call after job data read from files, to potentially identify
    #  - job records in more than one location
    #  - sites with more than one folder / name

    # add an extra 'root' option to the function, where
    #  - we pass the customer root as option, e.g. in Equans folder
    #  - It then works through each site folder, sampling a job from each, and lists any folders which refer to
    #  - the same site
    global tjobs

    # works through the given folder and identifies any folders with an mw ref num in title
    mwfolders=[]
    os.chdir(where)
    jreflist=[]
    fldrlist=[]
    custlist=[]
    inroot=''
    for root,dirs,files in os.walk(".", topdown=False):
        for name in dirs:
            test=findmw(name)
            ps=[]
            if len(test)>0:
                ps=test[0]
            if rootflag == 0:
                if root != inroot:
                    inroot=root
                    print("Working in "+root)
                if len(ps)>0:
                    # if an mwref has been found, test[1] is what's left of the string, so look for a date
                    dt=finddate(test[1])
                    # finddate() returns [datetime(), remaining]
                    # finddate() returns nothing if no date found, so folder left alone
                    if len(dt)>0:
                        try:
                            newname=dt[0].strftime('%Y-%m-%d ')+ps.upper()+" "+dt[1].strip()
                            newname=newname.strip()
                        except:
                            newname=name
                        same=0
                        if os.path.join(newname) == os.path.join(name):
                            same=1
                        mwfolders.append([ps.upper(),os.path.join(root,name),os.path.join(root,newname),same])
                        if same == 0:
                            print(os.path.join(root,name)+"\n  ---> "+os.path.join(root,newname))
                            if dryrun == 0:
                                try:
                                    os.rename(os.path.join(root,name),os.path.join(root,newname))
                                except:
                                    pass
                        else:
                            size=get_dir_size(os.path.join(root,name))
                            if size<100:
                                print("ickle")
            else:
                if len(ps)>0:
                    # if there's an mw ref in the folder name, then find the site info
                    site=''
                    ps=ps.upper()
                    found=0
                    for job in tjobs:
                        if ps == job[0]:
                            site=job[2]+" "+job[19]
                            found=1
                            break
                    if found == 1:
                        if site not in custlist:
                            custlist.append(site)
                            jreflist.append(ps)
                            fldrlist.append(root)
                        elif root not in fldrlist and ps not in jreflist:
                            # if customer alread found, but under a different folder...
                            print("'"+root+"': should possibly be filed under --> '"+site+"'?")

def get_dir_size(path):
    total = 0
    with os.scandir(path) as it:
        for entry in it:
            if entry.is_file():
                total += entry.stat().st_size
            elif entry.is_dir():
                total += get_dir_size(entry.path)
    return total
def quotechase(f):
    global tquot
    # function to trawl through quotes list and identify those that
    # need chasing in some way, according to following criteria:

    # f is 0 or 1
    # 0 for daily list - anything that was generated 3 days ago, and needs further chaser
    # 1 for the weekly list of stuff that needs further email or phones chasing
    
    # First chaser email, 3 days after submission:
    # Submitted Mon, chase Wed.  Tue - Thu, Weds - Fri, Thu - Mon, Fri - Tue

    # Phone call week after submission - aim for Thursday

    # Two weeks after sending, send further chaser email, identical to original chaser

    # 29 days after sending, or the Friday before if that falls on a
    # weekend, send further email advising quote expiring soon, and
    # warning that cost may be requoted if still wishing to proceed
    # after this point

    # 5 days after expiry, or the Monday after if falls on weekend, reject the quote

    #tquot=[] # turnover quotes list = [ mwref, customer, site name,
    #           cost, age, email flag, cust ref flag, status ]

    # reportdates(0,-1) returns a list of dates in previous week
    prevweek = reportdates(0,-1)
    weekbefore=reportdates(0,-2)
    icd=3
    lastchase = [29,29,29,29,28,27,26] # days after submission to send final
                                 # reminder chaser
    removeme = 35
    emslist=112
    
    doomsday=0
    if date.today().weekday() == 3:
        doomsday=1
    sow=0
    if date.today().weekday() == 0:
        # if it's a Monday, then show everything due to expire soon
        sow=1
    quotes=[[],[],[],[],[]] # 1st, 2nd, 3rd, last chase nos and removal
    wday=['Mon','Tue','Wed','Thu','Fri','Sat','Sun']
    ems=[]
    for quot in tquot:
        if quot[7] == 0:
            # if it's a 'processed' quote, which is all we're interested in here
            qdate = date.today()+relativedelta(days=-quot[4])
            qday = qdate.weekday() # returns 0 Mon, 1 Tue, etc.
            if len(quot[6])>3:
                cr="/ "+quot[6]
            else:
                cr=""
            if quot[4] == 14:
                mk="*"
            else:
                mk=""
            txtl1="**"+quot[0]+"** ("
            txtl2=") : "+mk+quot[1]+" / "+quot[2]+cr+" : "+cash(quot[3])+mk

            icdd=0
            if quot[4] >= icd and quot[4]<=icd+2:
                # anything between 3 and 5 days in age
                icdd=1
                quotes[0].append(txtl1+str(quot[4])+txtl2)
            if qdate in prevweek and icdd == 0:
                # if it was submitted last week, then follow up
                # unless included in the first test, i.e. no more than 5 days old
                quotes[1].append(txtl1+'Thu'+txtl2)
            elif qdate in weekbefore:
                # if submitted 2 weeks ago
                quotes[2].append(txtl1+wday[qday]+txtl2)
            elif quot[4] == lastchase[qday] or (quot[4]>=25 and quot[4]<=30):
                # final reminder chaser
                quotes[3].append(txtl1+str(quot[4])+txtl2)
                pass
            elif quot[4] >= removeme:
                # if it's past point of no return
                quotes[4].append(txtl1+str(quot[4])+txtl2)

    init='- [ ] '
    output=''
    output+="## "+date.today().strftime('%a %d %b %Y')+"\n\n"
    output+="Numbers in brackets indicate age of quote, in days\n\n"
    if f==0:
        output+="*The following recent quotes may need an initial chaser email:*\n\n"
        output+=init+('\n'+init).join(quotes[0])+"\n\n"
        output+="*Please also review quote details - name, contact nos., email address(es) - are they all correct?*"
    else:
        output+="*These quotes were submitted last week - phone call chase needed this week?*\n\n"
        output+=init+('\n'+init).join(quotes[1])+"\n\n"
        output+="*These quotes were submitted 2 weeks ago, and need a further chase email this week:*\n\n"
        output+=init+('\n'+init).join(quotes[2])+"\n\n"
        output+="*These quotes will expire soon - send final chaser email, with reminder that costs may need to be requoted if goes past expiry date:*\n\n"
        output+=init+('\n'+init).join(quotes[3])+"\n\n"
        output+="*These quotes are expired and need to be closed down:*\n\n"
        output+=init+('\n'+init).join(quotes[4])+"\n\n"
    
    return output
        
def datachew(guess):
    global data
    global acs
    global jcs
    global jas
    global qsc
    global subs
    global truck
    global ompd
    global truckcharge

    # Goes through the inputted data[] lists, and converts into the below formats

    tjobs=[] # turnover jobs data = [ mwref, customer, site name,
             # cost, total appts, worked appts, # sub'd appts, # truck
             # appts, start date, last date, job age, complete(-1) or
             # days until next appt, job type, email flag, products[],
             # cust ref flag, tags[], po num, status, labour,
             # description, applist] products[] - [code, price]
    tdays=[] # turnover daily data = [ date, [ [engineer name, job
             # ref, notes, recommendations] ], [ callouts £, contract
             # £, subcontract £, truck £, total £ ] ] (leave door open
             # for variety of cost types to split into) (costs[]
             # format to confirm...)
    tquot=[] # turnover quotes list = [ mwref, customer, site name,
             # cost, age, email flag, cust ref flag, status ]

    # function structure notes:
    #     First pass over appointments data, using it to start the tjobs list, and make all the
    #     (non-empty) entries for the tdays list
    #     Then work through jobs data, using it to fill in more of the blanks in tjobs

    log('First pass of appointment data')
    bar=Bar(padbar('Appointments data'), max=len(data[1]))
    for row in data[1]:
        # see if job already found
        fd=-1
        if len(tjobs)>0:
            try:
                for j in range(len(tjobs)):
                    if row[0] == tjobs[j][0]:
                        fd=j
                        break
            except:
                pass
        if fd == -1:
            # if not found, then create a blank job list
            d=datetime.strptime('01/01/1900','%d/%m/%Y')
            # default to old start/end dates, which should both be replaced as other data is imported
            tjobs.append([row[0],'','',row[3],0,0,0,0,d,d,0,0,'Contract Works',0,[],0,[],'','','',0,'',[],'',[]])
            # default to job type of Contract Works, to avoid daily costs being missed in the case of old jobs
            # If we've held a job for longer than 6 months, it could only really be Contract Works.
            # since working from appointments data, customer name, site, etc. aren't available

        # now that we know where it is in tjobs, can adjust various bits
        # careful to only count those appointments which aren't cancelled or abandoned

        if row[2] in acs: # if appointment is still live, or completed
            tjobs[fd][24].append([row[4].date(),row[1]])
            # build list of scheduled dates for this job
            # yes we're duplicating information.  It's only a one-pass script

            # increase total number of appointments
            if row[1] not in truck:
                tjobs[fd][4]+=1
            age=(datetime.now()-row[4]).days

            if age>0 and row[1] not in truck:
                # if appointment is historic, then add to worked
                tjobs[fd][5]+=1
            if row[1] in subs:
                # if it's a sub appointment
                tjobs[fd][6]+=1
            if row[1] in truck:
                # if it's a truck appointment
                tjobs[fd][7]+=1
            # don't touch start date, since that can come from original job, rather than first appointment

            # test appt date with current last date, and replace if appropriate
            if tjobs[fd][9]<row[4]:
                tjobs[fd][9]=row[4]

            # rest of tjobs[][] entry populated from jobs list, not appointments
            # so now populate tdays[] list
            # see if that date has already been started yet or not
            fd=-1
            if len(tdays)>0:
                try:
                    for j in range(len(tdays)):
                        if row[4].date() == tdays[j][0].date():
                            fd=j
                            #print(fd)
                            break
                except:
                    pass
            if fd == -1:
                # if not found, then create a blank date entry
                tdays.append([row[4],[],[0,0,0,0,0,0,0,0,0,0,0]])
                # since working from appointments data, customer name, site, etc. aren't available

            tdays[fd][1].append([row[1],row[0],row[6],row[7],row[4],row[5],row[8],row[2],row[9]])
            # add job ref and engineer to daily list
            # (plus user notes and recommendations and start/finish times - may as well include them)
            # (can't have unique list since need to calculate daily costs from this bit)
            # and add last-updated-time too, since photos script will make use of it
            # and appt status, for same reason
            # and now 'parts needed'
        bar.next()
    bar.finish()

    log('First pass through jobs data')
    bar=Bar(padbar('Jobs data'),max=len(data[0]))
    for row in data[0]:
        # now work through the jobs list

        # 0 ['Job Ref', 'Start Date', 'Purchase Order Ref', 'Job Type', 'Status', 'Customer Name',
        #    'Customer Job Ref', 'Customer Site', 'Site Postcode', 'Job Sub Total']

        # first populate tjobs: customer, site, cost total, age, completion flag, unassigned flag, email flag,
        # po flag, and cust ref flag

        # find where the job might be in tjobs[] first
        d=datetime.strptime('01/01/1900','%d/%m/%Y').date()
        fd=-1
        try:
            for j in range(len(tjobs)):
                if row[0] == tjobs[j][0]:
                    fd=j
                    break
        except:
            pass
        if fd == -1:
            # if not found, then create a blank job list
            tjobs.append([row[0],'','',0,0,0,0,0,d,d,0,1000,0,0,[],0,[],'','','',0,'',[],'',[]])
            # last element is postcode, which won't be available until an appointment appears for the job

        #tjobs=[] # turnover jobs data
        #     = [ mwref, customer, site name, cost, total appts, worked appts, # sub'd appts, # truck appts, start date, last date,
        #         job age, complete(-1) or days until next appt, type, empty space, po# flag, cust ref flag ]

        tjobs[fd][1] = row[5] # customer name
        # set site name - choosing from what's available
        if len(row[7]+row[8])>10: # if there's at least something there
            if len(row[7])>len(row[8]):  # get a site name from one of the 2 available fields
                tjobs[fd][2] = row[7] # site name
            else:
                tjobs[fd][2] = row[8]
        else:
            tjobs[fd][2] = row[5] # as a last resort, site name is just customer name - the folder will also
                                  # have postcode on it anyway
                                  
        tjobs[fd][3] = row[9] # total cost
        tjobs[fd][8] = row[1] # start date
        tjobs[fd][19]= row[2] # site postcode
        if tjobs[fd][9] == d:
            tjobs[fd][9] = row[1] # only change start date if other appointments haven't already changed it
        tjobs[fd][10] = (datetime.now()-row[1]).days # job age, in days
        tjobs[fd][15] = row[6] # short description
        #tjobs[fd][17] = row[2] # po #

        tjobs[fd][12] = row[3] # job type
        # if job completed or abandoned, then adjust age accordingly
        if row[4] in jas:
            tjobs[fd][11] = -1000
        elif row[4] in jcs:
            tjobs[fd][11] = -1
        else:
            tjobs[fd][11] = 1000
        # set job status
        tjobs[fd][18] = row[4]
        bar.next()
    bar.finish()

    # then work through the quotes list
    if len(data[2])>0:
        log("Working through the quotes list")
        bar=Bar(padbar('Quotes data'),max=len(data[2]))
        for row in data[2]:
            if row[2] in qsc:
                # hf[2] = ['Quote Ref', 'Quote Date', 'Status', 'Customer Name', 'Customer Job Ref', 'Last Updated On', 'Del Full Name', 
                #          'Email Address', 'Description', 'Quote Sub Total']
                # = [ mwref, customer, site name, cost, age, email flag, cust ref flag, quote status]

                d=datetime.strptime('01/01/1900','%d/%m/%Y').date()
                fd=-1
                if len(tquot)>0:
                    try:
                        for j in range(len(tquot)):
                            if row[0] == tquot[j][0]:
                                fd=j
                                break
                    except:
                        pass
                if fd == -1:
                    # if not fd, then create a blank quote list
                    tquot.append([row[0],'','',0,0,'','',-10000])

                tquot[fd][1]=row[3] # customer name
                tquot[fd][2]=row[7] # site name
                tquot[fd][3]=row[9] # cost
                tquot[fd][4]= (datetime.now()-row[1]).days #age
                tquot[fd][5]=row[7] # email
                tquot[fd][6]=row[4] # customer job ref
                if row[2] == 'Processed':
                    tquot[fd][7] = 0
                    # change age to since quote was last adjusted, to
                    # try not to be caught out by quotes which may tke
                    # a few days to prepare?
                    #tquot[fd][4] = (datetime.now()-row[5]).days
                    # if a currently outstanding quote
                elif row[2] == 'Converted To Job' or row[2] == 'Accepted':
                    # if accepted then status is number of days that decision took
                    tquot[fd][7] = max((row[5]-row[1]).days,1)
                elif row[2] == 'Rejected':
                    # if rejected then status is negative, number of days taken to decide
                    tquot[fd][7] = min((row[1]-row[5]).days,-1)
            bar.next()
        bar.finish()
        
    # now work through the products list
    if len(data[3])>0:
        log("Working through the products report")
        bar=Bar(padbar('Products data'),max=len(data[3]))
        for row in data[3]:
            # ['Job Ref', 'Start Date', 'Product Name', 'Item Code', 'Quantity', 'Price', tags]
            # to update relevant jobs and appointments with info re truck use
            # adding product lists to each job, can do the rest later
            try:
                for j in range(len(tjobs)):
                    if row[0] == tjobs[j][0]:
                        tjobs[j][14].append([row[3],row[4],row[5],row[6]])
                        if row[3].strip() == 'Labour':
                            # separately sum the labour cost
                            # use to more accurately measure turnover
                            tjobs[j][20]+=row[5]
                        # add a bit to check if tags list (tjobs[j][16]) is populated, and if not then
                        # do so
                        if len(row[7])>2:
                             tjobs[j][16] = row[7].split(',')

                        tjobs[j][17]=row[8] # job internal notes
                        tjobs[j][23]=row[1] # job description
                        break
            except:
                pass
            bar.next()
        bar.finish()
        
    log("Second pass through the appointments data")
    bar=Bar(padbar('Appointments again'),max=len(tdays))
    for row in tdays:
        # remember appointments are only listed in tdays[] if they're live
        day=row[0]
        fd=0
        for entry in row[1]: # now go through the appts for this day
            if entry[7] in acs: # only count 'live' appts
                for j in range(len(tjobs)):
                    #for job in tjobs: # and for each, find the relevant job in tjobs
                    if tjobs[j][0] == entry[1]:
                        fd=1
                        #tjobs[j][4]+=1 # no of appts
                        #if day<=date.today():
                        #    tjobs[j][5]+=1 # no of worked appts
                        #if entry[0] in subs:
                        #    tjobs[j][6]+=1 # if it's a subbie
                        #if entry[0] in truck:
                        #    tjobs[j][7]+=1 # if it's the truck
                        tjobs[j][9]=max(tjobs[j][9],day) # last date of job
                        if tjobs[j][11]>=0 and (day-datetime.now()).days>0:
                            # num of days until next appt.
                            tjobs[j][11] = min(tjobs[j][11], (day-datetime.now()).days)
                        break # does this just break the inner 'for' loop?
        bar.next()
    bar.finish()
    
    # now go through jobs - not sure about this bit?
    log("Second pass through jobs data")
    bar=Bar(padbar('Jobs again'),max=len(tjobs))
    types=['Contract Works','Survey FOC','Recall FOC','Reactive Callout','Truck']
    typesflag=[2,6,9,1,4]
    fullexplain=''
    for row in tjobs:
        #fullexplain+=jobcost(row[0],tjobs)
        for j in range(len(tdays)):
            for appt in tdays[j][1]:
                if row[0] == appt[1]:
                    # this is where we calculate daily costs per job type etc.
                    # row[3] is cost, row[4] number of appts
                    lab = row[20] # labour cost for the job, ripped from products report
                    cpa=0
                    if lab>0 and row[18] not in jcs and guess == 1:
                        # to work on
                        # only if not in jcs, since if job is completed then the num of appts
                        # must be 'right'
                        # if there is a labour value, then use that to estimate
                        # how many man-days should be needed
                        # then divide job cost accordingly
                        aps = max(lab/ompd,row[4])
                        cpa=row[3] / aps
                    else:
                        cpa=row[3]/max(row[4],1) # cpa - cost per appt
                    
                    subd=row[6]
                    truckd=row[7]
                    try:
                        jtype=typesflag[types.index(row[12])]
                    except:
                        jtype=0
                    # tdays ...[ callouts £, contract £, subcontract £, truck £, total £, # surveys, # quotes, $ quotes, # recalls ] ]
                    # now write to appts[2][]
                    if appt[0] not in truck:
                        if jtype==6 or jtype==9:
                            tdays[j][2][jtype-1]+=1/max(row[4],1)
                        elif jtype>0:
                            tdays[j][2][jtype-1]+=cpa
                        if appt[0] in subs:
                            tdays[j][2][2]+=cpa
                        tdays[j][2][4]+= cpa # just add full job cost for truck appts.
                    else:
                        tdays[j][2][3]+=truckcharge
                        #if appt[0] not in truck:
                        #tdays[j][2][4]+= row[3]/1 # just add full job cost for truck appts.
            if (row[8].date()-tdays[j][0].date()).days == 0 and row[12] == 'Contract Works':
                # counting new jobs received
                tdays[j][2][9]+=1
                tdays[j][2][10]+=row[3]
        bar.next()
    bar.finish()

    # sort the tdays[] list, and add in the gaps
    # rewrite this - make sure it works precisely as it should
    mnd=datetime.now().date()
    mxd=datetime.now().date()
    for dy in tdays:
        if (dy[0].date()-mnd).days<0:
            mnd=dy[0].date()
        if (dy[0].date()-mxd).days>0:
            mxd=dy[0].date()
    total = (mxd-mnd).days +1
    st=mnd
    tday2=[]
    for j in range(total):
        tday2.append([st+timedelta(days=j),[],[0,0,0,0,0,0,0,0,0,0,0]])

    for dy in tdays:
        i = (dy[0].date()-mnd).days
        tday2[i] = dy
        tday2[i][0]=tday2[i][0].date()

    # go through quotes list and record number/value per day
    #tquot=[] # turnover quotes list
    #        = [ mwref, customer, site name, cost, age, email flag, cust ref flag, status ]
    # hf[2] = ['Quote Ref', 'Quote Date', 'Status', 'Customer Name', 'Customer Job Ref', 'Last Updated On', 'Del Full Name', 
    #          'Email Address', 'Description', 'Quote Sub Total']
    if len(data[2])>0:
        bar=Bar(padbar('Sorting quotes per day'),max=len(data[2]))
        for qut in data[2]:
            dt=qut[1].date()
            here=-1
            for j in range(len(tday2)):
                if (tday2[j][0]-dt).days == 0:
                    here=j
                    break
            if here>=0:
                tday2[here][2][6]+=1
                tday2[here][2][7]+=qut[9]
            # add a bit for testing if quote accepted, and value if it has
            #if qut[2] == 'Converted To Job' and (tday2[j][0].date()-qut[5].date()).days == 0:
            #    tday2[here][2][9]+=1
            #    tday2[here][2][10]+=qut[9]
            bar.next()
        bar.finish()

    log("Data processed and collated")
    return [tjobs,tdays,tquot,tday2]
    
def jobcost(g):
    # change so that this function takes a job ref, so can be called
    # one job at a time. It can return the same 5 variables, just
    # non-list formats.  Then call this function from datachew(), and
    # the datachew() function can just return the lists that are built
    # by this function

    # also add a a function that this one can call, that trawls
    # through the tags and descrption for a job and tries to get the
    # recommended time to spend on it
    
    global ompd
    global tjobs
    global jas
    global jact
    global longj
    global truck
    global timetags
    # function to put together cost details for jobs
    # in particular explaining the cost-per-appointment and how it's calculated
    # this is where we calculate daily costs per job type etc.
    # row[3] is cost, row[4] number of appts
    costs = [['Ref','Customer','Site','Cost','Labour','Sched. appts.','CPA','Remaining']]
    costs[0]=headerify(costs[0])
    concerns=[] # separate list to track multi day jobs, age, dates, etc.
    #             [ ref, cust, site, desc., age, labour, # appts (estimated from labour), # appts planned, appts worked, [dates] ]
    leftover=0
    unass=0
    leftoverjobs=[]
    for j in range(len(tjobs)):
        # want to change this so there's a bit here looking for a time
        # tag in the job, then working out the cost per day
        # accordingly, to circumvent any guesswork re the labour line
        
        lab = tjobs[j][20] # labour cost for the job, ripped from products report
        guessed=0
        if lab>0 and tjobs[j][18] in jact and g == 1:
            aps = max(lab/ompd,tjobs[j][4])
            cpa=tjobs[j][3] / aps
            if lab/ompd>tjobs[j][4]:
                guessed=1
        else:
            cpa=tjobs[j][3]/max(tjobs[j][4],1) # cpa - cost per appt
        left=0
        if tjobs[j][18] in jact:
            if tjobs[j][4] == 0:
                left=-tjobs[j][3]
            else:
                left=tjobs[j][3]-tjobs[j][4]*cpa
        tjobs[j][22]=[tjobs[j][0],tjobs[j][1],tjobs[j][2],tjobs[j][3],lab,tjobs[j][4],cpa,abs(left),guessed, tjobs[j][4]-tjobs[j][5]]
        # ref, cust, site, cost, labour, total appts, cpa, left, guess flag, num planned appts left
        # 0 ref, 1 cust, 2 site, 10 age, 3 cost, 20 labour, 22-6 cpa, 24 dates/eng list 
        # concerns format:
        # [ ref, cust, site, desc., age, cost, labour, # appts (estimated from labour), # appts planned, appts worked, [dates] ]

        # this figure wants massaging so it also accounts for all assigned upcoming work
        leftover+=abs(left)
        leftover+=(max(0,tjobs[j][4]-tjobs[j][5])*cpa)

        
        if left<0: # keep separate tally of unassigned jobs
            unass+=abs(left)
        if abs(left)>0:
            leftoverjobs.append(tjobs[j][0])
        if abs(left)>0 and tjobs[j][18] in jact:
            # if has value, leftover cost, and isn't cancelled or abandoned
            costs.append([tjobs[j][0],tjobs[j][1][0:11],tjobs[j][2][0:20],cash(tjobs[j][3]),cash(lab),num(tjobs[j][4]),cash(cpa),cash(left)])
            if tjobs[j][3]/cpa > 2 or (longj>0 and tjobs[j][3]/cpa > longj):
                # flag anything that looks to need more than 2 appointments
                concerns.append([tjobs[j][0],tjobs[j][1],tjobs[j][2],tjobs[j][10],tjobs[j][3],lab,round(tjobs[j][3]/cpa),tjobs[j][4],tjobs[j][5],tjobs[j][24]])
        elif tjobs[j][18] in jact and cpa>0 and longj>0 and tjobs[j][3]/cpa > longj:
            # add on the long jobs too
            concerns.append([tjobs[j][0],tjobs[j][1],tjobs[j][2],tjobs[j][10],tjobs[j][3],lab,round(tjobs[j][3]/cpa),tjobs[j][4],tjobs[j][5],tjobs[j][24]])
    return [costs,leftover,leftoverjobs,unass,concerns]

def jobfolders():
    # processes through the jobs folder
    # moves anything authorised or invoiced out of the way
    # names according to site, where possible
    # creates empty folders for upcoming jobs
    
    # note this does not delete anything - it only ever moves folders
    # where it thinks they should go.
    global root
    global jobsfolder
    global tjobs
    global jcs # statuses (and folder names) for which to move job folders
    global jact # job statuses which should be in jobfolders
    global jas
    global dryrun

    subs=['PO','Report','Pics']

    # scan through the jobs folder
    # save each existing folder name
    # rename if short
    #    save the new name as well
    # move if either invoiced or authorised

    # find max current job number on system
    mj=0
    for job in tjobs:
        mj = max(mj,int(job[0][2:7]))
    
    os.chdir(os.path.join(root,jobsfolder))
    origfl = []
    refl   = []
    print("Checking existing job folders")
    with os.scandir(".") as itr:
        for entry in itr:
            en=entry.name
            if entry.is_dir() and en[0:2].lower() == 'mw' and en[2:7].isdigit():
                # if a folder an mw start, with 5 digits after
                origfl.append(en)
                refl.append(en[0:7].lower())
                # if an mwref name with no cust/site info
                found=0
                for job in tjobs:
                    if job[0].lower() == en[0:7].lower():
                        if len(en)<9:
                            if len(job[2])>2:
                                newname = en[0:7]+" - "+job[2]
                            else:
                                newname = en[0:7]+" - "+job[1]
                        else:
                            newname=en
                        if job[18] in jcs:
                            fmove = job[18]
                        elif job[18] in jas:
                            fmove='Other'
                        else:
                            fmove=''
                        found=1
                        break

                # if not found on tjobs list, then it may be deleted, in which case move it
                if found == 0 and int(en[2:7])<=mj:
                    fmove='Other'
                    newname=en
                #if found == 1:
                log("Possibly Moving "+en+" to "+fmove+"/"+newname)
                if dryrun == 0:
                    if len(fmove)>0:
                        log("Moving "+en+" to "+fmove+"/"+newname)
                        shutil.move(os.path.join(root,jobsfolder,en), os.path.join(root,jobsfolder,fmove,newname))
                    elif newname != en and int(en[2:7])<=mj:
                        log("Renaming "+en+" to "+newname)
                        os.rename(en, newname)
                        
    # refl is now the list of all job refs already existing in the folder
    
    # then work through existing jobs
    # if job live and folder already exists, then move on
    # otherwise, if job live, then create the folder
    bar = Bar(padbar('Moving/Renaming folders'), max=len(tjobs))
    #mj=0
    for job in tjobs:
        #mj = max(mj,int(job[0][2:7]))
        if job[18] in jact and job[0].lower() not in refl:
            log("Creating folder "+job[0]+" - "+job[2])
            if len(job[2])>2:
                newname=job[0]+" - "+job[2]
            else:
                newname=job[0]+" - "+job[1]
            #print("Creating"+job[0]+job[2])
            if dryrun == 0:
                os.mkdir(newname)
                for s in subs:
                    os.mkdir(os.path.join(newname,s))
        bar.next()
    bar.finish()

    bar = Bar(padbar('Creating blank folders'), max=10)

    # then create the next 10 job refs
    for j in range(10):
        jnum=mj+1+j
        if dryrun == 0 and "mw"+str(jnum) not in refl:
            os.mkdir("MW"+str(jnum))
            for s in subs:
                os.mkdir(os.path.join("MW"+str(jnum),s))
        bar.next()
    bar.finish()
            
    return
    
def headerify(names):
    out=[]
    for n in names:
        out.append(cl.hl1(n))
    return out
def findupcoming(n):
    # find upcoming jobs, with a view to emailing details of those
    global tday2
    global tjobs
    global aos
    global aws
    global root
    global photosfolder
    global dryrun
    global photosdo

    # n is the number of days to look back, in terms of deleting empty folders
    # c is the number of days to look back for creation, e.g. if hasn't been run for 2 days,
    # then historic folders may need creating, if we're behind for whatever reason
    
    #tdays=[] # turnover daily data
    #        = [ date, [ [engineer name, job ref, notes, recommendations] ], [ callouts £, contract £,
    #            subcontract £, truck £, total £ ] ]
    #        (leave door open for variety of cost types to split into)
    #        (costs[] format to confirm...)
    
    # filter out those appointments that need attention
    # remember **anything** over the past n days needs looking at, since may be renaming, deleting, etc.

    os.chdir(os.path.join(root,photosfolder))
    pfolders=[]
    jobsup=[] # list of job refs 
    photolinks=[]
    bar=Bar(padbar('Find upcoming jobs'), max=len(tday2))
    # for each appointment, just need: Customer name, site name,
    # folder name, engineer name, past/future flag then can sort list
    # in folder names order, and hopefully improve the order/way the
    # checking is done e.g. easier to possibly identify if a
    # particular appointment folder can be deleted altogether
    jref=''
    ji=0

    for j in range(len(tday2)):
        if len(tday2[j][1])>0:
            for appt in tday2[j][1]:
                if (appt[4]-datetime.now()).days <= n and (appt[4]-datetime.now()).days>0:
                    # if appointment is within the next n days
                    jref=appt[1]
                    for i in range(len(tjobs)):
                        if appt[1] == tjobs[i][0]:
                            ji=i
                            break
                    # so now we have the job ref, construct the folder names
                    froot = tjobs[ji][1] # just the customer name, simples
                    fsite = tjobs[ji][2]+" "+ tjobs[ji][19]
                    # site name & postcode - the decision around this is
                    # made in datachew() function
                    fjref = tday2[j][0].strftime('%Y-%m-%d')+" "+jref
                    # date is YYYY-MM-DD so that folders sort better on
                    # onedrive
                    feng  = appt[0]
                    frep = 0 # flag to show if appointment is
                             # reportable (for job reports task)
                    if appt[7] in aos:
                        fstat=1
                        # tjobs[ji][11] - is -1 if job complete, or
                        # +ve no of days until next appt
                        if jref not in jobsup:
                            # if completed then make sure job is in jobsup list
                            # also only if actual appointment was within n days
                            jobsup.append(jref)
                            mdlinktext="["+jref+" Site Photos]"+"(https://michaelwilsonmaintenance.sharepoint.com/sites/Photos/Shared%20Documents/Forms/AllItems.aspx?id=%2Fsites%2FPhotos%2FShared%20Documents%2F"+froot.replace(" ","%20")+"%2F"+fsite.replace(" ","%20")+")\n"
                            photolinks.append([jref,markdown.markdown(mdlinktext)])
                    elif appt[7] in aws:# or if it's cancelled, declined, etc.
                        fstat=-1
                    else:
                        fstat=0 # dunno what to do if it's zero
                    # fflag is 1 if it's a future appointment, relative to parameter c
        bar.next()
    bar.finish()
    return [jobsup,photolinks]

def photofolders(n,c):
    # this is the function that processes through the photo folders,
    # creating and sometimes deleting what's there.  It will only
    # delete empty folders, and only then if they're not going to be
    # needed
    global tday2
    global tjobs
    global acs
    global aws
    global root
    global photosfolder
    global dryrun
    global photosdo

    # n is the number of days to look back, in terms of deleting empty folders
    # c is the number of days to look back for creation, e.g. if hasn't been run for 2 days,
    # then historic folders may need creating, if we're behind for whatever reason
    
    # not in use yet
    # to be rewritten to process photo folders using the tjobs/tday2 lists
    # function tasks
    # Identify any jobs that have had appointments within the past n days, and any upcoming for next 7 days
    # Create empty folders for upcoming appointments, in the structure:
    #  -- Customer name
    #     -- Site name (or company site name - which ever is populated)
    #        -- YYYY-MM-DD MW54321
    #           -- Engineer name

    #tdays=[] # turnover daily data
    #        = [ date, [ [engineer name, job ref, notes, recommendations] ], [ callouts £, contract £,
    #            subcontract £, truck £, total £ ] ]
    #        (leave door open for variety of cost types to split into)
    #        (costs[] format to confirm...)
    
    # filter out those appointments that need attention
    # remember **anything** over the past n days needs looking at, since may be renaming, deleting, etc.

    os.chdir(os.path.join(root,photosfolder))
    pfolders=[]
    jobsup=[] # list of job refs with appointments marked as completed within the timeframe
    photolinks=[]
    bar=Bar(padbar('Find appts. from '+str(n)+" days"), max=len(tday2))
    # for each appointment, just need: Customer name, site name,
    # folder name, engineer name, past/future flag then can sort list
    # in folder names order, and hopefully improve the order/way the
    # checking is done e.g. easier to possibly identify if a
    # particular appointment folder can be deleted altogether
    jref=''
    ji=0

    # consider calling photofoldertree(root,0) for every folder we're working in?
    
    for j in range(len(tday2)):
        if len(tday2[j][1])>0:
            for appt in tday2[j][1]:
                if (datetime.now()-appt[6]).days <= n:
                    # if has been changed at all in past n days, then we need to check it
                    jref=appt[1]
                    for i in range(len(tjobs)):
                        if appt[1] == tjobs[i][0]:
                            ji=i
                            break
                    # so now we have the job ref, construct the folder names
                    froot = tjobs[ji][1] # just the customer name, simples
                    fsite = tjobs[ji][2]+" "+ tjobs[ji][19]
                    # site name & postcode - the decision around this is
                    # made in datachew() function
                    fjref = tday2[j][0].strftime('%Y-%m-%d')+" "+jref
                    # date is YYYY-MM-DD so that folders sort better on
                    # onedrive
                    feng  = appt[0]
                    frep = 0 # flag to show if appointment is
                             # reportable (for job reports task)
                    if appt[7] in acs: # if appointment is live
                        fstat=1
                        # tjobs[ji][11] - is -1 if job complete, or
                        # +ve no of days until next appt
                        if appt[7] == 'Completed' and jref not in jobsup and (datetime.now().date()-tday2[j][0]).days <= n:
                            # if completed then make sure job is in jobsup list
                            # also only if actual appointment was within n days
                            jobsup.append(jref)
                            mdlinktext="["+jref+" Site Photos]"+"(https://michaelwilsonmaintenance.sharepoint.com/sites/Photos/Shared%20Documents/Forms/AllItems.aspx?id=%2Fsites%2FPhotos%2FShared%20Documents%2F"+froot.replace(" ","%20")+"%2F"+fsite.replace(" ","%20")+")\n"
                            photolinks.append([jref,markdown.markdown(mdlinktext)])
                    elif appt[7] in aws:# or if it's cancelled, declined, etc.
                        fstat=-1
                    else:
                        fstat=0 # dunno what to do if it's zero
                    # fflag is 1 if it's a future appointment, relative to parameter c
                    if (tday2[j][0]-datetime.now().date()).days>=-c:
                        fflag=1
                    else:
                        # fflag 0 means it's historic
                        fflag=0

                    if froot != '' and fsite != '':
                        # pfolders just has structure [folder, flag,
                        # [eng,status]] we're not going down the road of
                        # deleting appointment folders, just the engineer
                        # folders, if empty, etc.
                        fder=os.path.join(froot,fsite,fjref)
                        f=-1
                        if len(pfolders)>0:
                            for i in range(len(pfolders)):
                                if fjref == pfolders[i][0][len(pfolders[i][0])-18:len(pfolders[i][0])]:
                                    f=i
                                    break
                        if f == -1:
                            pfolders.append([fder.strip(),fflag,[[feng,fstat]]])
                        else:
                            pfolders[f][2].append([feng,fstat])
        bar.next()
    bar.finish()

    if photosdo == 1:
        log(cl.hl1("Working through photo folder changes"))
        # so now we sort pfolders
        pfolders.sort()

        bar=Bar(padbar('Processing photo folders...'),max=len(pfolders))
        for visit in pfolders:
            # pfolders just has structure [folder, flag, [eng,status]]
            # folder is full path
            # flag is 1 for future, 0 for historic
            # status is 1 for live/completed, -1 for cancelled/abandoned

            es=len(visit[2]) # number of engineers listed
            # various things to check/do
            # 1. Does the folder visit[0] exist?
            #    - If not, then are there at least some live engineer visits?
            #        - Then create visit[0]
            created=0
            there=1
            if not os.path.exists(visit[0]):
                there=0
                lv=0
                for e in visit[2]:
                    if e[1] == 1:
                        lv+=1
                        break
                if lv>0:
                    #print(visit[0])
                    log(cl.good("Creating")+" folder '"+visit[0]+"'")
                    if dryrun == 0:
                        created=1
                        # makedirs function creates everything, not just the end folder
                        try:
                            os.makedirs(visit[0])
                        except:
                            created=0

            # 2. List what folders are actually already in visit[0]
            #    - Are there some for engineers not listed in visit[2]?
            #        - If yes, and if they're empty, then delete them
            #    - What about listed in visit[2] but not on disk?
            #        - Is it a 'future' appointment?
            #            - Then create those missing folders, if the status is 1
            #    - And if it is 'future', then remove any empty folders which also have a -1 status
            infolder=[]
            delfolder=[]
            if created == 1 or there == 1:
                for entry in os.scandir(os.path.join(os.getcwd(),visit[0].strip())):
                    if entry.is_dir():
                        matc=0
                        infolder.append(entry.name)
                        for eng in visit[2]:
                            # find if there's an appointment in eworks for which there isn't a folder on disk
                            if eng[0] == str(entry.name):
                                matc=eng[1]
                                break
                        if matc == 0 or (matc == -1 and visit[1] == 1):
                            # if nothing was found, or if what was found was a
                            # cancelled appt folder for a future appointment
                            if len(os.listdir(os.path.join(visit[0],entry.name))) == 0:
                                # if the folder is empty
                                log(cl.poor("Removing ")+"folder '"+str(os.path.join(visit[0],entry.name))+"', since it's empty")
                                delfolder.append(entry.name)
                                if dryrun == 0:
                                    try: 
                                        os.rmdir(os.path.join(visit[0],entry.name))
                                    except:
                                        pass
            for eng in visit[2]:
                if eng[0] not in infolder:
                    # if appt on eworks but no folder on disk
                    if visit[1] == 1 and eng[1] == 1: # if it's a live 'future' appointment
                        log(cl.good("Creating ")+"folder '"+os.path.join(visit[0],eng[0])+"'")
                        if dryrun == 0:
                            try:
                                os.mkdir(os.path.join(visit[0],eng[0]))
                            except:
                                pass

            # 3. Finally, are we left with an empty visit[0] folder?
            #    - Then delete it (contradicting what I said earlier)
            if len(os.listdir(visit[0])) == 0:
                log(cl.poor("Removing ")+"folder '"+str(visit[0])+"', since empty")
                if dryrun == 0:
                    # note that os.rmdir won't remove a non-empty folder anyway
                    try:
                        # if there are files in the folder, then it won't
                        # be empty so will throw out an error
                        os.rmdir(visit[0])
                    except:
                        pass
            bar.next()

        bar.finish()

    return [jobsup,photolinks]

def log(text):
    global logs
    global logtime
    secs=str(int((datetime.now()-logtime).total_seconds()))
    #secs+=(4-len(secs))*" "
    #logs.append("\n"+cl.avg(secs)+"s: --> "+text)
    logs.append("--> "+text)

def reportdates(rtype,offset): # 0-week/1-month, offset 0-current,-1-last,1-next,etc.
    # just a function to generate and return lists of the various dates used for
    # reports
    # all results returned in datetime.date() format

    # rtype = 0 for week, 1 for month
    # offset is 0 for the e.g. week with today in it, or -2 for 2 weeks earlier, for example
    # function returns a list of .date() format dates
    if rtype == 1:
        # if month, get first day of month
        firstday=(datetime.now().replace(day=15)+timedelta(days=offset*31)).replace(day=1)
        endday=(firstday+timedelta(days=31)).replace(day=1)-timedelta(days=1)
    else:
        firstday=(datetime.now()-timedelta(days=datetime.now().weekday()))+timedelta(days=7*offset)
        endday=firstday+timedelta(days=6)
        
    out=[]
    day=firstday
    while (endday-day).days >=0:
        out.append(day.date())
        day+=timedelta(days=1)
    return out

def monthtable(offst,offen):
    # generate the monthly tables, just pass the dates of the months we're looking at
    # [[label 1, start 1, end 1], [label 2, start 2, end 2], etc. ]
    global tday2
    global emailsum
    #global tjobs
    #global tquot
    # does everything, includes the headers & structure of the table
    # returns the list of lists, to then be passed through tabulate etc.

    # headers for month table format:
    #   label, callouts #, contract $, subc $, truck $, $ orders received,
    #   total turnover, var to target
    # doesn't produce a summary line at bottom

    # is set up so it doesn't have to be months - could use this for weeks, for instance
    out = [["Month","# Q",'$ Q','# O', '$ O', "Callouts","Contract","Subc.","Truck","Total"]]
    out[0]=headerify(out[0])

    mdates=[]
    i=offst
    mdates=reportdates(1,i)
    stdate = mdates[0]
    # find the starting date in tday2
    day=0
    here=-1
    for j in range(len(tday2)):
        if (tday2[j][0]-stdate).days == 0:
            here=j
            break
    # gather all the figures together
    while i<=offen:
        line=[mdates[0].strftime('%b %y'),0,0,0,0,0,0,0,0,0,0] # starting date
        for d in mdates:
            line[1] += tday2[here+day][2][6] # # quotes submitted
            line[2] += tday2[here+day][2][7] # $ quotes submitted
            line[3] += tday2[here+day][2][9] # # orders received
            line[4] += tday2[here+day][2][10] # $ orders received
            line[5] += tday2[here+day][2][0] # callouts
            line[6] += tday2[here+day][2][1] # contracts
            line[7] += tday2[here+day][2][2] # subc.
            line[8] += tday2[here+day][2][3] # truck
            line[9] += tday2[here+day][2][4] # total
            day+=1
        out.append([line[0],num(line[1]),cash(line[2]),num(line[3]),cash(line[4]),cash(line[5]),cash(line[6]),cash(line[7]),cash(line[8]),cash(line[9])])
        if -1<=i and i<=1:
            emailsum[1][i+1]=line[9] # monthly total
        i+=1
        mdates=reportdates(1,i)
    return barme2(out,9,0)

def weektable(offst,offen):
    # similarly, generates the weekly table
    # offst = starting week, relative to this week, e.g. -2 is week before last
    # offen = ending week, e.g. 3 is 3 weeks from this week
    global tday2
    global emailsum
    #    global tjobs
    #    global tquot
    # headers for week table format
    #   w/c date, surveys #, callouts $, contract $, subc $, truck $, total turnover, var to tgt,
    #   comparison
    # where comparison is a graphical measure showing the total turnover levels per week
    # Adds a summary total section at bottom

    # tdays [ callouts £, contract £, subcontract £, truck £, total £, # surveys, # quotes, $ quotes, # recalls, # orders, $ orders ] ]
    
    out = [["w/c","# S","# R","# Q",'$ Q','# O', '$ O', "Callouts","Contract","Subc.","Truck","Total"]]
    out[0]=headerify(out[0])

    weekdates=[]
    i=offst
    wdates=reportdates(0,i)
    stdate = wdates[0]
    # find the starting date in tday2
    day=0
    here=-1
    for j in range(len(tday2)):
        if (tday2[j][0]-stdate).days == 0:
            here=j
            break
    # gather all the figures together
    while i<=offen:
        line=[wdates[0].strftime('%d %b'),0,0,0,0,0,0,0,0,0,0,0,0]
        for d in wdates:

            line[1] += tday2[here+day][2][5] # # surveys
            line[2] += tday2[here+day][2][8] # # recalls
            line[3] += tday2[here+day][2][6] # # quotes submitted
            line[4] += tday2[here+day][2][7] # $ quotes submitted
            line[5] += tday2[here+day][2][9] # # orders received
            line[6] += tday2[here+day][2][10] # $ orders received
            line[7] += tday2[here+day][2][0] # callouts
            line[8] += tday2[here+day][2][1] # contracts
            line[9] += tday2[here+day][2][2] # subc.
            line[10] += tday2[here+day][2][3] # truck
            line[11] += tday2[here+day][2][4] # total
            day+=1
        out.append([line[0],num(line[1]),num(line[2]),num(line[3]),cash(line[4]),num(line[5]),cash(line[6]),cash(line[7]),cash(line[8]),cash(line[9]),cash(line[10]),cash(line[11])])
        if -1<=i and i<=1:
            emailsum[0][i+1] = line[11]
        i+=1
        wdates=reportdates(0,i)

    days7ago = date.today()+relativedelta(days=-7)
    i=0
    for j in range(len(tday2)):
        if (tday2[j][0]-days7ago).days == 0:
            here=j
            break
    for i in range(7):
        emailsum[2][0]+=tday2[here+i][2][9]
        emailsum[2][1]+=tday2[here+i][2][10]
        emailsum[3][0]+=tday2[here+i][2][6]
        emailsum[3][1]+=tday2[here+i][2][7]
    return barme2(out,11,0)

def emailtable():
    # function to generate a simple table as the body of the email
    # turnover last week, this week, next week
    #          last month, this month, next month
    # value of upcoming work
    # number and value of jobs received in last 7 days
    # number and value of quotes generated in last 7 days
    global emailsum
    global missingcost
    global unasscost
    global ompd
    global truck
    
    table=''
    table+="Turnover:\n"

    tb=[headerify(["w/c","t/o","Month","t/o"])]
    tb.append([reportdates(0,-1)[0].strftime("%d %b"),cash(emailsum[0][0]),reportdates(1,-1)[0].strftime("%b %y"),cash(emailsum[1][0])])
    tb.append([reportdates(0,0)[0].strftime("%d %b"),cash(emailsum[0][1]),reportdates(1,0)[0].strftime("%b %y"),cash(emailsum[1][1])])
    tb.append([reportdates(0,1)[0].strftime("%d %b"),cash(emailsum[0][2]),reportdates(1,1)[0].strftime("%b %y"),cash(emailsum[1][2])])
    table+=tabulate(tb,colalign=("left","right","left","right"),tablefmt="simple")+"\n\n"

    table+="In the pot (unassigned/outstanding): \n--->  "+cl.hl1(cash(missingcost))+"\n\n"
    table+="In the 7 days to yesterday:\n"
    table+="--->  "+cl.hl1(str(num(emailsum[2][0])))+" orders received,\n          worth "+cl.hl1(cash(emailsum[2][1]))+"\n"
    table+="--->  "+cl.hl1(str(num(emailsum[3][0])))+" quotes submitted,\n          worth "+cl.hl1(cash(emailsum[3][1]))+"\n\n"
    table+="Orders received:\n"+recenttable(0,1,0,0,7,0,0)+"\n\n"
    table+="Please view the email attachments for more details\n\n"
    table+="---------------------------------\n"
    table+="Where needed, these reports assume a labour cost of "+cash(ompd)+" per man per day, to estimate remaining time needed on unfinished jobs.\n\n"
    return table
    
def barme(tablist,datacol, barcol,width):
    # takes a table list of the form
    # [ [header list], [row 1], [row 2], etc ]
    # and column numbers datacol and barcol
    # and populates column barcol with bars to show relative size of elements in datacol
    h=len(tablist) # height of table
    data=[]
    bars=[]
    dmax=0
    dmin=1000000000
    for i in range(h-1):
        try:
            data.append(int(''.join(filter(lambda x: x.isdigit(), tablist[i+1][datacol]))))
        except:
            data.append(0)
        if data[-1]>dmax:
            dmax=data[-1]
        if data[-1]<dmin:
            dmin=data[-1]
    
    for i in range(h-1):
        rat = (data[i]-dmin)/(dmax-dmin)
        bar="#"*round(round(width)*data[i]/dmax)
        if rat<0.25:
            bars.append(cl.poor(bar))
        elif rat>0.75:
            bars.append(cl.good(bar))
        else:
            bars.append(cl.avg(bar))
        tablist[i+1][barcol]=bars[-1]
    return tablist
def barme2(tablist,datacol, hlcol):
    # takes a table list of the form
    # [ [header list], [row 1], [row 2], etc ]
    # and column numbers datacol and barcol
    # and highlights column hlcol accordingly

    h=len(tablist) # height of table
    data=[]
    bars=[]
    datsort=[]
    for i in range(h-1):
        #print(tablist[i+1][datacol])
        try:
            data.append(int(''.join(filter(lambda x: x.isdigit(), tablist[i+1][datacol]))))
            datsort.append(int(''.join(filter(lambda x: x.isdigit(), tablist[i+1][datacol]))))
        except:
            data.append(0)
            datsort.append(0)

    datsort.sort()
    l=len(data)
    red=int(l/3)
    gre=int(2*l/3)
    lr=datsort[red-1]
    lg=datsort[gre-1]

    for i in range(h-1):
        bar=tablist[i+1][hlcol]
        if data[i]<lr:
            bars.append(cl.poor(bar))
        elif data[i]>lg:
            bars.append(cl.good(bar))
        else:
            bars.append(cl.avg(bar))
        tablist[i+1][hlcol]=bars[-1]
    return tablist

def dailytable(st,fn,detailed):
    # generates a daily table between st and fn dates, inclusive,
    # including a totals line at the end

    # table format:
    #   date (short format, naming some days (weekend?))
    #   callout $, contr $, subc $, $ truck jobs, turnover $, num jobs attended, error margin
    # Adds a summary totals row at bottom
    # Also summarises potential variation from the way multi-day job costs are estimated
    global tquot
    global tjobs
    global tday2
    global jas

    if detailed == 1:
        out=[["Date", "C'outs", "Contract", "Sub'd", "Truck", "Total", "Detail - multi-day jobs, plus totals for others, with refs"]]
    else:
        out=[["Date", "C'outs", "Contract", "Sub'd", "Truck", "Total", "Number of jobs & totals"]]
    out[0] = headerify(out[0])

    for j in range(len(tday2)):
        if (tday2[j][0]-st).days == 0:
            here=j
            break

    nd=(fn-st).days +1
    d=0
    calls=0
    ctrs=0
    tots=0
    trucks=0
    while d<nd:
        line=[]
        dday = tday2[here+d][0]
        line.append(dday.strftime('%a %d')) # date
        line.append(cash(tday2[here+d][2][0]))
        calls+=tday2[here+d][2][0]
        line.append(cash(tday2[here+d][2][1]))
        ctrs+=tday2[here+d][2][1]
        line.append(cash(tday2[here+d][2][2]))
        line.append(cash(tday2[here+d][2][3]))
        trucks+=tday2[here+d][2][3]
        line.append(cash(tday2[here+d][2][4]))
        tots+=tday2[here+d][2][4]

        refs=[]
        appcount=[] # ref, no appts, cost, cpa, total appts, cust:site, flag
        # construct the detail line(s)
        for app in tday2[here+d][1]:
            if app[1] not in refs:
                refs.append(app[1])
                appcount.append([app[1],0,0,0,0,'','',''])
                if app[0] not in truck:
                    appcount[-1][1]+=1
                for job in tjobs:
                    if job[0] == app[1] and job[18] not in jas:
                        appcount[-1][2] = job[22][3] # total cost
                        appcount[-1][3] = job[22][6] # cpa
                        if job[22][6]>0:
                            appcount[-1][4] = job[22][3] / job[22][6]
                        else:
                            appcount[-1][4] = job[22][5] # total num appts
                        try:
                            tt=job[12][0]
                        except:
                            tt='?'
                        appcount[-1][5] = (":"+tt+"~"+job[22][2][0:16]).ljust(19)
                        if job[22][8] == 1:
                            appcount[-1][6] = cl.poor("! ")
                        else:
                            appcount[-1][6] = "- "
                        appcount[-1][7] = str(job[12])[0:5]+". " # job type
                            
                        #appcount[-1][6] = str(job[22][8]*"(!) ")
                        break
            else:
                fd=-1
                for j in range(len(appcount)):
                    if appcount[j][0] == app[1] and app[0] not in truck:
                        appcount[j][1]+=1
                        break
        if detailed == 1:
            lastline=cl.hl1("<<< Jobs for "+dday.strftime('%a')+" >>>")+"\n"
        else:
            lastline=''

        surveys=0
        contracts=[0,0,[]] # [       ditto       ]
        ab=0
        for apps in appcount:
            #if apps[6] == "!! ":
            if apps[3]>0 and apps[1]<apps[4] and detailed == 1:
                # if job has a cost, and if only part of it is covered today
                lastline+=apps[6]+apps[0]+apps[5]+" - "+(cash(apps[1]*apps[3])+"/"+cash(apps[2])).ljust(15)
                if ab==0:
                    lastline+="# "
                    ab=1
                else:
                    lastline+="\n"
                    ab=0
            else:
                if apps[3] == 0:
                    surveys+=1
                else:
                    contracts[0]+=1
                    contracts[1]+=apps[1]*apps[3]
                    contracts[2].append([apps[0],apps[7],apps[1]*apps[3]]) # ref, type, cost
        if ab==1:
            lastline+="\n"
        if surveys>0:
            lastline+="> "+str(num(surveys))+" surveys/recalls, "
        else:
            lastline+="> "
        if contracts[0]>0:
            if detailed == 1:
                lastline+="\n"
                conlines = int(contracts[0]/4+1)
                j=0
                i=0
                while i+(j*4)<contracts[0]:
                    if i==0:
                        lastline+="> "
                    nextbit=contracts[2][i+(j*4)][0]+" ("+contracts[2][i+(j*4)][1][0]+": "+cash(contracts[2][i+(j*4)][2])+"), "
                    if contracts[2][i+(j*4)][1] == "React. " and contracts[2][i+(j*4)][2]>150:
                        nextbit=cl.avg(nextbit)
                    lastline+=nextbit
                    if i==3:
                        i=0
                        j+=1
                        lastline+="\n"
                    else:
                        i+=1
            else:
                lastline+=str(contracts[0])+" paid jobs\n"
        else:
            lastline+="\n"
                
        #if contracts[0]>0:
        #    lastline+=str(num(contracts[0]))+" job(s) at "+cash(contracts[1])
        #    if detailed==1:
        #        lastline+=" ("+", ".join(contracts[2])+")"
        lastline+="\n"

        # add count of number & value of other jobs attended per day - surveys, callouts and contract, not including those listed individually
        # also keep running totals to use at end of table
        
        nj = len(refs) # number of jobs attended
        #line.append("")
        line.append(lastline)

        # tjobs[j][22]=[tjobs[j][0],tjobs[j][1],tjobs[j][2],tjobs[j][3],lab,tjobs[j][4],cpa,abs(left)]
        # ref, cust, site, cost, labour, total appts, cpa, left
        
        # get the comparison figure - for each estimated job cost, this is the difference between
        # turnover figure given and the basic cost/appts figure
        
        out.append(line)
        d+=1
    #out=barme(out,5,6,20)
    out.append(headerify(["Totals",cash(calls),cash(ctrs),"",cash(trucks),cash(tots),""]))
    return tabulate(out,headers="firstrow",tablefmt="presto",colalign=("center","center","center","center","center","center","left"))+"\n"
    
def turntablehtml(st,fn):
    # copy of the dailytable function, to be adjusted to better suit
    # putting the older style turnover report together.  Should have
    # columns for callouts, contract, sub'd, truck and total, with
    # total genuinely being the sum of those columns.  The job ref
    # detail should a) be colour coded according to which column(s)
    # they contribute to, and b) show appointment numbers as well as
    # cash value proportions

    # remember tjobs[??][24] contains a list of all appointment dates for this job
    
    # generates a daily table between st and fn dates, inclusive,
    # including a totals line at the end

    # table format:
    #   date (short format, naming some days (weekend?))
    #   callout $, contr $, subc $, $ truck jobs, turnover $, num jobs attended, error margin
    # Adds a summary totals row at bottom
    # Also summarises potential variation from the way multi-day job costs are estimated
    global tquot
    global tjobs
    global tday2
    global jas
    global jcs

    out=[["Date", "C/o", "Cont.", "Sub", "37m", "Total", "Detail - ref, apps/total, cost for day."]]
    out[0]=headerify(out[0])

    for j in range(len(tday2)):
        if (tday2[j][0]-st).days == 0:
            here=j
            break

    nd=(fn-st).days +1
    d=0
    calls=0
    ctrs=0
    tots=0
    trucks=0
    csvout=''
    while d<nd:
        line=[]
        csvout+=tday2[here+d][0].strftime("%d %b, ")

        dday = tday2[here+d][0]
        line.append(dday.strftime('%a\n%d %b')) # date
        line.append(cash(tday2[here+d][2][0]))
        csvout+=str(num(tday2[here+d][2][0]))+", "
        calls+=tday2[here+d][2][0]
        line.append(cash(tday2[here+d][2][1]-tday2[here+d][2][2]))
        csvout+=str(num(tday2[here+d][2][1]))+", "
        ctrs+=tday2[here+d][2][1]-tday2[here+d][2][2]
        line.append(cash(tday2[here+d][2][2]))
        csvout+=str(num(tday2[here+d][2][2]))+", "
        line.append(cash(tday2[here+d][2][3]))
        csvout+=str(num(tday2[here+d][2][3]))+", "
        trucks+=tday2[here+d][2][3]
        line.append(cash(tday2[here+d][2][4]))
        tots+=tday2[here+d][2][4]


        refs=[]
        appcount=[] # ref, no appts, cost, cpa, total appts, cust:site, flag
        engcheck=['Subcontractor','37m EN68 OPS']
        # construct the detail line(s)
        for app in tday2[here+d][1]:
            # work through the appointments listed for the day
            if app[0] in engcheck:
                tocheck=1
            else:
                tocheck=0
            if app[1] not in refs:
                csvout+=app[1]+", "
                refs.append(app[1])
                appcount.append([app[1],0,0,0,0,'','','',tocheck,[]])
                if app[0] not in truck:
                    appcount[-1][1]+=1
                for job in tjobs:
                    if job[0] == app[1] and job[18] not in jas:
                        if job[18] in jcs:
                            # if authorised or invoiced then don't need to check
                            appcount[-1][8]=0
                        appcount[-1][2] = job[22][3] # total cost
                        appcount[-1][3] = job[22][6] # cpa
                        if job[22][6]>0:
                            appcount[-1][4] = job[22][3] / job[22][6]
                        else:
                            appcount[-1][4] = job[22][5] # total num appts
                        appcount[-1][5] = job[1][0:6]+":"+job[2][0:12]
                        if job[22][8] == 1:  # whether appt count guessed or not
                            appcount[-1][6] = 1
                        else:
                            appcount[-1][6] = 0
                        appcount[-1][7] = str(job[12])[0:5]+". " # job type
                            
                        #appcount[-1][6] = str(job[22][8]*"(!) ")
                        appcount[-1][9]=job[24] # appointment list for the job
                        break
            else:
                fd=-1
                for j in range(len(appcount)):
                    if appcount[j][0] == app[1] and app[0] not in truck:
                        appcount[j][1]+=1
                        if tocheck==1:
                            appcount[j][8]=1
                        break
        lastline=''
        ll=['','']
        actll=''
        numc=0

        csvout+="\n"

        surveys=0
        contracts=[0,0,[]] # [       ditto       ]
        ab=0
        for apps in appcount:
            if apps[3] == 0:
                surveys+=1
            else:
                contracts[0]+=1
                contracts[1]+=apps[1]*apps[3]
                contracts[2].append([apps[0],apps[7],apps[1]*apps[3],apps[0][2:7]+" ",apps[6],apps[1],apps[4],apps[8],apps[9],apps[5],apps[2]]) # ref, type, cost

        nplin=3
        if contracts[0]>0:
            # alter this so it generates separate lines for 'standard'
            # jobs and those requiring checking
            
            #lastline+="\n"
            #conlines = int(contracts[0]/nplin+1)
            cc=0
            k=[0,0]
            l=[0,0]
            j=0
            i=0
            firstbit=["-  ","?! "]
            numc=0
            while cc<contracts[0]:
                # [4] is 1 if it's subd or truck appt
                # [7] is 1 if the appt number has been estimated based on labour cost
                if contracts[2][cc][4]==1 or contracts[2][cc][7]==1: # if to check
                    tc=1
                else:
                    tc=0
                    
                # add the necessary line feeds depending on where we are
                if l[tc]==0 and k[tc] == 0:
                    ll[tc]+="\n"
                if k[tc] == 0:
                    if l[tc]>0:
                        ll[tc]+="\n"
                    if tc == 0:
                        ll[tc]+=firstbit[tc]
                if tc==0:
                    endless=contracts[2][cc][3]+str(contracts[2][cc][5])+"/"+str(round(contracts[2][cc][6]))
                    nextbit=endless.ljust(11)+cash(contracts[2][cc][2])+", "
                    nextbit=nextbit.ljust(20)
                else:
                    # this is where we construct different detail for
                    # jobs that need checking

                    # ref:dailycost day a of b, c apps from d,
                    # dailycost of total ('estimated' or 'subd/truck')
                    numc+=1
                    endless=firstbit[tc]+contracts[2][cc][3]+(str(contracts[2][cc][5])+"/"+str(round(contracts[2][cc][6]))).ljust(4)
                    e1=''
                    e2=''
                    if contracts[2][cc][4] == 1:
                        e1="s/t"
                    if contracts[2][cc][7] == 1:
                        e2="lab"
                    if len(e1)>0 and len(e2)>0:
                        e3=e1+", "+e2
                    else:
                        e3=e1+e2
                    nextbit=endless+" "+(cash(contracts[2][cc][2])+"/"+cash(contracts[2][cc][10])).ljust(14)+(contracts[2][cc][9]+", ").ljust(19)+("("+e3+")").ljust(11)+"|+/-            |\n"
                    #nextbit=nextbit.ljust(20)
                ll[tc]+=nextbit
                
                #lastline+=nextbit
                if k[tc] == nplin-1:
                    k[tc]=0
                    l[tc]+=1
                    #ll[tc]+="\n"
                else:
                    k[tc]+=1
                cc+=1
            if len(ll[0])>3:
                lastline+=ll[0]
            else:
                lastline+=firstbit[0]
            if len(ll[1])>3:
                lastline+=ll[1]
        else:
            lastline+="Quiet day\n"
                
        line.append(lastline)
        ls=lastline.count('-  ')
        #line.append("")
        #line.append("-\n"*ls + "? ->\n"*(max(numc-1,0))+"? ->")

        # tjobs[j][22]=[tjobs[j][0],tjobs[j][1],tjobs[j][2],tjobs[j][3],lab,tjobs[j][4],cpa,abs(left)]
        # ref, cust, site, cost, labour, total appts, cpa, left
        
        out.append(line)
        d+=1
    #out=barme(out,5,6,20)
    out.append(["Totals",cash(calls),cash(ctrs),"",cash(trucks),cash(tots),"",""])
    return [tabulate(out,headers="firstrow",tablefmt="grid",colalign=("center","center","center","center","center","center","left")),csvout]


def recenttable(c,o,q,s,n,sort,fut):
    # generates a table list for recent things:
    #     c,o,q,s are 0 or 1, for orders, quotes and surveys
    #     n is number of days to look back
    #     sort is either
    #       0 for just date sort, newest to oldest
    #       1 to sort by customer & site, then date
    #     (that way if we're looking at a combined table, there's some visibility of
    #      surveys that have generated quotes and/or orders, for instance)
    #     cust is if we want to restrict to just one customer, leave empty otherwise
    #     fut is the number of days ahead to look too
    
    #tjobs=[] # turnover jobs data = [ mwref, customer, site name,
             # cost, total appts, worked appts, # sub'd appts, # truck
             # appts, start date, last date, job age, complete(-1) or
             # days until next appt, job type, email flag, products[],
             # cust ref flag, tags[], po num, status, labour,
             # description, applist] products[] - [code, price]
    #tdays=[] # turnover daily data = [ date, [ [engineer name, job
             # ref, notes, recommendations] ], [ callouts £, contract
             # £, subcontract £, truck £, total £ ] ] (leave door open
             # for variety of cost types to split into) (costs[]
             # format to confirm...)
    #tquot=[] # turnover quotes list = [ mwref, customer, site name,
             # cost, age, email flag, cust ref flag, status ]

    fn=date.today()+relativedelta(days=fut)
    st=date.today()+relativedelta(days=-n)
    # table format
    #   date, ref, value/survey, customer - site (both abbrev.)

    recdata=[]
    # function data lists:
    # [ date, ref, value, customer, site, tags/status ]
    
    # Adds summary row(s) showing total number and value (if appropriate) for each type
    global tjobs
    global tday2
    global tquot
    global jas
    global jcon

    # try to adjust the searching so that it does a double pass, and
    # includes all listed visits/quotes to each site?
    
    # first look through jobs
    for job in tjobs:
        if (job[8].date()-st).days>=0 and (fn-job[8].date()).days>=0 and job[18] not in jas:
            # if it's in the date range and not cancelled etc.
            try:
                tgs = ', '.join(job[16])
            except:
                tgs=''
            if job[3]>0:
                if job[12] in jcon:
                    if o == 1:
                        recdata.append([job[8].date(),job[0],job[3],job[1],job[2],tgs])
                elif c == 1:
                    recdata.append([job[8].date(),job[0],job[3],job[1],job[2],tgs])
            elif s == 1:
                tgs=''
                recdata.append([job[8].date(),job[0],job[3],job[1],job[2],tgs])
    if q == 1:
        for quote in tquot:
            if quote[4]<=n: # within date range and not still Draft
                dt=date.today()+relativedelta(days=-quote[4])
                if quote[7] == -10000:
                    st='Draft'
                elif quote[7] <0:
                    st=cl.poor('Rejected')
                elif quote[7]>0:
                    st=cl.good('Accepted')
                else:
                    st='Waiting'
                recdata.append([dt,quote[0],quote[3],quote[1],quote[2],st])
                
    # all collated now, needs sorting
    # 2 options - sort=0 means just order by date, newest first
    #             sort=1 means sort by customer, then site, then date
    recdata.sort(reverse=False)
    if sort == 1:
        recdata=sorted(recdata, key=lambda x: (x[3], x[4], x[1]))

    # now build the table
    if c+o+q+s==1:
        table=[headerify(["Ref","Cost","Site"])]
    else:
        table=[headerify(["Date","Ref","Cost","Site","Tags/Status"])]
    for record in recdata:
        if record[2] == 0 and len(record[1])>6:
            val="Survey"
        else:
            val=cash(record[2])
        if q == 1:
            if len(record[1])==6:
                r="Qu "+record[1]
            else:
                r="-- "+record[1]
        else:
            r=record[1]
        if c+o+q+s == 1:
            # if only one type wanted, then skip the date and make it skinnier
            table.append([r, val, record[4][0:12]])
        else:
            table.append([record[0].strftime("%d %b"), r, val, record[3][0:12]+" : "+record[4][0:24],record[5]])

    return tabulate(table,headers="firstrow",tablefmt="presto")

def custtable(n,m):
    # n is the number of days to look back
    # m is how many days to look to, default it to 0 (only affects quote searches)
    global tjobs
    global tquot
    global jact
    global jcs
    global jas
    # generates a table between st and fn dates, showing the top n customers for total turnover,
    # as well as other info
    # relies of info generated by jobcost() function

    # Customer
    # Turnover, past 3 months - value and percentage of business
    # Outstanding work, value and percentage
    # Quotes outstanding, value and percentage (submitted in past 6 months)

    # Totals line
    # Order the customers by turnover, largest to smallest, top n

    #tjobs=[] # turnover jobs data = [ mwref, customer, site name,
             # cost, total appts, worked appts, # sub'd appts, # truck
             # appts, start date, last date, job age, complete(-1) or
             # days until next appt, job type, email flag, products[],
             # cust ref flag, tags[], po num, status, labour,
             # description, applist] products[] - [code, price]
    #tdays=[] # turnover daily data = [ date, [ [engineer name, job
             # ref, notes, recommendations] ], [ callouts £, contract
             # £, subcontract £, truck £, total £ ] ] (leave door open
             # for variety of cost types to split into) (costs[]
             # format to confirm...)
    #tquot=[] # turnover quotes list = [ mwref, customer, site name,
             # cost, age, email flag, cust ref flag, status ]

    #tjobs[j][22]=[tjobs[j][0],tjobs[j][1],tjobs[j][2],tjobs[j][3],lab,tjobs[j][4],cpa,abs(left),guessed]
    # ref, cust, site, cost, labour, total appts, cpa, left, guess flag

    justcusts=[]
    custs=[]
    # list of lists of format [customer, turnover $, turnover %, outstanding $, outstanding %,
    #                          quotes $, quotes %, totperc, [quots: acc, waiting, rej], [dec times]
    for job in tjobs:
        if job[1] in justcusts:
            fd=justcusts.index(job[1])
        else:
            justcusts.append(job[1])
            custs.append([job[1],0,0,0,0,0,0,0,[0,0,0],[]])
            fd=-1
        if job[18] in jact: #if it's ongoing
            custs[fd][3]+=job[22][7] # add remaining cost
            custs[fd][1]+=(job[22][3]-job[22][7]) # add completed part to turnover total
        elif job[18] in jcs and (date.today()-job[8].date()).days <=n:
            # if completed within past 91 days (13 weeks)
            custs[fd][1]+=job[3] # add total cost if completed
    for quote in tquot:
        if quote[4]<=n and quote[4]>=m: 
            # don't include accepted quotes
            if quote[1] in justcusts:
                fd=justcusts.index(quote[1])
            else:
                justcusts.append(quote[1])
                custs.append([quote[1],0,0,0,0,0,0,0,[0,0,0],[]])
                fd=-1
            if quote[7]>0:
                custs[fd][8][0]+=1
                custs[fd][9].append(quote[7]) # decision time
            elif quote[7]<0:
                custs[fd][5]+=quote[3] # add value of quote
                custs[fd][8][2]+=1
                custs[fd][9].append(-quote[7])
            else:
                custs[fd][5]+=quote[3] # add value of quote
                custs[fd][8][1]+=1
                
    # now get the totals for all customer
    totturn=0
    totout=0
    totquot=0
    totacc=0
    totwait=0
    totrej=0
    for cust in custs:
        if cust[5]>0:
            totturn+=cust[1]
            totout+=cust[3]
            totquot+=cust[5]
            totacc+=cust[8][0]
            totwait+=cust[8][1]
            totrej+=cust[8][2]
            if len(cust[9])>0:
                avg=sum(cust[9])/len(cust[9])
                cust[9].append(avg)
            else:
                cust[9].append(0)

    totrate=str(round(100*totacc/(totacc+totwait+totrej),1))+"%"
    # now work out the percentages
    table=[]
    head=["Customer","Turnover","Upcoming","Quoted","Quotes acc/wait/rej","Impact %","Conversion"]
    head=headerify(head)
    for j in range(len(custs)):
        custs[j][2]=custs[j][1]/totturn
        custs[j][4]=custs[j][3]/totout
        custs[j][6]=custs[j][5]/totquot
        custs[j][7] = (custs[j][1]+custs[j][3])/(totturn+totout)

    custs.sort(key=lambda x: x[0])
    table2=[head]
    for cust in custs:
        if cust[5]>0: # only show customers who've had some quotes
            rate=str(round(100*cust[8][0]/(cust[8][0]+cust[8][1]+cust[8][2]),1))+"%"
            table2.append([cust[0][0:24], cash(cust[1]), cash(cust[3]), cash(cust[5]), "< "+str(num(cust[8][0])).ljust(3)+" : "+str(num(cust[8][1])).ljust(3)+" : "+str(num(cust[8][2])).ljust(3)+">", percent(cust[7]), rate])

    #table2=barme(table2,5,5,14)
    tail=headerify(["Total figures",cash(totturn),cash(totout),cash(totquot),"<  "+str(num(totacc)).ljust(3)+" : "+str(num(totwait)).ljust(3)+" : "+str(num(totrej)).ljust(3)+"  >","-",totrate])
    table2=barme2(table2,5,0)
    table2=barme2(table2,6,4)
    table2.append([])
    table2.append(tail)

    return "\nQuote figures and conversion rates:\n(only includes figures from jobs/quotes started within the past "+str(round(n/7))+" weeks)\n"+tabulate(table2,headers="firstrow",tablefmt="pretty",colalign=("left","right","right","right"))

# We'll still email, but, at least in this script, (gradually) switch over
# to terminal output, including ANSI color sequences
# Then use 'ansi2html -c -w -l' to convert to html

# the following are all to do with formatting the output
def cash(num):
    # not directly dependant on the markup processor used, for now
    if num>0:
        out="${:,.0f}".format(num)
    elif num<0:
        out="("+"${:,.0f}".format(num)+")"
    else:
        out="-"
    return out    
def percent(num):
    if num>0:
        out=str(round(num*100))+"%"
    else:
        out="-"
    return out    
    
def num(n):
    m=round(n)
    if m == 0:
        out='-'
    else:
        out=m
    return out
def keywords(ref):
    global tjobs
    # to do.  starting list of stuff to look for sika, slate(s),
    # tile(s), felt, point(int), gutter(s)(ing), tower / lift,
    # scaffold, picker, truck, 37m, 57m, ?m?d, ?  men, ? days

    # takes the prep'd tjobs list, and the job ref specified, and returns a list of keywords
    wordlist=['sika','gutter','guttering','gutters','tower','scaffold','57m','truck','picker','37m',
              'tile','tiles','slate','slates','felt','point','pointing','brick','plaster', 'plastering',
              'void','voids','ooh','access']

    f=-1
    for j in range(len(tjobs)):
        if tjobs[j][0] == ref:
            f=j
            break
        
    if f>=0:
        taglist=[]
        for t in tjobs[j][16]:
            taglist.append(t.lower().strip())
        desc=tjobs[j][23].lower()
        for w in wordlist:
            if w.strip() in desc and w.strip() not in taglist:
                taglist.append(w.strip())
    return taglist
def concernedjobs(concerns):
    global planweeks
    # concerns list has following format
    # [ ref, cust, site, desc., age, cost, labour, # appts (estimated from labour), # appts planned, appts worked, [dates] ]
    # function to generate output per job, summarising where we are in terms of planning
    # [dates] is just a list of [date() format, name]
    # probably more parameters to add, once have better idea of printed page
    # width and height in printed characters
    output=[]
    actual=[]
    jdline=[] # job detail lines
    thelot=''
    bar = Bar(padbar('Generating job calendars'), max=len(concerns))
    concerns.sort(key=lambda x: x[3], reverse = True)
    for job in concerns:
        jdline=[]
        l=job[0]+": "+job[1][0:16]+" - "+job[2][0:25] # truncate
                                                      # customer and
                                                      # site name

        #2 lines
        jdline.append(cl.hl3("~"*55))
        jdline.append(cl.hl2(l))
        # 1 line
        jdline.append("Age: "+cl.poor(str(job[3]))+" days, cost: "+cl.good(str(job[4]))+", labour: "+cl.good(str(job[5])))
        # 1 line
        jdline.append(cl.good(str(job[7]))+" appts. planned, "+cl.poor(str(job[6]-job[7]))+" more needed (est.).")
        jdline.append("")
        # leaves up to 3 lines for the description, tags, keywords, etc.
        jdline.append(cl.hl1("Keywords:"))
        tags = ", ".join(keywords(job[0]))
        #jdline.append(tags)
        out=textwrap.wrap(tags,width=55, initial_indent='', subsequent_indent='', expand_tabs=True, replace_whitespace=True, fix_sentence_endings=False, break_long_words=True, drop_whitespace=True, break_on_hyphens=True, tabsize=8, max_lines=None)
        for l in out:
            jdline.append(l)
        
        # cl.tday, cl.appt, cl.blnk

        # get start and end dates for calendar output
        # should be same for every job - approx 6 month timeframe
        startd=date.today()+relativedelta(weeks=-1,weekday=MO)
        # end date around 6 months from now
        endd=datetime.now().date()+relativedelta(weeks=+planweeks,weekday=SU)

        nw=round(((endd-startd).days+1)/7) # number of weeks,
                                           # shouldn't need rounding,
                                           # but anyway

        newweeks=[] # first weeks that are a different month, so that
                    # month name can be displayed
        newmon=[]
        justdates=[] # list of the just the attendance dates

        for a in job[9]:
            justdates.append(a[0])

        weekmatrix=[[],[],[],[],[],[],[],[],[]] # this will just be a
                                                # nwx7 matrix list
                                                # covering the days
                                                # we're looking at
        wdays=['','']
        mline="# "
        wd=0
        mnth=0
        lw=0
        for w in range(nw):
            for sw in range(7):
                wd=sw+(w*7)
                dday = startd+relativedelta(days=+wd)
                if int((dday.strftime('%d'))) == 1:
                    mline+=(w-lw)*"  "
                    mline+=dday.strftime('%b')+" "
                    lw=w+2

        for sw in range(7): # day of week to generate
            # add the day of week to start of the row
            weekmatrix[sw+2].append(['M ','T ','W ','T ','F ','S ','S '][sw])
            for w in range(nw):
                # sw is day of week
                # w is week num
                # so this loop should cover the whole ~6 month range
                # then sw+w*7 is the offset to look at
                wd=sw+(w*7)
                dday = startd+relativedelta(days=+wd)

                if dday in justdates:
                    # there's something scheduled on this date
                    if (dday-date.today()).days == 0:
                        # different colour if today
                        weekmatrix[sw+2].append(cl.tday(dday.strftime('%d')))
                    else:
                        weekmatrix[sw+2].append(cl.appt(dday.strftime('%d')))
                elif (dday-date.today()).days == 0:
                    weekmatrix[sw+2].append(cl.tday('<>'))
                elif int((dday.strftime('%d'))) == 1:
                    # first day of month
                    weekmatrix[sw+2].append(cl.hl1('<>'))
                else:
                    weekmatrix[sw+2].append(cl.blnk('<>'))
            wdays.append('')
            for string in weekmatrix[sw+2]:
                wdays[-1]+=string
        # construct the top line with the month names in it...
        weekmatrix[0].append('  ')
        weekmatrix[1].append('# ')

        for j in range(nw):
            weekmatrix[1][0]+=cl.blnk("--") # improve with date nos some time?

        wdays[0]=mline
        wdays[1]="  "+weekmatrix[1][0]

        for j in range(9):
            try:
                actual.append([jdline[j]])
            except:
                actual.append(['---'])
            actual[-1].append(wdays[j])
        actual.append(['',''])
        bar.next()
    thelot+=tabulate(actual,tablefmt="plain",colalign=("left","left"))+"\n"
    bar.finish()
        
    return thelot

def futureplanner():
    global tjobs
    global planweeks
    global jact
    global jtypes

    # alternative layout, just one line per job, showing ref, site, age, appts needed, and list of weeks
    # tjobs key bits
    # 0 ref, 1 cust, 2 site, 10 age, 3 cost, 20 labour, 22-6 cpa, 24 dates/eng list, 4 appts
    
    # concerns list has following format
    # [ ref, cust, site, desc., age, cost, labour, # appts (estimated from labour), # appts planned, appts worked, [dates] ]
    # function to generate output per job, summarising where we are in terms of planning
    # [dates] is just a list of [date() format, name]
    # probably more parameters to add, once have better idea of printed page
    # width and height in printed characters
    output=[]
    actual=[]
    jdline=[] # job detail lines
    thelot=''
    bar = Bar(padbar('Generating job planner'), max=len(tjobs))
    # get start and end dates for calendar output
    # should be same for every job - approx 6 month timeframe
    startd=date.today()+relativedelta(weeks=-1,weekday=MO)
    # end date around 6 months from now
    endd=datetime.now().date()+relativedelta(weeks=+planweeks,weekday=SU)
    
    nw=round(((endd-startd).days+1)/7) # number of weeks, shouldn't
                                       # need rounding, but anyway

    # construct month line for the date side
    mline='| '
    lw=0
    for w in range(nw):
        for sw in range(7):
            wd=sw+(w*7)
            dday = startd+relativedelta(days=+wd)
            if int((dday.strftime('%d'))) == 1:
                mline+=(w-lw)*"  "
                mline+=cl.hl2(dday.strftime('%b'))+" "
                lw=w+2
    actual=[]
    actual2=[]
    for job in tjobs:
        if job[18] in jact and job[12] in jtypes:
            # unassigned, in proress, appointed, action required, completed
            # include 'Completed' since this is just a temporary status until it's authorised or invoiced
            # jtypes iis contract or callout, just to catch jobs which should have been changed to contract
            tags = keywords(job[0])
            t=''
            if 'sika' in tags:
                t=cl.poor('  sika')
                
            # 2 lines of job detail
            refname = cl.hl1(job[0])+": "+job[1][0:8]+" - "+job[2][0:24] +t
            if job[22][6] >0:
                reqd = str(max(round(job[3]/job[22][6]),0)).rjust(3,' ')
                if int(reqd) == 0:
                    reqd = cl.good(reqd)
                else:
                    reqd = cl.poor(reqd)
            else:
                reqd = "  ?"
            stats = "Age: "+cl.poor(str(job[10]).rjust(3,' '))+", lab: "+str(job[20]).rjust(8,' ')+", sched: "+str(job[4]).rjust(3,' ')+", reqd: "+reqd

            # cl.tday, cl.appt, cl.blnk

            week='| '
            for w in range(nw):
                # w is week num
                # then sw+w*7 is the offset to look at
                fd=w*7
                firstd = startd+relativedelta(days=+fd)
                lastd = firstd+relativedelta(days=+6)
                wc=0 # week count, of appointments...
                dts=[]
                for appt in job[24]:
                    if abs((lastd-appt[0]).days) <=6 and abs((appt[0]-firstd).days) <= 6 and appt[0] not in dts:
                        dts.append(appt[0])
                        wc+=1
                if wc>0:
                    week+=cl.appt(str(wc).rjust(2,' '))
                else:
                    week+=cl.blnk('<>')

            actual.append([job[10],[refname,mline],[stats,week]])
            #actual.append([stats,week])
        bar.next()
    actual.sort(reverse=True)
    for j in actual:
        actual2.append(j[1])
        actual2.append(j[2])
        actual2.append([cl.blnk('~'*50),cl.blnk('~'*50)])

    thelot+=tabulate(actual2,tablefmt="plain",colalign=("left","left"))+"\n"
    bar.finish()
        
    return thelot

def jrheader(ref,cust,site,desc):
    # formats for job report title line
    
    # <<< MW12345 - Customer, My House >>>
    body=ref+" : "+cust+" : "+site
    out="\n\n"+cl.header(body)+"\n"+cl.header("="*len(body))+"\n"
    if len(desc)>0:
        out+=desc+"\n\n"
    return out

def jrdate(start,end, name,total):
    # takes start & finish datetime forms for an appointment, and returns 2 parts,
    # the formatted date, plus the formatted times

    # ~ 15-Sep-76 ~
    # # 09:00 - 17:00
    dt=start.strftime('%a %d/%m/%y')
    st=start.strftime('%H:%M')
    fn=end.strftime('%H:%M')
    tm=(end-start).total_seconds() / 60
    hrs=int(tm/60)
    mns=int(tm-(hrs*60))
    lab=""
    if hrs>0:
        lab=str(hrs)+"hrs, "
    lab+=str(mns)+"mins"
    tot=''
    if total>0:
        hrs=int(total/3600)
        mns=int(total/60-(hrs*60))
        tot="{ Total: "
        if hrs>0:
            tot+=str(hrs)+"hrs, "
        tot+=str(mns)+"mins }"
    if total>=0:
        lab="["+lab+"] "
    else:
        # total<0 means no total time on site printed, for the full list
        lab=''
    
    l=max(20-len(name),0)*" "
    out = cl.hl1(dt+" "+name)+l+" ("+st+"-"+fn+") "+lab+cl.hl4(tot)
    #out=[]
    #out.append(dt)
    #out.append("# "+st+" - "+fn)
    return out

def jreng(text):
    # takes engineer name and formats for job report

    # # Andy Pandy
    out="# "+text
    return out

def jrnotes(text,nwidth):
    # takes job report notes, wraps text as appropriate, and returns in a useable text format
    # currently wraps to at least 60 width, at an indent of 2 spaces
    nw=max(nwidth,60)
    #out='\n'.join(textwrap.wrap(text,width=nw, initial_indent='  ', subsequent_indent='  ', expand_tabs=True, replace_whitespace=True, fix_sentence_endings=False, break_long_words=True, drop_whitespace=True, break_on_hyphens=True, tabsize=8, max_lines=None))
    return text+"\n"

def jrrecs(text,nwidth):
    # takes text of further recommendations, formats appropriately, adds a header, and returns
    nw=max(nwidth,50)
    out=cl.good('Further Recommendations:')+'\n'
    #out+='\n'.join(textwrap.wrap(text,width=nw, initial_indent='    ', subsequent_indent='    ', expand_tabs=True, replace_whitespace=True, fix_sentence_endings=False, break_long_words=True, drop_whitespace=True, break_on_hyphens=True, tabsize=8, max_lines=None))
    return out+text+"\n"
def jrparts(text,nwidth):
    # takes text of further recommendations, formats appropriately, adds a header, and returns
    nw=max(nwidth,50)
    out=cl.good('Parts Needed:')+'\n'
    #out+='\n'.join(textwrap.wrap(text,width=nw, initial_indent='    ', subsequent_indent='    ', expand_tabs=True, replace_whitespace=True, fix_sentence_endings=False, break_long_words=True, drop_whitespace=True, break_on_hyphens=True, tabsize=8, max_lines=None))
    return out+text+"\n"

def ansiout(text):
    # ansi2html -c -w --style 'pre {font-family: Consolas}'
    f=open("/tmp/turnt.txt","w")
    f.write(text)
    f.close()
    converted=subprocess.run(['aha','-w'],input=text,capture_output=True,text=True)
    # manually adjusted stuff to stop lines wrapping when displaying
    # tables in email preview pane
    wrpd=converted.stdout.replace("white-space: pre-wrap","white-space: pre")
    # don't know why, but pound signs seem to be an issue, so manually
    # put in here
    pounded=wrpd.replace("$","&pound")
    return pounded
def ansioutwr(text):
    # ansi2html -c -w --style 'pre {font-family: Consolas}'
    f=open("/tmp/turnt.txt","w")
    f.write(text)
    f.close()
    converted=subprocess.run(['aha','-w'],input=text,capture_output=True,text=True)
    # manually adjusted stuff to stop lines wrapping when displaying
    # tables in email preview pane
    #wrpd=converted.stdout.replace("white-space: pre-wrap","white-space: pre")
    # don't know why, but pound signs seem to be an issue, so manually
    # put in here
    pounded=converted.stdout.replace("$","&pound")
    return pounded

def givesomehelp():
    # prints the help text
    ln=20
    hlp=[]
    hlp.append(["dry","performs dry run - logs created but nothing actually\nchanged/sent"])
    hlp.append(["photos n","updates photos folders, appts starting from n days ago, defaults to 7"])
    hlp.append(["folders","updates job folders"])
    hlp.append(["reports","generate the turnover reports"])
    hlp.append(["tidy","ensures processed reports are removed\non completion"])
    hlp.append(["short","prints number of jobs per day, rather than full list\nof MW refs"])
    hlp.append(["target n","sets £nx1000 as the target turnover for the year.\nDefaults to "+str(tgtpy)])
    hlp.append(["file","scans Eworks folder and files anything with an mw ref\nin the filename"])
    hlp.append(["help","prints this"])
    hlp.append(["phage n","only creates photos folders no older than n days,\ndefaults to 0 if not specified"])
    hlp.append(["guess n","Guess job length from labour cost and 'n' as cost\nper man per day, and estimate cost per day accordingly"])
    hlp.append(["plan n","Generate planning reports, for jobs estimated to take at least n appts."])
    hlp.append(["long n","Whether to plan long jobs, requiring more than n appointments"])
    hlp.append(["tree -loc-","Bulk renames folders to correct date format.  Give a folder."])
    hlp.append(["tree root","Identifies sites in multiple folders. Kindof"])
    hlp.append(["jrep","Whether to email individual job reports"])
    hlp.append(["quotes","Whether to send the separate email re chasing quotes"])
    print(tabulate(hlp,tablefmt="plain"))
    #for hmm in hlp:
    #    print(hmm[0]+" "*(ln-len(hmm[0]))+hmm[1])
    print("\nIf run without any of the photos/folders/reports options, nothing happens...")
    quit() # we don't do owt else if help's been given.

def getoptions(options):
    # pass the options list from commandline, this chews through it
    # returns: dryrun, tidy, appdays, tgtpy, plan, planweeks,
    # longj, guess, ompd, sendto,
    # foldersdo, photosdo, phistory, reports, jrep, test, help
    dryrun=0
    tidy=0
    appdays=1
    foldersdo=0
    photosdo=0
    if 'dry' in options:
        dryrun=1
        log("Performing dry run")
    if 'tidy' in options:
        tidy=1
    if 'phage' in options:
        try:
            appdays=int(options[options.index('age')+1])
        except:
            pass

    # target turnover per year, multiples of £1k
    tgtpy=1222
    if 'target' in options:
        try:
            tgtpy=int(options[options.index('target')+1])
        except:
            pass

    planweeks=20
    plan=0
    if 'plan' in options:
        plan=1
        try:
            planweeks=int(options[options.index('plan')+1])
        except:
            pass

    # long option to display details of current 'long' jobs
    longj=0
    if 'long' in options and 'plan' in options:
        try:
            longj=int(options[options.index('long')+1])
        except:
            longj=4

    # parameter to decide whether turnover calculations guesstimate multi-day costs
    # changed to on by default
    if 'guess' in options:
        guess=1
        try:
            ompd=int(options[options.index('guess')+1])
        except:
            ompd=275
    else:
        guess=1
        ompd=275

    sendto='andy.swallow@michaelwilsonandson.co.uk'
    if 'email' in options:
        try:
            sendto=options[options.index('email')+1]
        except:
            pass

    if 'folders' in options:
        foldersdo=1

    phistory=7
    if 'photos' in options:
        if os.path.ismount(root+photosfolder):
            photosdo=1
        else:
            log("Photos folder creation requested, but Photos folder not mounted")
            quit()
        try:
            phistory=int(options[options.index('photos')+1])
        except:
            pass

    if 'reports' in options:
        reports=1
    else:
        reports=0
    if 'jrep' in options:
        # whether to email separate job reports or not
        jrep=1
    else:
        jrep=0

    test=0
    if 'test' in options:
        # apply test flag.
        # any feature that needs testing, just put in appropriate place in the program, if test==1, and then can control
        # from command line whether it's run or not
        test=1

    chase=0
    if 'quotes' in options:
        chase=1
    hel=0
    if 'help' in options:
        hel = 1
    return [dryrun,tidy,appdays,tgtpy,plan,planweeks,longj,guess,ompd,sendto,foldersdo,photosdo,phistory,reports,jrep,test,hel,chase]


logs=[]
logtime=datetime.now()

bw=20

options=[]
try:
    for o in sys.argv:
        options.append(o.lower())
except:
    pass

[dryrun,tidy,appdays,tgtpy,plan,planweeks,longj,guess,ompd,sendto,foldersdo,photosdo,phistory,reports,jrep,test,hel,chase]=getoptions(options)

if hel == 1:
    givesomehelp()

log("Default age set to "+str(appdays))

#######################################################################################################################
# input file formats - the ht[] lists are used to check the header line of each file, to make sure they're useable
# so must all be spelt correctly, with the correct case
#######################################################################################################################
# Set header formats looked for
hf=[[],[],[],[]] # header formats
ht=[[],[],[],[]] # header types
# hf[0] report containing all jobs, appointed or not
# 'BigReport1' on eworks - defaults to jobs created in past 6 months
hf[0] = ['Job Ref', 'Start Date', 'Site Postcode', 'Job Type', 'Status', 'Customer Name', 'Short Description', 'Site Company Name', 'Customer Site', 'Job Sub Total']
ht[0] = [2,1,0,0,0,0,0,0,0,3]
# hf[1] appointments report
# 'BigReport2' on eworks - defaults to appointments updated within the past 6 months
hf[1] = ['Job Ref', 'Appointment User', 'Appointment Status', 'Job Sub Total', 'Actual Start Date', 'Actual End Date', 'Job User Notes', 'Recommendations', 'Last Updated On', 'Parts Needed']
ht[1] = [2,0,0,3,1,1,-1,-1,1,0]
# hf[2] quotes report
# 'BigReport3' on eworks - defaults to quotes created in past 6 months
hf[2] = ['Quote Ref', 'Quote Date', 'Status', 'Customer Name', 'Customer Job Ref', 'Last Updated On', 'Del Full Name', 'Customer Site', 'Description', 'Quote Sub Total']
ht[2] = [2,1,0,0,0,1,0,0,0,3]
# hf[3] products report
# 'ProductsReport' on eworks, defaults to jobs created in past 6 months
hf[3] = ['Job Ref', 'Description', 'Product Name', 'Item Code', 'Quantity', 'Price', 'Item Description','Tags','Notes','Start Date']
ht[3] = [2,0,0,0,3,3,0,-1,0,1]
#######################################################################################################################

# create empty list of list, to contain all the data, once reformatted

data=[[],[],[],[]]

# search for .csv files in reports directory
excellent=""
found=[0,0,0,0]
reportnames=['Jobs','Appointments','Quotes','Products']
files=['','','','']
fileshorts=['','','','']
log('Searching for and loading report files in '+os.path.join(root,reportsfolder))
for File in os.listdir(root+reportsfolder):
    if File.endswith(".csv"):
        excellent=File
        with open(root+reportsfolder+excellent, newline='') as csv_file:
            reader = csv.reader(csv_file, delimiter=",")
            line_count = 0
            caughtun=0
            for row in reader:
                if line_count == 0:
                    #print(row[0].find('"')
                    #print(len(row[0]))
                    # strip first element of list since includes some weird character
                    row[0]=row[0][row[0].find('"')+1:len(row[0])-1]
                    if row in hf:
                        # if row[] of first line is identical to one of hf[] lists,
                        # then save it somewhere
                        i=hf.index(row)
                        if found[i] == 0:
                            found[i]=1
                            files[i] = root+reportsfolder+excellent
                            fileshorts[i]=excellent
                            caughtun=1
                    else:
                        break
                    line_count += 1
                elif caughtun == 1:
                    data[i].append(formatter(row,i))
                else:
                    break

for j in range(4):
    if found[j]==1:
        log("Found "+reportnames[j]+" report")
    else:
        log("No "+reportnames[j]+" report")


if found[0] == 1 and found[1] == 1:
    # if at least the jobs and appointments reports are available, then process through it all
    [tjobs,tdays,tquot,tday2] = datachew(guess)
    [costs,missingcost,missingcostjobs,unasscost,concerns]=jobcost(guess)
    if plan == 1 and len(concerns)>0:
        cale=concernedjobs(concerns)
    if plan == 1:
        cale2=futureplanner()
else:
    # otherwise, just give up and go home
    quit()

if 'tree' in options:
    if 'root' in options:
        troot = 1
    else:
        troot = 0
    photofoldertree(sys.argv[options.index('tree')+1],troot) # use original sys.argv value since need original case
    # doesn't do much for now, just works through the folder names, suggesting proper formats
    quit()

# file away stuff
if 'file' in options:
    fileaway(root+reportsfolder+emailfiles,root+jobsfolder)

# Here we sort through the jobs to identify which ones to construct reports for
# This function also does the photo folder creation/deletion
# (folder stuff is a bit fresh off the assembly line - watch out for any issues)
[jobstorep,linkies]=photofolders(phistory,2)

[futjobs,futlinks]=findupcoming(7)
[futreports,fullly] = jrgen(futjobs,futlinks,-1000,1000,0)

[jobreports,full]=jrgen(jobstorep,linkies,-1000,0,0)
wd=date.today().weekday()

if wd==0:
    [jobreports2,full2]=jrgen(jobstorep,linkies,-3,-1,1)
    whenrep=date.today().strftime("%a %d %b")+" - Job reports \& recommendations from last Friday & the weekend"
    #fullreportlist2="Summary of past 3 days' appointment reports:\n"
else:
    whenrep=(date.today()+relativedelta(days=-1)).strftime("%a %d %b")+" - Job reports & recommendations"
    #fullreportlist2="Summary of yesterday's appointment reports:\n"
    [jobreports2,full2]=jrgen(jobstorep,linkies,-1,-1,1)

fullreportlist2=whenrep+"\n"
fullreportlist2+="Customers, sites & descriptions for all jobs from this day(s), along with details of who's attended, and the reports from eworks.\n"
fullreportlist2+="The attachment is a fuller list of recent jobs, including all eworks notes from every visit\n"

fullreportlist='Below is a list of all jobs attended in the past '+str(phistory)+' days.  Search this email by date dd/mm/yyyy to find specific job reports etc.\n'
ref=''
for itm in full:
    fullreportlist+=itm

for itm in full2:
    fullreportlist2+=itm

futfull=''
for itm in fullly:
    futfull+=itm
    
if reports==1:
    #repout=open('/tmp/gg.html',"w")
    emailsum=[[0,0,0],[0,0,0],[0,0],[0,0]]
    repoutt=''
    test=weektable(-5,5)
    try:
        test2=monthtable(-3,2)
    except:
        test2=''
    # last week, this week, next week
    # last month, this month, next month
    # orders and value over 7 days
    # quotes and value over 7 days
    
    j=-2

    j=-1
    monthlytab=[]
    dats=reportdates(1,0)

    #tthw=[]
    for i in range(3):
        datsm=reportdates(1,j+i)
        monthlytab.append([datsm[0].strftime("%b-%y"),"Figures for "+datsm[0].strftime("%b %Y")+"\n~~~~~~~~~~~~~~~~~~~~\n"+dailytable(datsm[0],datsm[-1],0)])
    # find week range to generate
    # aim for a range that always includes:
    # - all of current month
    # - last week, this week & next 2 weeks
    thismonth=reportdates(1,0)
    sdays=(date.today()-thismonth[0]).days
    edays=(thismonth[-1]-date.today()).days
    startw=-(int(sdays/7)+1)
    rangew=max(2,int(edays/7)+2)-startw
    allst=reportdates(0,startw)[0]
    allfn=reportdates(0,startw+rangew-1)[-1]
#    for i in range(rangew):
#        dats=reportdates(0,startw+i)
#        tthw.append(turntablehtml(dats[0],dats[-1])[0])
    tothw=turntablehtml(allst,allfn)[0]

    repoutt+="Weekly turnover figures:\n"
    repoutt+=tabulate(test,headers="firstrow",tablefmt="pretty")+"\n"
    repoutt+="\nMonthly turnover figures:\n"
    repoutt+=tabulate(test2,headers="firstrow",tablefmt="pretty")+"\n"

log("Job Folder tidying")

# first test if the reports are actually available to use
if found[0]==1 and found[1]==1 and foldersdo==1:
    jobfolders()
else:
    log("No job folder moves - either reports unavailable or folders option not set")

log('Finishing off')

if tidy == 1:
    for j in range(3):
        if found[j] == 1:
            shutil.copyfile(files[j],root+reportsfolder+"ProcessedReports/"+fileshorts[j])
            os.remove(files[j])
    log("Removing report files")
else:
    log("Leaving processed files in place")

log('Sending log report')
emailer('andy.swallow@michaelwilsonandson.co.uk', 'Logs, '+datetime.now().strftime("%d/%m/%Y at %H:%M:%S"), ansiout('\n'.join(logs)),[])

if chase == 1 and found == [1,1,1,1]:
    print("Generating quote chasing information")
    qtc=quotechase(0)
    qtc = (markdown.markdown(qtc)).replace("$","&pound")
    qtc2=quotechase(1)
    qtc2 = (markdown.markdown(qtc2)).replace("$","&pound")
    emailer(sendto, "Today's quotes to chase", qtc, [["This week's quotes",qtc2]])

if jrep == 1 and found == [1,1,1,1]:
    jobatt=[]
    #attachments.append(['Full report list',ansiout(fullreportlist)])
    for itm in jobreports:
        jobatt.append([itm[0],itm[2]+ansiout(itm[1])])
        if len(itm[3])>0:
            emailer(sendto, "Signoff report: "+itm[0],itm[2]+ansiout(itm[3]),[])
    for itm in futreports:
        jobatt.append([itm[0],itm[2]+ansiout(itm[1])])
        if len(itm[3])>0:
            emailer(sendto, "Upcoming attendance: "+itm[0],itm[2]+ansiout(itm[3]),[])
    emailer(sendto, 'Job reports', ansiout(fullreportlist),jobatt)
    emailer(sendto, 'Upcoming appointments', ansiout(futfull),[])


if reports == 1 and found == [1,1,1,1]:
    magic="###################\n# "+date.today().strftime('%a %d %b %Y')+" #\n###################\n\n"
    magic+=repoutt
    magic+=custtable(182,0)
    magic+=custtable(84,0)
    magic+=custtable(42,0)
    magic+=custtable(21,0)
    
    attachments=[]

    #tm=''
    #weekst=''
    #for w in tthw:
    #    weekst+= w+"\n\n"
    #attachments.append(["Daily detail",ansiout(weekst)])
    attachments.append(["Daily detail",ansiout(tothw)])
    attachments.append(['Turnover reports',ansiout(magic)])
    attachments.append(["All Recent Activity",ansiout(recenttable(1,1,1,1,14,0,0))])
    #attachments.append(["Tag suggestions",ansiout(tagsuggest())])
    #attachments.append(["Planner - full",ansiout(ongoing(14,0,120))])

    
    emailer(sendto, whenrep, ansioutwr(fullreportlist2),[["Full reports", ansioutwr(fullreportlist)]])

    emailer(sendto, 'Reports', ansiout(emailtable()), attachments)

    jobatt=[]
    [uap,etxt,tagsugs]=ongoing(14,0,90)
    jobatt.append(['Tags table',ansiout(tagsugs)])
    jobatt.append(['UAP Report',ansiout(uap)])
    emailer(sendto,'Tags/Planning', ansiout(etxt), jobatt)


# potentially unused stuff to remove

def fileaway(fromfolder,jobsfolder):
    # the idea of this one was to routinely file away files related to a job in the relevant folder
    # didn't really get used
    
    global tjobs
    #tjobs[0] - mwref
    #tjobs[15]- cust ref
    #tjobs[17]- po num
    custrefs=[]
    ponums=[]
    tjrefs=[]

    bar = Bar(padbar('Extracing job nums & refs'), max=len(tjobs))
    for job in tjobs:
        custrefs.append(str(job[15]))
        ponums.append(str(job[17]))
        tjrefs.append(job[0])
        bar.next()
    bar.finish()
    
    # searches fromfolder for anything with an mw ref in the filename,
    # and moves to the relevant folder in jobsfolder
    refslist=[]
    nameslist=[]
    urefs=[]
    # this scans the fromfolder and finds any file with an mw ref in the filename
    # (files only, ignores folders)
    log(bold('Filing away job-related files from '+fromfolder))
    for entry in os.scandir(fromfolder):
        if entry.is_file():
            found=-1
            name=entry.name.lower()
            while found == -1 and len(name)>0:
                i=0
                j=name.find('mw')
                if j>-1:
                    if name[j+2:j+7].isnumeric():
                        found=i+j
                        refslist.append(entry.name[found:found+7].lower())
                        if entry.name[found:found+7].lower() not in urefs:
                            # populate list of (unique) job refs found
                            urefs.append(entry.name[found:found+7].lower())
                        nameslist.append(entry.name)
                    else:
                        # if mw found but no number, then trim the string to start again
                        name=name[j+1:len(name)]
                        i=j
                else:
                    break

    # does the same for jobs folder, this time looking at only folders, not files
    # finds mw ref anywhere in name, not just at the beginning
    torefslist=[]
    tonameslist=[]
    for entry in os.scandir(jobsfolder):
        if entry.is_dir():
            found=-1
            name=entry.name.lower()
            while found == -1 and len(name)>0:
                i=0
                j=name.find('mw')
                if j>-1:
                    if name[j+2:j+7].isnumeric():
                        found=i+j
                        if entry.name[found:found+7] not in torefslist:
                            torefslist.append(entry.name[found:found+7].lower())
                            tonameslist.append(entry.name)
                    else:
                        # if mw found but no number, then trim the string to start again
                        name=name[j+1:len(name)]
                        i=j
                else:
                    break

    # now do the comparison and moves
    # just stick to looking for mw refs - anything else just gets a little over-complicated

    # Create folders separately, since otherwise risks system trying to create stuff twice
    bar = Bar(padbar('Creating missing folders'), max=len(urefs))
    for ref in urefs:
        log('Creating folder '+ref)
        if ref not in torefslist and dryrun == 0:
            os.mkdir(os.path.join(jobsfolder,ref.upper()))
        bar.next()
    bar.finish()
    
    bar = Bar(padbar('Move files to correct folders'), max=len(refslist))
    for i in range(len(refslist)):
        ref=refslist[i]
        if ref in torefslist:
            where=torefslist.index(ref)
            fold=tonameslist[where]
            log('Moving '+nameslist[i]+' to folder '+fold)
            if dryrun == 0:
                if os.path.exists(os.path.join(jobsfolder,fold,nameslist[i])):
                    shutil.move(os.path.join(fromfolder,nameslist[i]),os.path.join(jobsfolder,fold,"a "+nameslist[i]))
                else:
                    shutil.move(os.path.join(fromfolder,nameslist[i]),os.path.join(jobsfolder,fold))
        else:
            log('Moving '+nameslist[i]+' to folder '+ref)
            if dryrun == 0:
                #                os.mkdir(os.path.join(jobsfolder,ref.upper()))
                shutil.move(os.path.join(fromfolder,nameslist[i]),os.path.join(jobsfolder,ref.upper()))
        bar.next()
    bar.finish()
