#!/usr/bin/perl

use strict;
use warnings;
use File::Spec::Functions 'catfile';
use File::HomeDir qw(home);
use Term::ReadKey;
use Path::Tiny qw(path);
use Term::ANSIColor;


# get root directory location
my $root=home();
# set list filename
my $file=catfile($root,'lists.data');

# first read in the data file, since we always need to, even if just to help
# generate a new identifier
# this command just reads the data line by line into the array
# Since it's such a simple file format, s
my @listdata = path($file)->lines_utf8;
# various data formats used
my %internals;  # main internal data
my %hashes;     # list of hashtags in use, with the items they appear in
my @labels;     # list of internal labels
my @newlines;   # list of any new lines found
my @az=("a" .. "z","A" .. "Z",0 .. 9); # letter list used to generate item labels

parsedata(); # should take the file(s) read in, and convert into internal data format

# experimental loop
my $i;
my $j;
my @temp;
for $i (1 .. 10) {
    print findhash("this one is #this thing and that one is #that-thing");
    $j=labelgen();
    @temp=$internals{$j}[0];
    #print $internals{"&abcd"}[0];
    print @temp;
    print "\n";
}

# look at options passed
my @vals=starter(join(' ',@ARGV));

sub starter { # ongoing
    # pass this the command line arguments to be parsed
    my $args=$_[0];
    chomp $args; # trim the input
    if (grep /^\-/, $args) {
	# to dissect the above:
	# 1. search term surrounded by /
	# 2. ^ indicates beginning of string
	# 3. \- indicates -, the \ is escape character to stop '-' being interpreted as something else

	# get 2nd character of the string
	my $command = substr $args, 1, 1;
	if ($command eq 'i') {
	    # import option - for adding new items from a file, or from commandline
	    my $term = substr $args, 3; # remainder of string
	    return ('1',$term);
	} elsif ($command eq 'r') {
	    # review option, for amending any unflagged or unowned items
	    # if further options are passed, then used as search terms for lines to flag
	    # as completed
	    my $term = substr $args, 3;
	    return ('2',$term);
	} elsif ($command eq 'e') {
	    # if completing, get 3rd character as marker
	    my $itemlab = substr $args, 3, 1;
	    return ('3',$itemlab);
	} 
    } else {
	# if no arguments passed, then we'll just print the list out
	my $term = $args;
	itemadd($term);
	return ('5',$term);
    }
}

sub printer {
    # function to export the list of items, in various formats
    # separately calls a routine to email the output
}
sub reviewer {
    # one of the main functions
    
    # is passed a list of search terms, and generates a list of items
    # & subitems accordingly.  For main items, there'll be option to
    # mark as complete or reset.  For subitems, there'll be option to
    # remove, or edit change which main item it's attached to, or set
    # as main item instead

    # if no search terms provided, then generates list of all items
    # without a main tag, and gives option to flag as main items, or
    # subitems, etc.

    # this is automatically run after new items added or imported as well

    # remember to purge the newlines array at the end of this, or bit
    # by bit.  Either way it needs to be empty when this function
    # returns
}
sub importer {
}

sub emailer { # can do this later - printing to terminal ok for now
    # pass this an output printout from the printlist() function, and it'll email the relevant person,
    # and also increment all the relevant counters
}

sub parsedata {
    # take the @listdata array and:

    # - identify any internally generated tags
    # - search for hashtags in each item
    
    # - Look for any main items without tags, or incorrectly tagged, and fix.

    my $itemline;
    for $itemline (@listdata) {
	# search for an item label
        my $label=grep /&\w{4}/,$itemline;  # search for label of format '&abcd'
	my $counter=grep /c\d{5}c/,$itemline; # search for counter of format 'c12345c'
	if length($counter)>0 { $counter=substr($counter,1,5);}

	# to do
	# if flag is there then just ignore the line
	# and build the counter value into the internal data

	if (grep !/^<x>/,$itemline) { # only bother if no completion flag
	    if (length($label)>0) {
		$itemline =~ s/$label//; # remove mention of label from the item line
		# if there's a label, then is it already in %internals?
		if (exists $internals{$label}) {
		    # add this line as further info to the existing item
		    push (@{$internals{$label}}[2], $itemline);
		} else {
		    # add a new main item
		    @internals{$label}=[$counter,$itemline,[]];
		}
	    } else {
		# if no label found, then create one
		
		# but with a question mark on end of it, since may be
		# further info item?
		$label=labelgen(1);
		# also add to the @newlines list, with this label, to
		# be processed by the reviewer() routine
		push (@newlines, $itemline.' '.$label);
	    }
	    # find hashtags in the item line
	    my @tags = findhash($itemline);
	    if (scalar @tags > 0) {
		# if there are some hashtags
		my $tag;
		for $tag (@tags) {
		    if (exists $hashes{$tag}) {
			push (@{$hashes{$tag}}, $label);
		    } else {
			@hashes{$tag}=[$label]
		    }
		}
	    }
	}
    }
    return;
}

sub findhash {
    # pass this a string
    # it returns an array of any/all of the hashtags contained
    # a hashtag is # followed by alphanumeric characters only
    my $string=$_[0];
    my @words = split /[;:!?,. ]/,$string; # split string into words
    my $word; my @tags;
    for $word (@words) {
	if (grep /^#/, $word) { # check each word if begins with #
	    push @tags, $word;
	}
    }
    return @tags;
}

sub labelgen { # completed
    # randomly generates a new item label, and adds it to the labels list
    # also adds new element to the internals hash
    my $newlabel='';
    my $param=$_[0]; # if there's been a parameter passed, get it
    my $addn='';
    if ($param==1) { $addn='?';}
    while () { 
	# generate a random 4 character label
	$newlabel=$az[rand @az].$az[rand @az].$az[rand @az].$az[rand @az];
	if ("&".$newlabel ~~ @labels) {next;} # if it's now new then try again
	last; # otherwise leave
    }
    $internals{"&".$newlabel} = ["&".$newlabel,[]];
    push(@labels,"&".$newlabel.$addn);
    return "&".$newlabel;
}

sub itemadd { # ongoing
    #my $term=' | '.$_[0];
    print color 'green';
    print("What do you want to add?\n");
    print color 'reset';
    my $term=<STDIN>;
    chomp $term;
    open(TTY, "</dev/tty");
    print color 'cyan';
    print "Is this further info? ";
    my $key='';
    while($key ne 'y' and $key ne 'n') {
	ReadMode "raw";
	$key=ReadKey 0, *TTY;
	ReadMode "normal";
    }
    print("\n");
    print color 'reset';
    if ($key eq 'y') {
	# search for hashtags, parse input file, etc

	# open, read and parse the data file
	# scan data for relevant terms, hashtags, etc.
	# print list of just the main items which are contenders for this info line
	# get user to select which one
	# if there's ambiguity, i.e. if there was more than one contender, then add an internally generated
	# identifier (of the form &abc) to avoid confusion further down the line?
	
	path($file)->append_utf8('    | '.$term."\n");
    } else {
	# easier, just add to existing file
	path($file)->append_utf8('000 | '.$term." [".labelgen()."]\n");
    }
    
}
sub addline {
    # function to add a line to the output file
    # pass it up to 2 parameters - the text to add, and an optional (internal) label?
    # Main data array should surely be global?
}
sub findidents {
    # pass this some text content

    # takes the @listdata array, and forms a full wordlist?
}
sub readfile {
    # open list file and read into array
    my $file=$_[0];
    open(my $filedata, '<', $file) or die;
    # go throgh file line by line
    
    # create empty array?
    my $i=0;
    while (my $line = <$filedata>)
    {
	# trim whitespace from end of line
	chomp $line;
	if ($line ne "") {
	    # add next line to array
	    push ( @listdata, ());
	    # split according to |
	    # not sure if the | need spaces between?
	    my @bits = split "|",$line;
	    # trim the separated bits.  prob unnecessary?
	    chomp(@bits);
	    foreach(@bits) {
		# construct the internal array
		push (@{$listdata[$i]},$_);
	    }
	    $i++;
	}
    }
}

sub opener {
    # takes @listdata and converts to internal data format

    # for each line, finds the &label, and
    #     if new label, adds new item to internal hash
    #     and adds that internal label to the label list
    #     if existing label, add as further info
    #     either way, remove mention of the internal label 
    # if &label not present then add to separate array of new lines

    # if there are new lines, then run the reviewer routine?
}

sub closer {
    # takes the @internals list and writes out to the external data file
    # assumes that everything is correctly labelled, therefore make sure
    # the reviewer sub has been run prior to this
}

=begin
first parse the command line - if it's a new item then can do straight away
list <r>eview|<i>mport

(new) key points for how it should work:

with no arguments, prints to screen

'<r>eview' option is followed by search term(s), and gives option to
           complete or reset each one, or amend tags
           if no search terms supplied, then just allows for review
           of any questionable or missing tags
'<i>mport' takes text file(s), and imports into new items, then runs
           review function, to allow unclear tagging to be amended
           If no input files given, then allows for manually adding
           a line

The counter needs incrementing every time any item is completed

Functions needed:

opener -   opens the data file, and imports into whatever internal format is needed

closer -   writes internal format back out to the data file

importer - reads given text file(s) and adds on to existing data, ready to be written to file

review -   scans through existing data and identifies any items without a main tag.
           For each one, asks whether new, or further info item
           If further info:
           - Uses item as search terms to try to match with existing main items
           - Offers those
           - If none of those then lets user type in search terms, and does same again
           - Otherwise, show list of tags in use

printer -  to print the list to screen
           or to generate a printout suitable to be emailed

emailer -  to be given output from 'printer', to email to a set address
           also increments all the item counters

Others:

lineformat - takes an item line, either a main or a further info, and a list of search term(s),
             and outputs a formatted and/or coloured version, highlighing any hashtags, search
             terms, and stripping out the main (internal) tag
labelgen -   generates a new item identifier, just use 2 lowercase letters

File format:
text &label &12345&

with optional <x> at beginning to indicate done.  No counter if further info item

Internal data format:
hashes of arrays?
%hash{internallabel} = [counter, mainitem, [furtheritems]]

%hash{hashtag} = [listofinternals]

=cut

# variables are indicated by $name

# " la la " double quoted has control characters in it interpreted, e.g. \n
#           and variable names are replaced too
# ' la la ' whereas single quoted stuff is printed literally

# concatenation is $a.$b, instead of $a+$b

# lists are @list
# get 2nd element by $list[1] - note $ not @
# $#list is the length of the list, -1

# 3rd variable type - a hash
# %hash is a list of pairs
# e.g. %list{"first"}=101 assigns value 101 to the key "first"
# it's a labelled list, with very little effort
# can have array label as hash value.  if the array is @name, then
# %list{"first"}=\@name assigns array label to the hash %list

=begin 
Use tags as markers in items, in following ways:
- Hashtags, i.e. #thisisamarker
- Groups - [marker1, marker2,marker3]

Want to be able to have notepad open at work and know that the various
stuff I type in can get organised automatically, provided I use some
hashtags.  Want to be able to email myself notes.

---------------------------------


The text could contain at least one hashtag, to be used as identifier
to link the main items with the further info. Doesn't even have to be
a hashtag, just an identifier that's unique.
Only necessary when adding further info, so only required then.
Single items can be whatever

- No dates for items, unless manually typed in with the info

- Don't display counter, use some sort of colour coded dots, e.g. '.'
  for up to count of 5, '..' for up to 15, and '...' for 15 or above
- Or maybe just the vertical bars colour coded, red, amber green

------------------------------------------------------
# Send job report for Crewe sika                 [ ]
# job [25/4/22]                               
| - Take report from emails                   
| - Report saved to job folder                
# Do TM plan for MSC jobs for w/c 23/7/22        [ ]
| - Further note 1
| - Further note 2
------------------------------------------------------

Colour the '|' to give indication of age
Colour the main item text to highlight

=cut
