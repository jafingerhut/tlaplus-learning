# Introduction

I created this repository to record links to learning resources, TLA
files, and notes while I learned about
[TLA+](https://lamport.azurewebsites.net/tla/tla.html).


# Learning TLA+


## Leslie Lamport's TLA+ video course

The home page of this course is
[here](http://lamport.azurewebsites.net/video/videos.html).  All
videos in this course can also be viewed via [this
list](https://www.youtube.com/watch?v=p54W-XOIEF8&list=PLWAv2Etpa7AOAwkreYImYt0gIpOdWQevD)
on YouTube.

The directory
[`lamport-tlaplus-video-course-material`](lamport-tlaplus-video-course-material)
in this repository contains `.tla` files mentioned in the course.


## Dr. TLA+ Series

A [series of lecture video
recordings](https://github.com/tlaplus/DrTLAPlus) and associated TLA+
specifications that delve into various distributed algorithms,
primarily variations of Paxos.  The TLA+ parts of this are probably
more appropriate for someone who is already familiar with TLA+.


## tlaplus Google group

https://groups.google.com/g/tlaplus


# Utilities


## TLA command line interface

The [`tla-bin`](https://github.com/pmer/tla-bin) repository lets you
install simple bash scripts that function as a command line interface
to these commands:

* `sany` (TODO how to get help on options): A parser and syntax
  checker for TLA+ specifications.  I do not know if there are command
  line options.  Documented in the book ["Specifying
  Systems"](https://lamport.azurewebsites.net/tla/book.html), Chapter
  12.
* `tlc` (`tlc -h` for help): A model checker and simulator for
  executable TLA+ specifications, which include most specifications
  written by engineers.  Documented in the book ["Specifying
  Systems"](https://lamport.azurewebsites.net/tla/book.html), Chapter
  14.
* `pcal` (`pcal -h` for help): A translator from the PlusCal algorithm
  language to TLA+.  Not documented in the book "Specifying Systems",
  since PlusCal was developed after that book was written.  See the
  "Learning PlusCal" section of [this
  page](https://lamport.azurewebsites.net/tla/learning.html).
* `tlatex` (`tlatex -help` for help): A program for typesetting TLA+
  specifications.  Documented in the book ["Specifying
  Systems"](https://lamport.azurewebsites.net/tla/book.html), Chapter
  13.

All of these tools, plus the TLAPS Proof System, are described on the
[TLA+ Tools](https://lamport.azurewebsites.net/tla/tools.html) page.

I learned about `tla-bin` from the following article, which has a few
tips on using it, but I suspect the "Specifying Systems" book is more
in depth on this topic:

* Marianne Bellotti, "Introduction to TLA+ Model Checking in the
  Command Line", 2019-Jan-18,
  https://medium.com/software-safety/introduction-to-tla-model-checking-in-the-command-line-c6871700a6a2

There is also documentation for doing this on the TLA documentation
pages
[here](https://lamport.azurewebsites.net/tla/standalone-tools.html?back-link=tools.html).
