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
in this repository contains `.tla` files mentioned in the course.  The
[`README.md`](lamport-tlaplus-video-course-material/README.md) file in
that directory contains detailed instructions for what steps to do in
the TLA Toolbox GUI program to match what is suggested in the
lectures, and in addition, how to do all of those steps using `tlc`
from the command line.

The directory [`andy-exercises`](andy-exercises) contains slightly
modified versions of several files from the directory
[`lamport-tlaplus-video-course-material`](lamport-tlaplus-video-course-material)
which I edited while working through the exercises suggested in the
lectures.

The command line capabilities of `tlc` are documented thoroughly in
the book ["Specifying
Systems"](https://lamport.azurewebsites.net/tla/book.html), Chapter
14.


## Cheatsheet for ASCII syntax of TLA+ operators

As a way to be able to go to a relatively small file and see a few
examples of each TLA+ operator, including those defined in the
standard modules, using the ASCII syntax rather than the
pretty-printed version that I often forget what their ASCII
equivalents are, I created the file
[`cheatsheet.tla`](tlaplus-cheatsheet/cheatsheet.tla).  The output of
running `tlc` on that file is in
[`cheatsheet-tlc-out.txt`](tlaplus-cheatsheet/cheatsheet-tlc-out.txt).
I may take the time to create one that looks nicer than that, with
both pretty-printed and ASCII versions in a PDF file, for example, but
this file is highly useful to me as is.


## My variants of the alternating bit protocol

The directory [`alternating-bit-variants`](alternating-bit-variants)
contains several variations and extensions of the alternating bit
protocol, starting with the version given in Lamport's video Lecture
9.  See the [`README.md`](alternating-bit-variants/README.md) file in
that directory for the order that I created them, and comments on the
results of running `tlc` on each one.


## Other reliable transport protocols

Starting from the alternating bit protocol, directory
[`reliable-transport`](reliable-transport/README.md) contains a
different specification [`RTSpec.tla`](reliable-transport/RTSpec.tla)
for how a reliable transport protocol ought to behave, without
reference to any alternating bits.

That directory includes TLA+ implementations of a Go-Back-N protocol,
and a Selective Repeat ARQ protocol.  See the
[`reliable-transport`](reliable-transport/README.md) there for
comments on the results of running `tlc` on each of them.


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

After learning about the `tla-bin` repository described below, I found
that the scripts that it installs are so simple that if you use the
Bash command line shell in Linux or macOS, it is quite easy to define
Bash aliases that work the same for most purposes.

See the files [`setup-tla-macos.bash`](setup-tla-macos.bash) and
[`setup-tla-ubuntu.bash`](setup-tla-ubuntu.bash) in this directory for
small scripts that I have successfully used on my macOS and Linux
systems to create Bash aliases like `sany` and `tlc` for running these
commands from a shell.  They would likely require modifications to
work on your system, e.g. to specify the directory where you installed
the TLA Toolbox.

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

There is also documentation for doing this on the TLA documentation
pages
[here](https://lamport.azurewebsites.net/tla/standalone-tools.html?back-link=tools.html).


### `tla-bin`

The [`tla-bin`](https://github.com/pmer/tla-bin) repository lets you
install simple bash scripts that function as a command line interface
to these commands.  See the previous section for a basic idea of what
each command does.

* `sany`
* `tlc`
* `pcal`
* `tlatex`

I learned about `tla-bin` from the following article, which has a few
tips on using it, but I suspect the "Specifying Systems" book is more
in depth on this topic:

* Marianne Bellotti, "Introduction to TLA+ Model Checking in the
  Command Line", 2019-Jan-18,
  https://medium.com/software-safety/introduction-to-tla-model-checking-in-the-command-line-c6871700a6a2
