# Introduction

This document describes how to perform the steps recommended in Leslie
Lamport's TLA+ video course, both in the TLA+ Toolbox GUI, and also
using the TLA+ command line tools.

I have done all of this using the following versions of software:

* Ubuntu Linux 20.04.3
* For the TLA+ command line tools, I installed AdoptOpenJDK 11.0.9.1
  dated 2020-11-04
* TLA+ Toolbox 1.7.1 for Linux from file
  `TLAToolbox-1.7.1-linux.gtk.x86_64.zip`

I had the file `tla2tools.jar` installed on my system in the directory
`$HOME/install/bin`.  Below are the long form commands for running the
static analyzer tool, the TLATeX converter, and TLC model checker.
After that are 3 Bash shell `alias` commands that, after executing
them in a Bash shell, the shorter commands given after them are
equivalent in behavior to the longer ones.

Long form of commands:
```bash
$ java -cp $HOME/install/lib/tla2tools.jar tla2sany.SANY SimpleProgram.tla 
$ java -cp $HOME/install/lib/tla2tools.jar tla2tex.TLA SimpleProgram.tla 
$ java -XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC -cp $HOME/install/lib/tla2tools.jar tlc2.TLC SimpleProgram.tla
```

Bash alias commands:
```bash
$ alias sany='java -cp $HOME/install/lib/tla2tools.jar tla2sany.SANY'
$ alias tlatex='java -cp $HOME/install/lib/tla2tools.jar tla2tex.TLA'
$ alias tlc='java -XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC -cp $HOME/install/lib/tla2tools.jar tlc2.TLC'
```

Short form of commands:
```bash
$ sany SimpleProgram.tla
$ tlatex SimpleProgram.tla
$ tlc SimpleProgram.tla
```

The `tlatex` command above writes several files when successful,
including `SimpleProgram.dvi`.  Running the command:

```bash
dvipdf SimpleProgram.dvi
```

causes a file `SimpleProgram.pdf` to be created that can be viewed
with any PDF reader, e.g.

```bash
xdg-open SimpleProgram.pdf
```

on Ubuntu Linux.


# Lecture 3: SimpleProgram.tla

The section of the video "Creating a Spec" begins at time 2:47 of the
video, which is directly reachable at [this
link](https://youtu.be/4NtHUfXlf4g?t=167).

In that video, the first screen appearing for the TLA Toolbox shows
that the person making the recording was using version 1.5.3 of
2016-Feb-11 of the TLA Toolbox.  There seem to be a few differences
with version 1.7.1 that I am using, which I will try to highlight in
my description.


## Creating a new spec

To start a new spec named "SimpleProgram":

* Select menu item File -> Open Spec -> Add New Spec...
* In the window that appears, click Browse button
* In the window that appears, navigate to an empty folder
  `andy-exercises` that I created.
* In the top middle of that window is a text box containing
  "Untitled.tla" with "Untitled" selected.  The text box has a label
  "Name" to its left.  I changed the text box contents to
  "SimpleProgram.tla", then clicked the Save button.
* Back at the window where I clicked the Browse button, click the
  Finish button.
* I now see a Spec Explorer menu on the left, and a window labeled
  "SimpleProgram.tla" at the top, with a big text editor window
  beneath it containing only a few lines of text, the first line
  saying "MODULE SimpleProgram" in the middle.
* Minimize the Spec Explorer menu on left by clicking the Minimize
  icon near the upper right of that sub-window, which looks like a
  horizontal bar.

To copy the desired spec into this new spec:

* In a separate text editor window that had the file
  `SimpleProgram.tla` in this directory open, I copied all except the
  first and last lines, then pasted that text after the "MODULE
  SimpleProgram" line in the TLA+ Toolbox window.
* Select menu item File -> Save to save the spec.

Using the command line tools, I simply copied the file
`SimpleProgram.tla` from this directory into a new directory.

To check its syntax:
```bash
$ sany SimpleProgram.tla
```


## Pretty-printing the spec

To create a pretty-printed version of a spec:

* Selecting File -> Produce PDF Version worked on my system since I
  had the necessary LaTeX software installed.  I do not know what a
  minimum set of Ubuntu 20.04 packages is to do this, but on my system
  I had used this script to install TeX packages:
  https://github.com/p4lang/p4-spec/blob/main/p4-16/spec/setup-for-ubuntu-linux.sh

To create a DVI file using the command line tools, then a PDF file
from the DVI file, and view it:
```bash
$ tlatex SimpleProgram.tla
$ dvipdf SimpleProgram.dvi
$ xdg-open SimpleProgram.pdf
```


## Create a model and run TLC on it

Back in the TLA+ Toolbox:

* Create a new model by selecting menu item TLC Model Checker -> New
  Model...
* In the "New model..." window that appears, there is a default model
  name of "Model_1" supplied.  Leave that unchanged and click the OK
  button.
* A new tab titled "Model_1" appears in the Toolbox window.
* In the section titled "What is the behavior spec?" are two text
  boxes, one labeled "Init:" containing "Init", and one labeled
  "Next:" containing "Next".  The Toolbox has auto-detected
  definitions with these default names and guessed this is what we
  want.  Leave them unchanged.
* Click on the green arrow button that gives the tooltip "Runs TLC on
  the model." when you hover the mouse cursor over it.

Note that when you run TLC, it creates several files in a directory
named `SimpleProgram.toolbox/Model_1` (when the model is named
`Model_1`), including a file `MC.cfg`.  If there is ever a TLC run
that you know how to perform using the Toolbox GUI settings, do it,
then look for such a file.

To run the model from the command line, create a file
`SimpleProgram.cfg` using a text editor, containing these lines:

```
INIT
Init
NEXT
Next
```

Then run the command:

```bash
$ tlc SimpleProgram.tla
```

Version difference: In the video, it says that a model contains three
pages, shown as 3 tabs in the Toolbox named "Model Overview",
"Advanced Options", and "Model Checking Results".  With the software
versions I was using, I only saw the first and last one, with no
"Advanced Options" tab.


## Run TLC treating deadlock as expected termination, not an error

* Click to select the "Model Overview" page.
* In the section titled "What to check?", there is a checkbox,
  currently checked, labeled "Deadlock".  Click the box to make it
  unchecked.
* Click the green run button.  There should be no errors this time.

To do this in the command line version, add the `-deadlock` option to
the command line:
```bash
$ tlc -deadlock SimpleProgram.tla
```

You can also do it by adding the following lines to the
`SimpleProgram.cfg` file, and running `tlc SimpleProgram.tla` with no
`-deadlock` option:
```
CHECK_DEADLOCK
FALSE
```
Even if you explicitly assign `TRUE` to `CHECK_DEADLOCK` in the `.cfg`
file, the `-deadlock` command line option will override that.


# Lecture 4: DieHard.tla

The section of the video "SAVING OUR HEROES" begins at time 9:34 of
the video, which is directly reachable at [this
link](https://youtu.be/IW0oA3Pxe-Q&t=573).

Start by creating a new spec named "DieHard", using the same steps
used in the previous section, except with a different module name.

Then copy the contents of the file `DieHard.tla` in this directory
into the Toolbox window, and save it.

Create a new model with the default name "Model_1" as in the previous
section.  Note that there is effectively a separate namespace for
model names for each spec, i.e. every spec can have a model with the
same name as each other, and there will be no naming conflicts.

Verify that the "Init:" and "Next:" text boxes have automatically been
filled in with "Init" and "Next" definition names from the DieHard
spec, and then run the model.  It should complete with no errors.

From the command line, create a file `DieHard.cfg` containing the
following lines:

```
INIT
Init
NEXT
Next
```

Then run the command:

```bash
$ tlc DieHard.tla
```

As mentioned in the video, we did not ask TLC to check anything, so no
errors simply means there were no terrible problems with the spec that
prevents it from being checked.


## Run TLC, checking that every reachable state satisfies an invariant

* Click to select the "Model Overview" page.
* In the section titled "What to check?", there is sub-section titled
  "Invariants".  If it is minimized, i.e. if it does _not_ have the
  text "Formulas true in every reachable state" just below it, click
  the little square with a plus sign inside of it to the left of
  "Invariants" to make that appear.
* To the right of the empty rectange are buttons Add, Edit, and
  Remove.  Click the Add button.
* In the new window that appears, type "TypeOK" (without the double
  quotes) into the text box, then click the Finish button.
* That new window should disappear, and now the box in the Invariants
  section should list "TypeOK" inside of it, with a check box next to
  it that is checked, meaning that checking of that condition as an
  invariant is currently enabled.
* Click the green run button.  There should be no errors this time.

From the command line, edit the file `DieHard.cfg` so it contains the
following, adding the `INVARIANT` and `TypeOK` lines shown at the end:

```
INIT
Init
NEXT
Next
INVARIANT
TypeOK
```

Then run the command:

```bash
$ tlc DieHard.tla
```

To add the `big /= 4` invariant to check recommended in the course,
repeat the steps above in the Toolbox to add another invariant, this
time typing `big /= 4` instead of `TypeOK` as the condition of the new
invariant.

When you click the green run button this time, there should be an
error "Invariant big /= 4 is violated." and the Error-Trace
exploration lets you view the sequence of states that TLC found that
leads to the invariant being violated.

From the command line, unfortunately you _cannot_ simply edit the file
`DieHard.cfg` to add a line `big /= 4` at the end.  If you try this,
running `tlc` will give an error.  I believe this is because the
`.cfg` file only supports symbols that name definitions in the
`INVARIANT` section, not arbitrary expressions.

Instead, edit the file `DieHard.tla` to add a new named definition for
the invariant you want to check, e.g.:

```
BigNot4 == big /= 4
```

Then edit `DieHard.cfg` to add a new line containing `BigNot4` at the
end, in the `INVARIANT` section after the line `TypeOK`.

Then run the command:

```bash
$ tlc DieHard.tla
```

Version difference: The version used in the video does not show the
names of steps taken in the error trace.  Fortunately in version 1.7.1
that I was using, the names of steps taken are displayed.  That is a
nice improvement.



# Lecture 5: TCommit.tla
# Lecture 6: TwoPhase.tla
# Lecture 7: PaxosCommit.tla
# Lecture 9, Part 1: Remove.tla
# Lecture 9, Part 1: ABSpec.tla
# Lecture 9, Part 2: AB.tla
# Lecture 10, Part 1: AB2.tla
# Lecture 10, Part 2: AB2P.tla
# Lecture 10, Part 2: AB2H.tla
