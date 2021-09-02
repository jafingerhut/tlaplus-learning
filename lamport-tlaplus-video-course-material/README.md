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

The section of the video "THE TLA+ SPEC" begins at time 5:15 of the
video, which is directly reachable at [this
link](https://youtu.be/JwO4yPSEp-0&t=315).

Start by creating a new spec named "TCommit", using the same steps as
in the section for Lecture 3, except with a different module name.

Then copy the contents of the file `TCommit.tla` in this directory
into the Toolbox window, and save it.

The section of the video "CHECKING THE SPEC" begins at time 18:13 of
the video, which is directly reachable at [this
link](https://youtu.be/JwO4yPSEp-0&t=1093).

Create a new model with the default name "Model_1" using the same
steps as in the section for Lecture 3.  Click the green arrow to run
the model.

There is an error.  Look for the red text "3 errors detected" next to
the heading "Model Overview" at the top of the Model Overview page.
In my version of TLC, clicking on "3 errors detected" did nothing.
Instead, some tooltip text appeared when I hovered my mouse cursor
over those words.  That tooltip text said:

```
Provide a value for constant RM
Next: The Next formula must be provided
Init: The Init formula must be provided
```

Before you can run the model, you must fill in the names of the
definitions of the Init: and Next: formulas.  They are not filled in
for you automatically by the Toolbox because the spec `TCommit.tla`
does not use the default names `Init` and `Next`.

Type `TCInit` into the Init: box, and `TCNext` into the Next: box.
Then click the green button to run the model.

To resolve the "Provide a value for constant RM" error:

* In the section titled "What is the model?" is a box containing the
  text "RM <-" with an unclickable "Edit" button to its right.  Click
  on the line containing the text "RM <-", and it should become
  selected, and the Edit button should now respond to clicks.
* Click the Edit button
* In the new window that appears, enter the text:

```
{"r1", "r2", "r3"}
```

* If any of the choices in the bottom left of the window other than
  "Ordinary assignment" is selected, click the circle to the left of
  "Ordinary assignment" to select it.
* Click the Finish button.

Add the invariant `TCTypeOK` in the Invariants section. using the same
steps as in the section for Lecture 4.

Disable deadlock being considered an error, using the same steps as in
the sectino for Lecture 3.

Click the green arrow button to run the model.  TLC should find no
errors.

Using the command line tools, create a file `TCommit.cfg` with the
following contents:

```
CONSTANT
RM <- RM_value
INIT
TCInit
NEXT
TCNext
INVARIANT
TCTypeOK
CHECK_DEADLOCK
FALSE
```

Note that running TLC will give an error if you use a line like this
in the `.cfg` file:

```
RM <- {"r1", "r2", "r3"}
```

Instead, we can add a line like this to `TCommit.tla`:

```
RM_value == {"r1", "r2", "r3"}
```

and use `RM_value` in the `.cfg` file as shown above.  Then run the
command:

```bash
$ tlc TCommit.tla
```

TODO: I see in the video the number of distinct states found: 34, and
I see this corresponding output from the `tlc` command line tool:

```
94 states generated, 34 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 7.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 6 and the 95th percentile is 4).
```

However, in the video Lamport points out that part of the Toolbox
output is the number of times each sub-action was used.  How can one
get that output from the command line tool?  I tried a few of the
options visible from `tlc -h`, but did not find one yet that provides
that output.


## Checking that `TCConsistent` is an invariant

Add the invariant `TCConsistent` in the Invariants section. using the
same steps as in the section for Lecture 4.

For the command line, the full contents of `TCommit.cfg` should now
be:

```
CONSTANT
RM <- RM_value
INIT
TCInit
NEXT
TCNext
INVARIANT
TCTypeOK
CHECK_DEADLOCK
FALSE
INVARIANT
TCConsistent
```


# Lecture 6: TwoPhase.tla

The section of the video "THE TLA+ SPEC" begins at time 4:30 of the
video, which is directly reachable at [this
link](https://youtu.be/U4mlGqXjtoA&t=270).

Start by creating a new spec named "TwoPhase", using the same steps as
in the section for Lecture 3, except with a different module name.

Then copy the contents of the file `TwoPhase.tla` in this directory
into the Toolbox window, and save it.

The section of the video "CHECKING THE SPEC" begins at time 15:41 of
the video, which is directly reachable at [this
link](https://youtu.be/U4mlGqXjtoA&t=941).

Create a new model with the default name "Model_1" using the same
steps as in the section for Lecture 3.

Before you can run the model, you must fill in the names of the
definitions of the Init: formula with `TPInit` and the Next: formula
with `TPNext`.  You must also provide a value for the constant `RM`.
As in the previous section, assign it a value of:

```
{"r1", "r2", "r3"}
```

Add the invariant `TPTypeOK` in the Invariants section. using the same
steps as in the section for Lecture 4.

Click the green arrow button to run the model.  TLC should find no
errors.

Using the command line tools, create a file `TwoPhase.cfg` with the
following contents:

```
CONSTANT
RM <- RM_value
INIT
TPInit
NEXT
TPNext
INVARIANT
TPTypeOK
```

Note that there is no need to add a line defining `RM_value` to
`TwoPhase.tla` if you already did so in `TCommit.tla` as recommended
in the previous section, because `TwoPhase.tla` has a line `INSTANCE
TCommit` that 'imports' this definition of `RM_value`.

Then run the command:

```bash
$ tlc TwoPhase.tla
```

TODO: Why isn't deadlock detected for this spec?  I suppose there must
be an enabled transition out of every state into another state?

The number of distinct states reported by both the Toolbox and command
line versions was 288 when I ran TLC on `TwoPhase.tla`.


## Making the value of `RM` a symmetry set

In the Toolbox:

* In the model's "Model Overview" tab, in the section titled "What is
  the model?", click to select the line `RM <- {"r1", "r2", "r3"}` and
  click the Edit button.
* In the text box, change `{"r1", "r2", "r3"}` to `{r1, r2, r3}`.
* Below the text box, click the circle next to "Set of model values".
* Then click the check box next to "Symmetry set" so that the check
  box is enabled.
* Click the Finish button.

Version difference: In the video, you must click a Next button to get
to another window before clicking Finish, but in Version 1.7.1 there
is no Next button to click.

Click the green arrow button to run the model.

There should be no error.  Because of making `RM` a symmetry set, the
number of Distinct States reported should be 80, much smaller than the
288 found above.

Using the command line tools, I am not sure if the following is the
best or only way to make `RM` a symmetry set, but it is one way.
Create a file `TwoPhase.cfg` with the following contents:

```
CONSTANT
r1 = r1
r2 = r2
r3 = r3
RM <- RM_value2
SYMMETRY RM_value2_permutations
INIT
TPInit
NEXT
TPNext
INVARIANT
TPTypeOK
```

You must also add the following lines to `TwoPhase.tla`:

```
EXTENDS TLC

CONSTANTS r1, r2, r3

RM_value2 == {r1, r2, r3}

RM_value2_permutations == Permutations(RM_value2)
```

The `EXTENDS TLC` line must be first in the spec, and is needed
because it defines the function `Permutations`.  The other lines can
be just about anywhere in the `TwoPhase.tla` file.

Then run the command:

```
$ tlc TwoPhase.tla
```

As above there should be no error.  Because the value of `RM` is a
symmetry set, the number of distinct states reported is 80 in the
output of `tlc`.



# Lecture 7: PaxosCommit.tla
# Lecture 9, Part 1: Remove.tla
# Lecture 9, Part 1: ABSpec.tla
# Lecture 9, Part 2: AB.tla
# Lecture 10, Part 1: AB2.tla
# Lecture 10, Part 2: AB2P.tla
# Lecture 10, Part 2: AB2H.tla
