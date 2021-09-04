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

The section of the video "CHECKING THE SPEC" begins at time 14:02 of
the video, which is directly reachable at [this
link](https://youtu.be/u7fTLyiSnZw&t=842)

For the Toolbox, this time we will do something slightly different
than before to add the spec, because the file `PaxosCommit.tla`
already is a complete file, including the `--- MODULE PaxosCommit
----` line at the beginning and the line of equals signs at the end.

First copy the file `PaxosCommit.tla` from this directory into the
directory where you are doing your exercises (in my case it was the
directory `andy-exercises`, also in the repository).  Use your
operating system's capabilities to copy the file.

* Select menu item File -> Open Spec -> Add New Spec...
* In the window that appears, click Browse button
* In the window that appears, navigate to the folder to which you just
  copied the file `PaxosCommit.tla`.
* In the list of files within the folder that is now displayed, you
  should see `PaxosCommit.tla`.  Click on it to select it.  This
  should cause the text box in the top middle of the window that
  formerly contained "Untitled.tla" to now contain "PaxosCommit.tla".
* Click the Save button.
* Back at the window where I clicked the Browse button, click the
  Finish button.
* Save the spec using File -> Save

Create a new model with the default name "Model_1" using the same
steps as in the section for Lecture 3.

Before you can run the model, you must fill in the names of the
definitions of the Init: formula with `PCInit` and the Next: formula
with `PCNext`.

You must also provide a value for the four constants with names
`Ballot`, `Acceptor`, `Majority`, and `RM`.  Here are the values
recommended in the lecture.  You can assign these values in the
Toolbox following the same instructions described in the notes for
Lecture 5 above for the `RM` constant.

```
Ballot <- {0, 1}
Acceptor <- {a1, a2, a3}
Majority <- {{a1, a2}, {a1, a3}, {a2, a3}}
RM <- {r1, r2}
```

Make `Acceptor` and `RM` symmetry sets, as we did for `RM` as
described in the notes for Lecture 6 above.  `Ballot` and `Majority`
should be marked as "Ordinary assignment".

Add conditions `PCTypeOK` and `TCConsistent` as invariants to check.
This can be done using the same instructions as described in Lecture 4
above.

Click the green arrow button to run the model.  This took about 55
seconds on my 2015 MacBook Pro laptop.  It found no errors, and
119,992 distinct states.

Using the command line tools, I am not sure if the following is the
best or only way to make `RM` a symmetry set, but it is one way.
Create a file `TwoPhase.cfg` with the following contents:

```
CONSTANT
a1 = a1
a2 = a2
a3 = a3
r1 = r1
r2 = r2
Ballot <- Ballot_value
Acceptor <- Acceptor_value
Majority <- Majority_value
RM <- RM_value2
SYMMETRY symmetry_value_permutations
INIT
PCInit
NEXT
PCNext
INVARIANT
PCTypeOK
TCConsistent
```

TODO: I do not know why, but it is important that the lines giving
values for `Ballot`, `Acceptor`, `Majority`, and `RM` in the `.cfg`
file above must use `<-`, not `=` as done for the earlier constants.

You must also add the following lines to `TwoPhase.tla`:

```
EXTENDS Integers, TLC

CONSTANTS a1, a2, a3
CONSTANTS r1, r2

Ballot_value == {0, 1}
Acceptor_value == {a1, a2, a3}
Majority_value == {{a1, a2}, {a1, a3}, {a2, a3}}
RM_value2 == {r1, r2}

symmetry_value_permutations == Permutations(Acceptor_value) \union Permutations(RM_value2)
```

The line `EXTENDS Integers, TLC` should replace the existing line
`EXTENDS Integers`.  The other lines can follow the `EXTENDS` line if
you wish, or they can appear just about anywhere in the `.tla` file.

Then run the command:

```
$ tlc PaxosCommit.tla
```

As above there should be no error.  Again it found 119,992 distinct
states.


# Lecture 9, Part 1: Remove.tla


# Lecture 9, Part 1: ABSpec.tla

The section of this video discussing what to do in the Toolbox begins
at time 10:17 of the video, which is directly reachable at [this
link](https://youtu.be/G2QkMpiVFDo&t=617).

Follow the steps in the section for Lecture 7 above to copy the file
`ABSpec.tla` from this directory into the directory where you are
doing your exercises, and add it to the Toolbox.

Create a new model with the default name "Model_1" using the same
steps as in the section for Lecture 3.

Define a value for the constant `Data` of `{"d1","d2","d3"}` using
similar steps as in the section for Lecture 5.

Add `TypeOK` and `Inv` as invariants to check using similar steps as
in the section for Lecture 4.

Click the green run button.  There should be no errors this time.

To run the model from the command line, create a file
`ABSpec.cfg` using a text editor, containing these lines:

```
CONSTANT
Data <- Data_value
SPECIFICATION
Spec
INVARIANT
TypeOK
Inv
```

You must also add the following lines to `ABSpec.tla`:

```
Data_value == {"d1", "d2", "d3"}
```

Then run the command:

```
$ tlc ABSpec.tla
```


## Cloning a model

The section of this video discussing what to do in the Toolbox for
adding liveness conditions to `ABSpec` starts at time 18:32 of the
video, which is directly reachable at [this
link](https://youtu.be/G2QkMpiVFDo&t=1112).

In the Toolbox, while `ABSpec` and its `Model_1` are open:

* Clone the model by selecting menu item TLC Model Checker -> Clone
  Model -> Model_1
* In the window that appears, the default name of `Model_2` is fine.
  Click the OK button.

A note from the lecture: For liveness checking, your model must not
have any symmetry set.  If it does, change it.  If you have followed
the instructions above and not created a symmetry set, there is
nothing to change.

Change its behavior spec to `FairSpec`:

* Select the "Model Overview" tab.
* In the section "What is the behavior spec?", the popup menu should
  say "Temporal formula".  If it does not, change the popup menu
  setting to "Temporal Formula".
* In the text box below "Temporal Formula", change the text so it says
  `FairSpec`.

Check a particular liveness property:

* In the section "What to check?", open the sub-section named
  "Properties".
* Click the Add button on the right in the "Properties" section.
* In the window that appears, enter the following liveness formula:

```
\A v \in Data \X {0,1}: (AVar = v) ~> (BVar = v)
```

* Click the Finish button.

Click the green arrow button to run the model.  No errors should be found.

To run the model from the command line, create a file
`ABSpec-liveness.cfg` using a text editor, containing these lines:

```
CONSTANT
Data <- Data_value
SPECIFICATION
FairSpec
INVARIANT
TypeOK
Inv
PROPERTY
Liveness_property_1
```

You must also add the following lines to `ABSpec.tla`:

```
Liveness_property_1 == \A v \in Data \X {0,1}: (AVar = v) ~> (BVar = v)
```

Then run the following command.  Note that if you do not use the
`-config` command line option to `tlc`, as we have always run it
before, then `tlc` will read the configuration for a spec `foo.tla`
from `foo.cfg`.  If you give the `-config bar.cfg` option, you can
force `tlc` to read the configuration from any file you wish.

```bash
$ tlc -config ABSpec-liveness.cfg ABSpec.tla
```


# Lecture 9, Part 2: AB.tla

The section of the video "THE TLA+ SPEC" begins at time 2:35 of the
video, which is directly reachable at [this
link](https://youtu.be/ata84UpVJkU&t=155).

Follow the steps in the section for Lecture 7 above to copy the file
`AB.tla` from this directory into the directory where you are doing
your exercises, and add it to the Toolbox.

The section of the video "CHECKING SAFETY" begins at time 6:34 of the
video, which is directly reachable at [this
link](https://youtu.be/ata84UpVJkU&t=394).

Create a new model with the default name "Model_1" using the same
steps as in the section for Lecture 3.

In the section "What is the behavior spec?", the popup menu should
have "Temporal Formula" selected, and the box beneath that should
contain `Spec`.  If anything differs from that, change it to be that
way.

* In the model's "Model Overview" tab, in the section titled "What is
  the model?", click to select the line `Data <-` and click the Edit
  button.
* In the text box, enter `{d1,d2,d3}`
* Below the text box, click the circle next to "Set of model values".
* Click the Finish button.

Add `TypeOK` as an invariant to check using similar steps as in the
section for Lecture 4.


## Adding state constraints to the model

* In the model's "Model Overview" tab, just above the section "What is
  the model?", there is an underlined "Additional Spec Options" link.
  Click on it. A new tab "Spec Options" should appear and be selected.
* In the section "State Constraint", enter the following formula in
  the text box:

```
/\ Len(AtoB) =< 3
/\ Len(BtoA) =< 3
```


## Checking that AB implements ABSpec

In the "Model Overview" tab, add this formula in the Properties
sub-section of section "What to check?":

```
ABS!Spec
```

Click the green arrow to run the model.  There should be no errors.

Using the command line tools, we could create a file `AB.cfg` similar
to how we have done in earlier lectures, but it would again require
adding several lines to `AB.tla` that define things that do not really
belong in the specification `AB.tla`.

Instead, this time we are going to do it more like how the TLA+
Toolbox does, which is to create a new specification
`ABplusconstraints` that extends `AB`.  Create a file
`ABplusconstraints.tla` with the following contents:

```
-------------------------- MODULE ABplusconstraints -------------------------
EXTENDS AB

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_atmost3messages ==
    /\ Len(AtoB) =< 3
    /\ Len(BtoA) =< 3

ABS_Spec == ABS!Spec

=============================================================================
```

Now create a file `ABplusconstraints.cfg` with the following contents:

```
CONSTANT
d1 = d1
d2 = d2
d3 = d3
Data <- Data_value
SPECIFICATION
Spec
CONSTRAINT
Constraint_atmost3messages
INVARIANT
TypeOK
PROPERTY
ABS_Spec
```

To run TLC on this new extended spec:

```bash
$ tlc ABplusconstraints.tla
```


## Checking liveness of AB

The section of the video "LIVENESS" begins at time 10:52 of the video,
which is directly reachable at [this
link](https://youtu.be/ata84UpVJkU&t=652).

Edit the definition of `FairSpec` in `AB.tla` to look like this,
i.e. replace boh occurrences of `SF` with `WF`:

```
FairSpec == Spec  /\  WF_vars(ARcv) /\ WF_vars(BRcv) /\
                      WF_vars(ASnd) /\ WF_vars(BSnd)
```

Clone `Model_1` of `AB` to a new model `Model_2`, using the same steps
for cloning described earlier in the section on Lecture 9, Part 1.

In the "What is the behavior spec?", change `Spec` to `FairSpec`.

In the Properties sub-section of section "What to check?", edit
`ABS!Spec` to replace it with `ABS!FairSpec`.

Click the green arrow button to run the model.  It reports a violation
of the temporal part of the specification.  The video discusses the
counterexample given by TLC, and the difference between weak and
strong fairness.

Using the command line tools, create a new module `ABwithfairness` by
creating the file `ABwithfairness.tla` with the contents below:

```
--------------------------- MODULE ABwithfairness ---------------------------
EXTENDS AB

CONSTANTS d1, d2, d3

Data_value == {d1, d2, d3}

Constraint_atmost3messages ==
    /\ Len(AtoB) =< 3
    /\ Len(BtoA) =< 3

ABS_Spec == ABS!FairSpec

=============================================================================
```

Now create a file `ABwithfairness.cfg` with the following contents:

```
CONSTANT
d1 = d1
d2 = d2
d3 = d3
Data <- Data_value
SPECIFICATION
FairSpec
CONSTRAINT
Constraint_atmost3messages
INVARIANT
TypeOK
PROPERTY
ABS_Spec
```

To run TLC on this new extended spec:

```bash
$ tlc ABwithfairness.tla
```


# Lecture 10, Part 1: AB2.tla
# Lecture 10, Part 2: AB2P.tla
# Lecture 10, Part 2: AB2H.tla


# Andy's experiments on variants of the Alternating Bit protocol


## Make receiver only send acknowledgements when it receives a data message

That is, B will only send an ACK message as a consequence of receiving
a data message from A.  It will not periodically send ACK messages.

As long as A periodically sends data messages, I believe that should
be enough to maintain liveness properties.  Verify that this is so.


## Make sender only send data messages when it receives an acknowledgement

That is, A will only send a data message as a consequence of receiving
an acknowledgement from B.  It will not periodically send data
messages.

As long as B periodically sends acknowledgements, I believe that
should be enough to maintain liveness properties.  Verify that this is
so.


## Make both sender and receiver only send messages after receiving a message

It seems pretty clear to me that this should lead to deadlock.  Verify
that TLC can detect this, too.


## Make the link in one or both directions able to reorder messages

I believe the protocol will behave incorrectly in the face of
reordered messages, in either direction.

Verify that TLC can find an incorrect behavior if the link from A to B
can reorder messages, but the link from B to A is still FIFO (and
lossy).

Verify that TLC can find an incorrect behavior if the link from B to A
can reorder messages, but the link from A to B is still FIFO (and
lossy).

Finally, verify TLC can find an incorrect behavior if the links in
both directions can reorder messages.


## Make the link in both directions able to reorder messages, but use finite sequence number

I am not sure how best to model this in TLA+, but here is one thought:

Use a 3-bit sequence number, for example, i.e. sequence numbers in
messages must be in the range [0.7].

Whenever A increases its message sequence number from X-1 to X for
sending data messages, as a side effect of doing that, all messages on
the link from A to B with sequence number X are removed.  I believe
this should simulate in the model the assumption: by the time that A
reuses sequence number X after it last used it, all earlier messages
with sequence number X will have exceeded the maximum latency that the
network from A to B should ever have for any data message.

If that behavior is not difficult to specify, then a minor variation
is to make the side effect of A increasing its sequence number from
X-1 to X to instead discard all messages it sent earlier with a
sequence number in the range [X-D, X] (using arithmetic modulo 8, or
whatever the number of sequence numbers is), where D >= 0 is a
parameter that can be used to tune the maximum lifetime of messages in
the network.
