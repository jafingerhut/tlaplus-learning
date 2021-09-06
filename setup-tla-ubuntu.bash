# This is a script I have on my system to set the JAVA_HOME
# environment variable, and to add to the PATH variable the directory
# ${JAVA_HOME}/bin
source $HOME/jdks/setup-adoptopenjdk-hotspot-11-64bit.sh

# This directory on my Ubuntu 20.04 system contains both the toolbox
# executable, to start the TLA+ Toolbox, and also a copy of the file
# tla2tools.jar
TLA2TOOLS_DIR=$HOME/p4-docs/tlaplus-toolbox-1.7.1

# Add the directory containing the toolbox command to PATH
export PATH=$TLA2TOOLS_DIR:$PATH

# Create bash aliases to provide short command names for command line
# utilities.
alias sany='java -cp $TLA2TOOLS_DIR/tla2tools.jar tla2sany.SANY'
alias pcal='java -cp $TLA2TOOLS_DIR/tla2tools.jar pcal.trans'
alias tlatex='java -cp $TLA2TOOLS_DIR/tla2tools.jar tla2tex.TLA'
alias tlc='java -XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC -cp $TLA2TOOLS_DIR/tla2tools.jar tlc2.TLC'
