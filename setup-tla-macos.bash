# This directory on my macOS system contains a copy of the file
# tla2tools.jar
export TLA2TOOLS_DIR=$HOME/Documents/p4-docs/tlaplus/tlaplus-1.7.1

# Create bash aliases to provide short command names for command line
# utilities.
alias sany='java -cp $TLA2TOOLS_DIR/tla2tools.jar tla2sany.SANY'
alias pcal='java -cp $TLA2TOOLS_DIR/tla2tools.jar pcal.trans'
alias tlatex='java -cp $TLA2TOOLS_DIR/tla2tools.jar tla2tex.TLA'
alias tlc='java -XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC -cp $TLA2TOOLS_DIR/tla2tools.jar tlc2.TLC'
