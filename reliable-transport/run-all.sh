#! /bin/bash

# OS detection
function is_osx() {
  [[ "$OSTYPE" =~ ^darwin ]] || return 1
}
function is_ubuntu() {
  [[ "$(cat /etc/issue 2> /dev/null)" =~ Ubuntu ]] || return 1
}

if is_osx; then
    TIME_CMD="/usr/bin/time -lp"
fi
if is_ubuntu; then
    TIME_CMD="/usr/bin/time --verbose"
fi

TLC="java -XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC -cp $TLA2TOOLS_DIR/tla2tools.jar tlc2.TLC"

for j in `seq 1 9`
do
    case $j in
	1) expected_status=12
	   ARGS="RTSpec_ql.tla"
	   ;;
	2) expected_status=0
	   ARGS="AB_fifo_ql.tla -config AB_ql_safety_only.cfg"
	   ;;
	3) expected_status=0
	   ARGS="AB_fifo_ql.tla -config AB_ql_fss_satisfies_fs.cfg"
	   ;;
	4) expected_status=0
	   ARGS="AB_fifo_ql.tla -config AB_ql_fww_satisfies_fs.cfg"
	   ;;
	5) expected_status=0
	   ARGS="AB_fifo_ql.tla -config AB_ql_fweaker_satisfies_fs.cfg"
	   ;;
	6) expected_status=12
	   ARGS="-difftrace AB_nonfifo_ql.tla -config AB_ql_safety_only.cfg"
	   ;;
	7) expected_status=0
	   ARGS="GBN_ql.tla -config GBN_ql_NSeq-4-W-2-safety_only.cfg"
	   ;;
	8) expected_status=0
	   ARGS="GBN_ql.tla -config GBN_ql_NSeq-4-W-3-safety_only.cfg"
	   ;;
	9) expected_status=12
	   ARGS="-difftrace GBN_ql.tla -config GBN_ql_NSeq-4-W-4-safety_only.cfg"
	   ;;
    esac
    ${TIME_CMD} ${TLC} ${ARGS} >& out-$j.txt
    exit_status=$?
    echo ""
    echo "$j $TIME_CMD \$TLC ${ARGS}"
    echo "exit_status: ${exit_status}"
    echo "expected_status: ${expected_status}"
    if [ $exit_status != $expected_status ]
    then
	echo "FIXME"
    fi
done
