#! /bin/bash

TLC="java -XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC -cp $TLA2TOOLS_DIR/tla2tools.jar tlc2.TLC"

for j in `seq 7 9`
do
    case $j in
	1) expected_status=12
	   ARGS="RTSpec_ql.tla"
	   ;;
	2) expected_status=0
	   ARGS="AB_ql.tla -config AB_ql_safety_only.cfg"
	   ;;
	3) expected_status=0
	   ARGS="AB_ql.tla -config AB_ql_fss_satisfies_fs.cfg"
	   ;;
	4) expected_status=0
	   ARGS="AB_ql.tla -config AB_ql_fww_satisfies_fs.cfg"
	   ;;
	5) expected_status=0
	   ARGS="AB_ql.tla -config AB_ql_fweaker_satisfies_fs.cfg"
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
    ${TLC} ${ARGS} >& out-$j.txt
    exit_status=$?
    echo ""
    echo "$j \$TLC ${ARGS}"
    echo "exit_status: ${exit_status}"
    echo "expected_status: ${expected_status}"
    if [ $exit_status != $expected_status ]
    then
	echo "FIXME"
    fi
done
