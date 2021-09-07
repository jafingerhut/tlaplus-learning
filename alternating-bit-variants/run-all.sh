#! /bin/bash

TLC="java -XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC -cp $TLA2TOOLS_DIR/tla2tools.jar tlc2.TLC"

for j in `seq 1 16`
do
    case $j in
	1) expected_status=0
	   ARGS="AB_ql3.tla -config AB_ql3_safety_only.cfg"
	   ;;
	2) expected_status=0
	   ARGS="AB_ql3.tla -config AB_ql3_fss_satisfies_fs.cfg"
	   ;;
	3) expected_status=13
	   ARGS="AB_ql3.tla -config AB_ql3_fww_satisfies_fs.cfg"
	   ;;
	4) expected_status=13
	   ARGS="AB_ql3.tla -config AB_ql3_fsw_satisfies_fs.cfg"
	   ;;
	5) expected_status=13
	   ARGS="AB_ql3.tla -config AB_ql3_fws_satisfies_fs.cfg"
	   ;;
	6) expected_status=0
	   ARGS="AB_trigacks_ql3.tla -config AB_ql3_safety_only.cfg"
	   ;;
	7) expected_status=0
	   ARGS="AB_trigacks_ql3.tla -config AB_ql3_fss_satisfies_fs.cfg"
	   ;;
	8) expected_status=13
	   ARGS="AB_trigacks_ql3.tla -config AB_ql3_fww_satisfies_fs.cfg"
	   ;;
	9) expected_status=13
	   ARGS="AB_trigacks_ql3.tla -config AB_ql3_fsw_satisfies_fs.cfg"
	   ;;
	10) expected_status=13
	   ARGS="AB_trigacks_ql3.tla -config AB_ql3_fws_satisfies_fs.cfg"
	   ;;
	11) expected_status=13
	   ARGS="-difftrace AB_nonfifo_ql3.tla -config AB_ql3_safety_only.cfg"
	   ;;
	12) expected_status=13
	   ARGS="-difftrace AB_nonfifoBtoA_ql3.tla -config AB_ql3_safety_only.cfg"
	   ;;
	13) expected_status=0
	   ARGS="ABQSpec_ql.tla -config ABQSpec_ql_safety_only.cfg"
	   ;;
	14) expected_status=0
	   ARGS="ABQ_ql.tla -config AB_ql3_safety_only.cfg"
	   ;;
	15) expected_status=0
	   ARGS="-difftrace ABQ_ql.tla -config AB_ql3_fss_satisfies_fs.cfg"
	   ;;
	16) expected_status=13
	   ARGS="-difftrace ABQ_nonfifo_ql.tla -config AB_ql3_safety_only.cfg"
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
