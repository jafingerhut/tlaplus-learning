#! /bin/bash

# TODO: Allow this value to be changed from the command line.
max_compute_time_sec=300

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

for j in `seq 1 14`
do
    # I do not want to bother giving an estimated compute time for all
    # of the TLC runs that are under 30 seconds, only for the longer
    # ones.  Treat all 'short' ones as 1 second, even if that is quite
    # far off numerically.
    estimated_compute_sec=1
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
	   estimated_compute_sec=216
	   ARGS="-difftrace AB_nonfifo_ql.tla -config AB_ql_safety_only.cfg"
	   ;;
	7) expected_status=0
	   ARGS="GBN_fifo_ql.tla -config GBN_ql_NSeq-4-W-2-safety_only.cfg"
	   ;;
	8) expected_status=0
	   estimated_compute_sec=90
	   ARGS="GBN_fifo_ql.tla -config GBN_ql_NSeq-4-W-3-safety_only.cfg"
	   ;;
	9) expected_status=12
	   ARGS="-difftrace GBN_fifo_ql.tla -config GBN_ql_NSeq-4-W-4-safety_only.cfg"
	   ;;
	10) expected_status=12
	    estimated_compute_sec=2280
	    ARGS="-difftrace GBN_nonfifo_ql.tla -config GBN_ql_NSeq-4-W-2-safety_only.cfg"
	    ;;
	11) expected_status=0
	    estimated_compute_sec=40
	    ARGS="-difftrace SRA_fifo_ql.tla -config SRA_ql_NSeq-4-W-2-safety_only.cfg"
	    ;;
	12) expected_status=12
	    estimated_compute_sec=20
	    ARGS="-difftrace SRA_fifo_ql.tla -config SRA_ql_NSeq-4-W-3-safety_only.cfg"
	    ;;
	13) expected_status=0
	    estimated_compute_sec=550
	    ARGS="-difftrace SRA_fifo_ql.tla -config SRA_ql_NSeq-6-W-3-safety_only.cfg"
	    ;;
	14) expected_status=12
	    estimated_compute_sec=550
	    ARGS="-difftrace SRA_fifo_ql.tla -config SRA_ql_NSeq-6-W-4-safety_only.cfg"
	    ;;
    esac
    echo ""
    if [ $estimated_compute_sec -gt $max_compute_time_sec ]
    then
	skip=1
	echo "Skipping the following command because estimated compute time $estimated_compute_sec sec > $max_compute_time_sec sec"
    else
	skip=0
	${TIME_CMD} ${TLC} ${ARGS} >& out-$j.txt
	exit_status=$?
    fi
    echo "$j $TIME_CMD \$TLC ${ARGS}"
    echo "expected_status: ${expected_status}"
    if [ $skip -eq 0 ]
    then
	echo "exit_status: ${exit_status}"
	if [ $exit_status != $expected_status ]
	then
	    echo "FIXME"
	fi
    fi
done
