#!/bin/bash
# negative controls of the second upper-bound checker (environment switches of ub86audit.py; see its docstring)
PY="python3 -I -B"
C=cert_ub_A22_1807129_83e03d16.json
run() { name=$1; shift; env OMP_NUM_THREADS=1 "$@" $PY ub86audit.py $C 1 > neg_$name.log 2>&1; echo "$name rc=$? $(tail -1 neg_$name.log)" >> negs.txt; }
rm -f negs.txt
run eps50000 UB_EPS=1/50000
run scaleb101 UB_SCALEB=101/100
run drop_x1 UB_DROP=1
run drop_mcK UB_DROP=11
run shift12e6 UB_SHIFT=12/1000000
run eps1e14 UB_EPS=1/100000000000000
echo ALLDONE >> negs.txt
