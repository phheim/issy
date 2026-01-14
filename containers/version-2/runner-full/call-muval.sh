#!/bin/bash

OLDDIR=$(pwd)

INFILE=$(mktemp --suffix=.hes)
OPTS="-c ./config/solver/dbg_muval_parallel_exc_tb_ar.json -p muclp"
TIMEOUT=$1
tee > $INFILE
cd /muval
timeout $TIMEOUT ./_build/default/main.exe $OPTS $INFILE 2> /dev/null
rm $INFILE

cd $OLDDIR
