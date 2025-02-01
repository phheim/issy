#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
COARDIR=$SCRIPT_DIR/../muval-mod-dc094f
BINARY=$COARDIR/_build/default/main.exe
OLDDIR=$(pwd)
INFILE=$(mktemp --suffix=.smt2)

OPTS="-c $COARDIR/config/solver/dbg_optpcsat_nc_tb_ar.json -p chcmax"

TIMEOUT=$1

tee > $INFILE

cd $COARDIR
timeout $TIMEOUT systemd-run --scope -p MemoryMax=8G --user $BINARY $OPTS $INFILE 2> /dev/null
cd $OLDDIR

rm $INFILE
