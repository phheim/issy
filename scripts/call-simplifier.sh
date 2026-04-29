#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
SIMPDIR=$SCRIPT_DIR/../../symbolic-formula-simplification
SIMP=$SIMPDIR/simplify_smtlib.py

TIMEOUT=$1

STRENGTH=""

case $2 in
    1)
        STRENGTH="-s redundancy" # least aggressive simplification
        ;;
    2)
        STRENGTH="-s expansion"
        ;;
    3)
        STRENGTH="-s combined" # most aggressive simplification
        ;;
    *)
        STRENGTH="" # default simplification
        ;;   
esac

timeout $TIMEOUT python3 $SIMP - $STRENGTH --verify 2> /dev/null

