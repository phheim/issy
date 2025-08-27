#!/bin/bash

/usr/bin/issy-bin "$@" \
        --caller-z3 /usr/bin/z3-4.13.3 \
        --caller-aut /usr/bin/ltl2tgba \
        --caller-muval /usr/bin/call-muval \
        - 
