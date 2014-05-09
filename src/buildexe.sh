#!/usr/bin/env bash

set -x

# $1: input code
# $2: output filename
# $3: libraries includes

input=$1
output=$2

shift 2
LIBS=$@

noext="${input%.*}"
hex=$noext.hex

coqc -dont-load-proofs $LIBS $input > $hex || exit $?
x86/bin/hexbin.exe $hex $output # was: xxd -r -p $hex > $output

