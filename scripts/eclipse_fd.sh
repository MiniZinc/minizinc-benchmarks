#!/bin/sh

cat $1 | eclipse -e "lib(flatzinc), lib(flatzinc_syntax), flatzinc:fzn_run(fzn_fd)"
