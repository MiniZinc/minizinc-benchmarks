#!/bin/sh
# Usage: zc --data <data>.dzn <model>.mzn
#
# Produces an executable named model_data
# (For using the Zinc compiler

OUTPUT_FILE=""

while test $# -gt 0
do
	case "$1" in

	-d|--data)
		DATA_FILE="$2"
		DATA_FLAGS="--data $2"
		shift
	;;
	
	--output-to-file)
		OUTPUT_FILE="$2"
		shift
	;;

	*)
		break
	;;
	esac
	shift
done

base_model=`basename $1 .mzn`
zinc --mmc-flags="-O5 --intermodule-optimisation --optimise-constructor-last-call" $DATA_FLAGS $1

if test "$OUTPUT_FILE" != ""
then
	mv "$base_model" "$OUTPUT_FILE"
	OUTPUT_FILE="$base_model"
fi
