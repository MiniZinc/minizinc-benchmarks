#!/bin/bash
# For each problem, tries to compile the "smallest" instance.

for PROBLEM_DIR in $(find . -mindepth 1 -maxdepth 1 -type d ! -name .git)
do
    OUTPUT_DIR=/tmp/minizinc-benchmarks/$PROBLEM_DIR
    mkdir -p $OUTPUT_DIR
    cd $PROBLEM_DIR
    MODEL_FILES=$(find . -type f -iname '*.mzn')
    DATA_FILES=$(find . -type f -iname '*.dzn')
    if [ -n "$DATA_FILES" ]
    then
        SMALLEST_DATA_FILE=$(ls -Sr $DATA_FILES | head -n 1)
        for MODEL_FILE in $MODEL_FILES
        do
            echo "Instantiating $MODEL_FILE with $SMALLEST_DATA_FILE"
            mzn2fzn --output-base $OUTPUT_DIR/$(basename -s .dzn $SMALLEST_DATA_FILE) $MODEL_FILE $SMALLEST_DATA_FILE
        done
    else
        SMALLEST_MODEL_FILE=$(ls -Sr $MODEL_FILES | head -n 1)
        echo "Compiling $SMALLEST_MODEL_FILE"
        mzn2fzn --output-base $OUTPUT_DIR/$(basename -s .mzn $SMALLEST_MODEL_FILE) $SMALLEST_MODEL_FILE
    fi
    cd ..
done
