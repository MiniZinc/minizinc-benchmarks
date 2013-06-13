#!/bin/bash

PREFIX="rpp"
UNITSQUARE="true"

for i in {3..30}
do
	if [ $i -lt 10 ] 
	then
		filename=$(echo $PREFIX)0$( echo $i)_$UNITSQUARE.data
	else
		filename=$PREFIX$(echo $i)_$UNITSQUARE.data
	fi
	#echo "$filename";
	echo -e "n = $i;\nConsider_Unit_Square = $UNITSQUARE;" > $filename
done
