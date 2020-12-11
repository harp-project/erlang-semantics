#!/bin/bash
TMPDIR="tmp"
TMPFILE=$TMPDIR/"tmp.erl"

mkdir -p $TMPDIR

if [ -f $TMPFILE ] ; then
    rm $TMPFILE
fi

for ((i=2;i<=$#;i++))
  do
    if [ -d ${!i} ]
    then
        find ${!i}/* -maxdepth 0 -type f -name '*.erl' -exec cat {} + >> $TMPFILE
    else
        cat ${!i} >> $TMPFILE
    fi    
done

krun --config-var Exp=$1 $TMPFILE
