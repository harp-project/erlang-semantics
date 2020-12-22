#!/bin/bash
TESTDIR="../erl_tests"
MODDIR="modules"
TMPDIR="tmp"
TMPFILE=$TMPDIR/"tmp.erl"


if [[($# -ge 1) && (! -d $1)]]; then
    FILES=$1
    NUM=1
else
    if  [[($# -ge 1) && (-d $1)]]; then
        $TESTDIR=$1
    fi
    FILES=$TESTDIR/*.erl
    NUM=$(ls -lR $TESTDIR/*.erl | wc -l)
fi

OK=0

mkdir -p $TMPDIR

if [ -f $TMPFILE ] ; then
    rm $TMPFILE
fi

echo "Run $NUM module-local test(s)."
echo "-------------------------------------------------------------------"

for f in $FILES
do
  echo -n "  $(basename $f)..."
  echo "-module(tmp). -export([main/0]). " >> $TMPFILE
  cat $f >> $TMPFILE
  KCELL=$(krun --config-var Exp="tmp:main(.Exps)" $TMPFILE | sed -n '3p' | grep -c "true")
  if [ "$KCELL" -eq "1" ];  then
    echo "ok"
    OK=$((OK + 1))
  else
    echo "nok"
    NOK="$NOK $(basename $f)"
  fi
  rm $TMPFILE
done

echo "-------------------------------------------------------------------"
echo "$OK/$NUM passed."
echo "Errors: $NOK"

if [ "$#" -ge 1 ]; then
    exit 1
fi

DIRS=$TESTDIR/$MODDIR/*
NUM=$(ls $TESTDIR/$MODDIR/ | wc -l)
OK=0
NOK=0

mkdir -p $TMPDIR

if [ -f $TMPFILE ] ; then
    rm $TMPFILE
fi

echo "Run $NUM cross-module tests."
echo "-------------------------------------------------------------------"

for d in $DIRS
do
  echo -n "  $(basename $d)..."
  find $d/* -maxdepth 0 -type f -name '*.erl' -exec cat {} + >> $TMPFILE
  KCELL=$(krun --config-var Exp="main:main(.Exps)" $TMPFILE | sed -n '3p' | grep -c "true")
  if [ "$KCELL" -eq "1" ];  then
    echo "ok"
    OK=$((OK + 1))
  else
    echo "nok"
    NOK="$NOK $(basename $d)"
  fi
  rm $TMPFILE
done

echo "-------------------------------------------------------------------"
echo "$OK/$NUM passed."
echo "Errors: $NOK"
