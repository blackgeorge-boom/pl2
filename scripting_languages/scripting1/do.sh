#! /bin/bash

function die () {
  printf "FAILED!!!\n"
  rm -f *.asm a.*
  read
  exit 1
}

while [ "$1" != "" ]; do
  f="${1/%.dna}"

  echo "--------------------------------------------------------------------"
  printf "%-40s" "$f"
  rm -f *.asm a.*
  cp -f "$f".dna a.dna
  ./dana a.dna > /dev/null || die
  printf "success\n"

  dosbox run.bat -exit >& /dev/null

  shift
done

rm -f *.asm a.*

exit 0
