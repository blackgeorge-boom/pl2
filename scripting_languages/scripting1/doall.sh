#! /bin/bash

start="$1"

for f in Correct/[0-9]*.dna Wrong/[0-9]*.dna ; do
  t=${f/%.dna}
  if [[ "$t" < "$start" ]]; then
    continue
  fi
  ./do.sh $t
done

exit 0
