#!/bin/sh
# Check that every statement listed in AxiomCheck.lean depends only on Lean's
# standard axioms (propext, Classical.choice, Quot.sound): no sorry and no
# added axiom.  Run after `lake build`; CI runs it on every push.
set -e
cd "$(dirname "$0")"
expected=$(grep -c '^#print axioms' AxiomCheck.lean)
lake env lean AxiomCheck.lean > axioms.txt
cat axioms.txt
std='(propext|Classical\.choice|Quot\.sound)'
bad=$(grep -v -E "depends on axioms: \[$std(, $std)*\]\$|does not depend on any axioms" axioms.txt || true)
if [ -n "$bad" ]; then
  echo "statements with non-standard axioms (or sorry):"
  echo "$bad"
  exit 1
fi
got=$(wc -l < axioms.txt | tr -d ' ')
if [ "$got" -ne "$expected" ]; then
  echo "expected $expected lines of output, got $got"
  exit 1
fi
echo "all $expected statements use only the standard axioms"
