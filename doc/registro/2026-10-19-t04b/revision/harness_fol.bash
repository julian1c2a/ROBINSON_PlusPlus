#!/bin/bash
# harness_fol.bash — corre VERBATIM [A] y [A2] de FOL (fol-check.bash = git show 2897e1b:check-doc-sync.bash) en <dir>.
H=$(cd "$(dirname "$0")" && pwd); SCRIPT=$H/fol-check.bash; cd "$1" || exit 2
ACTIVE=${ACTIVE-54}; QUAR=${QUAR-0}; AXIOMS=${AXIOMS-0}; SORRY=${SORRY-0}; DOCS=${DOCS-$(cat docs.list)}; FAIL=0
a=$(grep -n '════ \[A\] CIFRAS' "$SCRIPT" | cut -d: -f1); b=$(grep -n 'el cuerpo tampoco tiene cifras obsoletas' "$SCRIPT" | cut -d: -f1)
eval "$(sed -n "${a},$((b+7))p" "$SCRIPT")"
echo "FAIL=$FAIL"
