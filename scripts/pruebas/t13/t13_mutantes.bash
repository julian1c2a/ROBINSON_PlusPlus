#!/bin/bash
# t13_mutantes.bash [SALIDA] — los mutantes de T13 (ADR-179): cada uno ROMPE una cosa del censo por entorno
# —`check-estratos.bash` de RPP o `check-axioms.bash` de FOL—, en una copia junto al original (el script hace `cd` a su
# directorio), la corre y la borra. Lo esperado: el censo mutado sigue diciendo «✓ ninguno» en la clase rota (está
# ciego), y el SEÑUELO lo dice: rojo. Desde PowerShell (`lake` en el PATH), en la raíz de RPP.
export PATH="/usr/bin:/bin:$PATH"
cd "$(dirname "$0")/../../.." || exit 2
SAL=${1:-/dev/stdout}
: > "$SAL" 2>/dev/null || true
echo "# t13_mutantes.bash, $(date -u +%Y-%m-%dT%H:%MZ), RPP $(git rev-parse --short HEAD), FOL $(git -C ../FOL rev-parse --short HEAD) (más los árboles de trabajo)" >> "$SAL"
echo >> "$SAL"
limpia() { rm -f check-estratos.mutante.bash ../FOL/check-axioms.mutante.bash; }
trap limpia EXIT INT TERM
corre() {   # $1 = repo (RPP|FOL), $2 = nombre, $3 = qué se rompe, $4 = expresión de sed
  local repo="$1" n="$2" que="$3" ex="$4" orig dest dir out rc
  if [ "$repo" = RPP ]; then orig=check-estratos.bash; dest=check-estratos.mutante.bash; dir=.
  else orig=../FOL/check-axioms.bash; dest=../FOL/check-axioms.mutante.bash; dir=../FOL; fi
  sed -E "$ex" "$orig" > "$dest"
  if [ "$n" != control ] && cmp -s "$orig" "$dest"; then echo "== $repo $n: ⚠️ EL SED NO CAMBIÓ NADA (mutante nulo): $que" >> "$SAL"; echo >> "$SAL"; return; fi
  out=$(cd "$dir" && bash "${dest##*/}" 2>&1); rc=$?
  { echo "== $repo $n (salida $rc): $que"
    printf '%s\n' "$out" | LC_ALL=C awk '/^════ (CONFIANZA|partial|SEÑUELO)/ { p = 1; print; next } /^════/ { p = 0 } p && NF' | cut -c1-170
    echo; } >> "$SAL"
}
corre RPP control 'CONTROL: sin mutar (verde)' 's/^$/&/'
corre RPP nativo-ciego 'el censo deja de ver implemented_by/extern (una API que cambia de nombre o de sentido)' \
  's/if \(Lean\.Compiler\.getImplementedBy\? env n\)\.isSome \|\| Lean\.isExtern env n then/if false then/'
corre RPP trust-como-antes 'el TRUST de antes de ADR-179: sin el auxiliar de native_decide' \
  's/ \|\| u\.components\.contains `_native\)/)/'
corre RPP trust-ajeno-ciego 'el TRUST deja de ver los axiomas AJENOS que no son de los tres de Lean (Lean.ofReduceBool…)' \
  's/\(!\(esNuestro env u\) && !\(esSenuelo env u\)\)/false/'
corre RPP partial-ciego 'el censo deja de reconocer un partial' 's/n \+\+ `_unsafe_rec/n ++ `_unsafe_recX/'
corre RPP sorry-ciego 'el censo deja de ver sorryAx' 's/if usadas\.contains ``sorryAx then/if false then/'
corre FOL control 'CONTROL: sin mutar (verde)' 's/^$/&/'
corre FOL nativo-ciego 'el censo deja de ver implemented_by/extern' \
  's/if \(Lean\.Compiler\.getImplementedBy\? env n\)\.isSome \|\| Lean\.isExtern env n then/if false then/'
corre FOL trust-como-antes 'el TRUST de antes: sin el auxiliar de native_decide' \
  's/ \|\| u\.components\.contains `_native\) then/) then/'
corre FOL trust-ajeno-ciego 'el TRUST deja de ver los axiomas AJENOS' \
  's/\(!\(esNuestro env u\) && !\(esSenuelo env u\)\)/false/'
