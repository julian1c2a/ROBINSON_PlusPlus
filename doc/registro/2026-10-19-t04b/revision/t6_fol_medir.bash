#!/bin/bash
# t6: lo mismo que t2, sobre los documentos de FOL (git show HEAD, 2897e1b): las cifras VIEJAS que EXC_A exime y por qué.
# Valores verdaderos medidos hoy en FOL: 54 módulos activos, 0 cuarentena, 0 axiom, 0 sorry.
cd "$(dirname "$0")/fol" || exit 2
export LC_ALL=${LOC:-es_ES.UTF-8}
ALTS=('hist(o|ó)rico' 'previo' 'antes' 'era ' 'fueron' '→' '->' 'en su momento' 'entonces' 'ya no' '~' 'p\. ej' 'ejemplo' 'umbral' '(^|[^0-9-])[0-9]{1,3}-[0-9]{1,3}([^0-9-]|$)' '«[^»]*[0-9]' 'retirad')
EXC_A='hist(o|ó)rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|~|p\. ej|ejemplo|umbral|(^|[^0-9-])[0-9]{1,3}-[0-9]{1,3}([^0-9-]|$)|«[^»]*[0-9]'
NB='(\*\*)?'
H=$(mktemp); B=$(mktemp)
for d in $(cat docs.list); do head -100 "$d" | sed "s|^|$d:|" >> "$H"; tail -n +101 "$d" | sed "s|^|$d:|" >> "$B"; done
mide () {
  grep -nE "$2" "$1" | while IFS= read -r line; do
    n=$(echo "$line" | grep -oE "$2" | grep -oE "[0-9]+" | head -1)
    [ -n "$n" ] && [ "$n" != "$3" ] || continue
    echo "$line" | grep -qiE "$EXC_A|retirad" || continue
    why=""; for a in "${ALTS[@]}"; do m=$(echo "$line" | grep -oiE -e "$a" | head -1); [ -n "$m" ] && why="$why [$m]"; done
    w=$(echo "$line" | grep -oiE "[[:alpha:]]*(antes|era )" | tr '\n' ',')
    printf '%s\t%s\t%s\t%s\t%s\n' "$4" "$n" "$why" "$w" "$(echo "$line" | cut -c1-220)"
  done
}
for reg in H B; do eval f=\$$reg; echo "######## región $reg"
  mide "$f" "[0-9]+$NB módulos activos" 54 "módulos activos"
  mide "$f" "[0-9]+$NB (módulos )?en \`cuarentena/\`" 0 cuarentena
  mide "$f" "[0-9]+$NB "'`?axiom`? de Lean' 0 axiom
  mide "$f" "[0-9]+$NB sorrys?" 0 sorry
done; rm -f "$H" "$B"
