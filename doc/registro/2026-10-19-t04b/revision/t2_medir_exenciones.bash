#!/bin/bash
# t2: sobre los documentos REALES (copia del árbol: $1 = wt|head), las líneas con una cifra VIEJA que EXC_A/EXC_A2
# exime, y POR QUÉ alternativa. Valores verdaderos medidos hoy: 133 jobs, 116 módulos activos, 0 axiom, 0 sorry,
# 43 sondeos. Uso: bash t2_medir_exenciones.bash wt
cd "$(dirname "$0")/$1" || exit 2
export LC_ALL=${LOC:-es_ES.UTF-8}
DOCS=$(cat ../docs.list)
ALTS=('hist(o|ó)rico' 'previo' 'antes' 'era ' 'fueron' '→' '->' 'en su momento' 'entonces' 'ya no' '~' 'p\. ej' 'ejemplo' 'umbral' '(^|[^0-9-])[0-9]{1,3}-[0-9]{1,3}([^0-9-]|$)' '«[^»]*[0-9]' 'retirad')
EXC_A='hist(o|ó)rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|~|p\. ej|ejemplo|umbral|(^|[^0-9-])[0-9]{1,3}-[0-9]{1,3}([^0-9-]|$)|«[^»]*[0-9]'
NB='(\*\*)?'
H=$(mktemp); B=$(mktemp)
for d in $DOCS; do [ -e "$d" ] || continue; head -100 "$d" | sed "s|^|$d:|" >> "$H"; [ "$d" = DECISIONS.md ] || tail -n +101 "$d" | sed "s|^|$d:|" >> "$B"; done
mide () { # $1 región  $2 pat  $3 bueno  $4 etiqueta
  grep -nE "$2" "$1" | while IFS= read -r line; do
    n=$(echo "$line" | grep -oE "$2" | grep -oE "[0-9]+" | head -1)
    [ -n "$n" ] && [ "$n" != "$3" ] || continue
    echo "$line" | grep -qiE "$EXC_A|retirad" || continue
    why=""; for a in "${ALTS[@]}"; do m=$(echo "$line" | grep -oiE -e "$a" | head -1); [ -n "$m" ] && why="$why [$m]"; done
    # la palabra entera que contiene «antes» / «era »
    w=$(echo "$line" | grep -oiE "[[:alpha:]]*(antes|era )" | tr '\n' ',')
    printf '%s\t%s\t%s\t%s\t%s\n' "$4" "$n" "$why" "$w" "$(echo "$line" | cut -c1-170)"
  done
}
for reg in H B; do
  eval f=\$$reg
  echo "######## región $reg"
  mide "$f" "[0-9]+$NB jobs" 133 jobs
  mide "$f" "[0-9]+$NB módulos activos" 116 "módulos activos"
  mide "$f" "[0-9]+$NB "'`?axiom`? de Lean' 0 axiom
  mide "$f" "[0-9]+$NB sorrys?" 0 sorry
  mide "$f" "[0-9]+$NB "'`sondeos/`' 43 sondeos
done
rm -f "$H" "$B"
