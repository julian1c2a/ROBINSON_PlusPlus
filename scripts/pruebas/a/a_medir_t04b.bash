#!/bin/bash
# a_medir_t04b.bash JOBS SOND — la medición previa de T04b (doc/AUDITORIA-SUELO-2026-10-12.md; ADR‑169): réplica de [A] y
# [A2] de check-doc-sync.bash con cada cambio por separado: (1) sin la FECHA como exención; (2) patrones que admiten la
# negrita (`**131** jobs`); (3) la cifra de sondeos (SOND, que se calculaba y no se comparaba). Imprime, por variante,
# las líneas de la cabecera (las 100 primeras) y del cuerpo cuya cifra no cuadra. JOBS y SOND: las cifras de hoy.
export PATH="/usr/bin:/bin:$PATH"
cd "$(dirname "$0")/../../.." || exit 2
JOBS=$1; SOND=$2
AUTH="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
AUTH="$AUTH TEOREMAS-E-HIPOTESIS.md $(ls doc/REFERENCE-*.md 2>/dev/null) cuarentena/README.md sondeos/README.md"
EXC_CON_FECHA='hist[oó]rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|20[0-9]{2}-[0-9]{2}-[0-9]{2}|~|p\. ej|ejemplo|umbral|[0-9]+-[0-9]+'
EXC_SIN_FECHA='hist[oó]rico|previo|antes|era |fueron|→|->|en su momento|entonces|ya no|~|p\. ej|ejemplo|umbral|[0-9]+-[0-9]+'
mide() {   # $1 = región (cab|cuerpo)  $2 = exención  $3 = regex  $4 = valor  $5 = etiqueta
  for d in $AUTH; do
    [ -f "$d" ] || continue
    if [ "$1" = cab ]; then head -100 "$d"; else tail -n +101 "$d"; fi | sed "s|^|$d:|"
  done | grep -nE "$3" | grep -viE "$2" | while IFS= read -r l; do
    n=$(printf '%s' "$l" | grep -oE "$3" | grep -oE '[0-9]+' | head -1)
    [ -n "$n" ] && [ "$n" != "$4" ] && echo "  $5: dice $n, real $4 :: ${l:0:140}"
  done
}
for V in "cab|con|plano" "cab|sin|plano" "cab|sin|negrita" "cuerpo|con|plano" "cuerpo|sin|negrita"; do
  REG=${V%%|*}; R=${V#*|}; F=${R%%|*}; P=${R#*|}
  EXC=$EXC_CON_FECHA; [ "$F" = sin ] && EXC=$EXC_SIN_FECHA
  B=''; [ "$P" = negrita ] && B='(\*\*)?'
  echo "== $REG · exención $F fecha · patrones $P"
  { mide "$REG" "$EXC" "[0-9]+$B jobs" "$JOBS" jobs
    mide "$REG" "$EXC" "[0-9]+$B (sondeos|ficheros en \`?sondeos/)" "$SOND" sondeos; } > "${TMPDIR:-/tmp}/a_medir.$$"
  cat "${TMPDIR:-/tmp}/a_medir.$$"; echo "  total: $(grep -c . "${TMPDIR:-/tmp}/a_medir.$$")"; rm -f "${TMPDIR:-/tmp}/a_medir.$$"
done
