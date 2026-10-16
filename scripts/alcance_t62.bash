#!/bin/bash
# alcance_t62.bash — el RADIO TEXTUAL de T62: cuántas declaraciones del build nombran EN SU FUENTE (sin comentarios ni
# literales: strip-lean.awk) la teoría, el verificador y las reglas. ADR-144, con sondeos/AlcanceT62.lean.
#
# Por qué un recuento textual además del de Lean: el término elaborado de una prueba de `a ∈ axioms` hecha con
# `simp [axioms]` lleva la lista ENTERA desplegada (el de `prf_add_zero_t`, tres líneas, nombra los 22 `ax_vpf_*`), así que
# «nombrar `ax_vpf_thy`» en el término no quiere decir que el fuente lo nombre (sondeos/AlcanceT62.lean lo mide y lo dice). Lo que un cambio de firma obliga
# a EDITAR es lo que nombra el fuente. Una línea cuenta para la declaración que la contiene: la última cabecera
# (`theorem`, `def`, `lemma`, `abbrev`, `instance`, `inductive`, `structure`, `opaque`, `axiom`) por encima de ella.
# Se excluyen las órdenes `#print axioms`.
#
# Uso, desde la raíz de RPP: bash scripts/alcance_t62.bash  →  doc/registro/2026-10-16-t62-alcance/textual.txt
set -euo pipefail
cd "$(dirname "$0")/.."
[ -d /usr/bin ] && export PATH="/usr/bin:/bin:$PATH"
OUT=doc/registro/2026-10-16-t62-alcance/textual.txt
mkdir -p "$(dirname "$OUT")"
B="(^|[^A-Za-z0-9_'ᵢ])"   # frontera izquierda (el punto vale: `Axioms.axioms`)
E="([^A-Za-z0-9_'ᵢ]|$)"
GRUPOS=(
  "G1 la lista de axiomas|${B}(axioms|axiomsBase|coreAxioms|codingAxioms)${E}"
  "G2 el código de la teoría y su ancla|${B}(axiomsCodeT|axD|psiD|nD|deltaD|ax_axiomsCodeT_def)${E}"
  "G3 el verificador objeto|${B}(lineWF|lineOk|chainOk|provFormulaC'|provCodeC')${E}"
  "G4 los 25 axiomas del verificador|${B}(ax_lineWF_[A-Za-z0-9_]+|ax_chainOk_nil|ax_chainOk_cons)${E}"
  "G4b sólo ax_lineWF_thy|${B}ax_lineWF_thy${E}"
  "G5 la regla thy (Prfᵢ.thy y prf_ax)|(Prfᵢ[.]thy|${B}prf_ax${E})"
  "G6 las reglas ind, listInd y p3 (constructores y reglas derivadas)|(${B}(Prf|PrfH|Rule)[.](p3|ind|listInd)${E}|${B}(prf_nat_induction|prf_list_induction)${E})"
  "G7 el verificador antiguo (ax_vpf_*, validProofFn)|${B}(ax_vpf_[A-Za-z0-9_]+|validProofFn)${E}"
  "G8 el verificador en el modelo|${B}(lineWFT|lineWFN|chainOkL|chainOkN)${E}"
)
FICH=$(find ROBINSON_PlusPlus ROBINSON_PlusPlus.lean -name '*.lean' | sort)
{
  echo "RADIO TEXTUAL de T62 — $(date +%F), scripts/alcance_t62.bash (sobre el código despojado de comentarios y literales)"
  echo "grupo | declaraciones que lo nombran | líneas que lo nombran | ficheros"
  for g in "${GRUPOS[@]}"; do
    nom=${g%%|*}; re=${g#*|}
    tmp=$(mktemp)
    for f in $FICH; do
      LC_ALL=C awk -f strip-lean.awk "$f" | awk -v F="$f" -v RE="$re" '
        /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|partial|unsafe|nonrec)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque|axiom)[[:space:]]/ { d = NR }
        /^[[:space:]]*#print[[:space:]]+axioms/ { next }
        $0 ~ RE { print F ":" (d ? d : 0) }' >> "$tmp"
    done
    nl=$(wc -l < "$tmp" | tr -d ' ')
    nd=$(sort -u "$tmp" | wc -l | tr -d ' ')
    nf=$(cut -d: -f1 "$tmp" | sort -u | wc -l | tr -d ' ')
    echo "$nom | $nd | $nl | $nf"
    rm -f "$tmp"
  done
} > "$OUT"
cat "$OUT"
