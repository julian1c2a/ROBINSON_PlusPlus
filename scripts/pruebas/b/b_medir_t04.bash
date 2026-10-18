#!/bin/bash
# b_medir_t04.bash DIR_SALIDA — la medición previa de T04 (doc/AUDITORIA-SUELO-2026-10-12.md), en el árbol
# (ADR‑166). Réplica del bloque [B] de check-doc-sync.bash con dos cambios que se miden por separado:
#   (1) el UNIVERSO: toda cita `X` cuyo contenido es un identificador (no sólo los siete prefijos de CAND);
#   (2) la VENTANA: el marcador sólo cuenta a ±W bytes de la cita, y sin cruzar una celda de tabla (`|`).
# Los nombres de Lean salen de `lake env lean scripts/VolcarEntorno.lean` (desde PowerShell: lake en el PATH; ADR‑166: el volcado vive en scripts/VolcarEntorno.lean).
# Escribe en DIR_SALIDA una línea «variante|clave|cita|fichero:línea» por cita no absuelta, y un resumen.
export PATH="/usr/bin:/bin:$PATH"
OUT=$1
cd "$(dirname "$0")/../../.." || exit 2
mkdir -p "$OUT"
ENV_NOMBRES=$OUT/env.txt
VOLCADO="$ENV_NOMBRES" lake env lean scripts/VolcarEntorno.lean > /dev/null || { echo "no pude volcar los nombres de Lean"; exit 2; }
DEAD_MARKER='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|F7a|histórico|ANTERIORES|🗑️|muert|Aquí vivía|tampoco existe|inexistente|desapareci|ya no son|se borró'
DEAD_MARKER="$DEAD_MARKER"'|propuest|candidat|hipot(e|é)tic|har(i|í)a falta|si se |habr(i|í)a que|añadir |descartad|no existe|NO EXISTE|sin materializar'
MD='|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la'
FECHA='|20[0-9][0-9]-[0-9][0-9]-[0-9][0-9]'
DECL_RE="(^|[^A-Za-z0-9_'.])(theorem|lemma|def|abbrev|axiom|opaque|instance|structure|inductive|class) +[^[:space:]:({[]+"
NOMBRES='{n = $NF; sub(/[.]$/, "", n); if (n == "") next; print n; k = n; sub(/.*[.]/, "", k); if (k != n && k != "") print k}'
DECLS=$OUT/decls.txt; DECLS_SOND=$OUT/decls_sond.txt
find ROBINSON_PlusPlus/ ROBINSON_PlusPlus.lean cuarentena/ ../FOL/FOL/ ../FOL/TheoryFramework/ ../FOL/FOL.lean -name '*.lean' ! -path '*/.lake/*' -print0 2>/dev/null \
  | xargs -0 env LC_ALL=C awk -f strip-lean.awk | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C sort -u > "$DECLS"
find sondeos/ -name '*.lean' 2>/dev/null | sort | while IFS= read -r f; do
  LC_ALL=C awk -f strip-lean.awk "$f" | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C awk -v f="$f" '{print $0 "|" f}'
done | LC_ALL=C sort -u > "$DECLS_SOND"
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
AUTHORITATIVE="$AUTHORITATIVE TEOREMAS-E-HIPOTESIS.md $(ls doc/REFERENCE-*.md 2>/dev/null) cuarentena/README.md sondeos/README.md"
B_DOCS=""; for d in $AUTHORITATIVE; do [ -f "$d" ] && B_DOCS="$B_DOCS $d"; done
# los MÓDULOS que existen hoy (sus nombres de fichero, sin `.lean`): las librerías, sondeos/ y cuarentena/, de RPP y de FOL
MODULOS=$OUT/modulos.txt
{ git ls-files "*.lean"; git -C ../FOL ls-files "*.lean"; } | sed "s|.*/||; s|[.]lean$||" | LC_ALL=C sort -u > "$MODULOS"

# variante: «universo|marcadores|ventana» — universo: cand (los 7 prefijos) o todo; ventana: 0 = la línea entera
for V in "cand|full|0" "cand|full|100" "cand|nofecha|100" "todo|full|0" "todo|full|100" "decl|full|0" "decl|full|100" "decl|nofecha|100"; do
  U=${V%%|*}; R=${V#*|}; M=${R%%|*}; W=${R#*|}
  MK="$DEAD_MARKER$MD"; [ "$M" = "full" ] && MK="$MK$FECHA"
  LC_ALL=C awk -v MARK="$MK" -v UNI="$U" -v W="$W" -v VAR="$V" '
    BEGIN {
      L = "([A-Za-z_]|[\303-\337][\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])"
      C = "([A-Za-z0-9_'"'"'!?]|[\303-\337][\200-\277]|\342(\202|\204|\205|\261)[\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])"
      IDENT = "^" L C "*([.]" L C "*)*$"
      CAND = "^([A-Z][A-Za-z0-9_]*[.])*(prf_|pcc_|goedel_|godel|d[123]_|repr_|ax_)"
    }
    FILENAME == ARGV[1] { vivo[$0] = 1; next }
    FILENAME == ARGV[2] { split($0, e2, "	"); env[e2[1]] = 1; if (e2[2] == "P") { u = e2[1]; sub(/.*[.]/, "", u); ult[u] = 1 }; next }
    FILENAME == ARGV[4] { modulo[$0] = 1; next }
    FILENAME == ARGV[3] { p = index($0, "|"); k = substr($0, 1, p - 1); sond[k] = sond[k] "|" substr($0, p + 1); next }
    FNR == 1 { fence = 0 }
    /^[ \t]*```/ { fence = !fence; next }
    fence { next }
    {
      s = $0; off = 0
      while (match(s, /`[^`]+`/)) {
        t = substr(s, RSTART + 1, RLENGTH - 2); ini = off + RSTART; fin = off + RSTART + RLENGTH - 1
        off = off + RSTART + RLENGTH - 1; s = substr(s, RSTART + RLENGTH)
        if (t !~ IDENT) continue
        if (t ~ /[.](lean|md|bash|py|txt|json|yml|yaml|tsv|csv|olean|awk|ps1|htm|html|tex|pdf|sh)$/) continue
        if (UNI == "cand" && t !~ CAND) continue
        if (UNI == "decl" && (length(t) < 3 || t ~ /^[a-z]+$/)) continue
        k = t; sub(/^([A-Z][A-Za-z0-9_]*[.])*/, "", k)
        if (k ~ /^ax_[A-Z]/) continue
        n_cit++
        if ((t in vivo) || (k in vivo)) { n_vivo++; continue }
        if (t in env) { n_env++; continue }
        if (UNI == "decl" && (k in ult)) { n_ult++; continue }
        if (UNI == "decl" && (t in modulo)) { n_mod++; continue }
        if (k ~ /_$/) {
          if (!(k in fam)) { fam[k] = 0; for (v in vivo) if (index(v, k) == 1) { fam[k] = 1; break } }
          if (fam[k]) { n_vivo++; continue }
        }
        # el marcador: en la línea entera (W = 0) o en la ventana [ini - W, fin + W] sin cruzar un `|`
        l = $0
        if (W > 0) {
          a = ini - W; if (a < 1) a = 1
          b = fin + W; if (b > length(l)) b = length(l)
          izq = substr(l, a, ini - a); der = substr(l, fin + 1, b - fin)
          q = 0; while ((p = index(substr(izq, q + 1), "|")) > 0) q += p
          if (q > 0) izq = substr(izq, q + 1)
          p = index(der, "|"); if (p > 0) der = substr(der, 1, p - 1)
          l = izq "``" der
        }
        gsub(/`[^`]+`/, "``", l)
        if (l ~ MARK) { n_marca++; continue }
        if (k in sond) {
          nf = split(substr(sond[k], 2), fs, "|"); ex = 0
          for (q2 = 1; q2 <= nf; q2++) { bb = fs[q2]; sub(/[.]lean$/, "", bb); if (match($0, bb "([^A-Za-z0-9_]|$)")) ex = 1 }
          if (ex) { n_sond++; continue }
        }
        muertas[k] = 1; n_muerta++
        print VAR "|" k "|" t "|" FILENAME ":" FNR
      }
    }
    END {
      nk = 0; for (k in muertas) nk++
      printf "RESUMEN %s: citas %d · vivas en el proyecto %d · vivas en Lean %d · constructor o campo %d · módulo %d · absueltas por marcador %d · por su sondeo %d · NO absueltas %d (%d claves)\n", VAR, n_cit, n_vivo, n_env, n_ult, n_mod, n_marca, n_sond, n_muerta, nk > "/dev/stderr"
    }' "$DECLS" "$ENV_NOMBRES" "$DECLS_SOND" "$MODULOS" $B_DOCS
done > "$OUT/citas.txt" 2> "$OUT/resumen.txt"
cat "$OUT/resumen.txt"
