#!/bin/bash
# b_medir.bash DIR_SALIDA — réplica del bloque [B] de check-doc-sync.bash con cuatro juegos de marcadores (completo,
# sin fecha, sin (d), sólo (a)+(b)): mide cuántas citas de símbolos muertos absuelve cada juego. La escribió el
# verificador de controles de la auditoría del 2026-10-05; rescatada el 2026-10-12 (ADR-132, T00), sólo con la ruta
# del repo hecha relativa. Es la medición previa de T04 (doc/AUDITORIA-SUELO-2026-10-12.md).
export PATH="/usr/bin:/bin:$PATH"
cd "$(dirname "$0")/../../.."
DEAD_MARKER='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|F7a|histórico|ANTERIORES|🗑️|muert|Aquí vivía|tampoco existe|inexistente|desapareci|ya no son|se borró'
DEAD_MARKER="$DEAD_MARKER"'|propuest|candidat|hipot(e|é)tic|har(i|í)a falta|si se |habr(i|í)a que|añadir |descartad|no existe|NO EXISTE|sin materializar|20[0-9][0-9]-[0-9][0-9]-[0-9][0-9]'
#   (d) es un OBJETIVO declarado, no una afirmación de que ya está.
DEAD_MARKER="$DEAD_MARKER"'|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la'
DECL_RE="(^|[^A-Za-z0-9_'.])(theorem|lemma|def|abbrev|axiom|opaque|instance|structure|inductive|class) +[^[:space:]:({[]+"
# el nombre entero y su último componente; `prf_univ.{u}` → `prf_univ`
NOMBRES='{n = $NF; sub(/[.]$/, "", n); if (n == "") next; print n; k = n; sub(/.*[.]/, "", k); if (k != n && k != "") print k}'
DECLS=$1/decls.txt; DECLS_SOND=$1/decls_sond.txt
find ROBINSON_PlusPlus/ ROBINSON_PlusPlus.lean cuarentena/ ../FOL/FOL/ ../FOL/TheoryFramework/ ../FOL/FOL.lean -name "*.lean" ! -path "*/.lake/*" -print0 2>/dev/null | xargs -0 env LC_ALL=C awk -f strip-lean.awk | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C sort -u > "$DECLS"
find sondeos/ -name "*.lean" 2>/dev/null | sort | while IFS= read -r f; do LC_ALL=C awk -f strip-lean.awk "$f" | LC_ALL=C grep -oE "$DECL_RE" | LC_ALL=C awk "$NOMBRES" | LC_ALL=C awk -v f="$f" "{print \$0 \"|\" f}"; done | LC_ALL=C sort -u > "$DECLS_SOND"
AUTHORITATIVE="REFERENCE.md CURRENT-STATUS-PROJECT.md DEPENDENCIES.md DECISIONS.md README.md AXIOMS.md GODEL-STATUS.md NEXT-STEPS.md"
AUTHORITATIVE="$AUTHORITATIVE $(ls doc/REFERENCE-*.md 2>/dev/null) cuarentena/README.md sondeos/README.md"
# (2026-10-14, ADR-135: check-doc-sync.bash añadió TEOREMAS-E-HIPOTESIS.md a su AUTHORITATIVE; esta réplica es la
#  de la medición de T04, del 2026-10-12, y se deja como estaba: al repetir la medición, añadirlo aquí también.)
# Marcadores que hacen LEGÍTIMA la mención de un símbolo inexistente:
B_DOCS=""; for d in $AUTHORITATIVE; do [ -f "$d" ] && B_DOCS="$B_DOCS $d"; done
MA='YA NO EXISTE|NO EXISTEN|retirad|RETIRADO|eliminad|borrad|legacy|F7a|histórico|ANTERIORES|🗑️|muert|Aquí vivía|tampoco existe|inexistente|desapareci|ya no son|se borró'
MB='|propuest|candidat|hipot(e|é)tic|har(i|í)a falta|si se |habr(i|í)a que|añadir |descartad|no existe|NO EXISTE|sin materializar'
MC='|20[0-9][0-9]-[0-9][0-9]-[0-9][0-9]'
MD='|falta|FALTA|construir|objetivo|medir|sin medir|pendiente|⏳|abiert|necesita|exige|pide|TAREA|hace falta|no hay ni habrá|sub‑familia|sub-familia|buscaba|buscó|usan la'
for VAR in full nodate nod abonly; do
  case $VAR in full) MK="$DEAD_MARKER" ;; nodate) MK="$MA$MB$MD" ;; nod) MK="$MA$MB$MC" ;; abonly) MK="$MA$MB" ;; esac
  DEAD_MARKER_USE="$MK"
  LC_ALL=C awk -v MARK="$DEAD_MARKER_USE" '
    BEGIN { CAND = "`([A-Z][A-Za-z0-9_]*[.])*(prf_|pcc_|goedel_|godel|d[123]_|repr_|ax_)([A-Za-z0-9_'"'"'!?]|[\303-\337][\200-\277]|\342(\202|\204|\205|\261)[\200-\277]|\341[\265-\277][\200-\277]|\360\235[\200-\277][\200-\277])+`" }
    FILENAME == ARGV[1] { vivo[$0] = 1; next }
    FILENAME == ARGV[2] { p = index($0, "|"); k = substr($0, 1, p - 1); sond[k] = sond[k] "|" substr($0, p + 1); next }
    {
      s = $0
      # un carácter de nombre: ASCII, o en UTF-8 una letra (2 bytes), un subíndice, un letterlike, ⱼ,
      # el griego extendido o el alfabeto matemático — NO la puntuación general (`1‑3`, `a–b`, `…`)
      while (match(s, CAND)) {
        t = substr(s, RSTART + 1, RLENGTH - 2); s = substr(s, RSTART + RLENGTH)
        k = t; sub(/^([A-Z][A-Za-z0-9_]*[.])*/, "", k)
        # los axiomas objeto son snake_case: `ax_UpperCamel` es un PLACEHOLDER de convención
        # de nombres (`ax_TagDescriptor`), no un símbolo
        if (k ~ /^ax_[A-Z]/) continue
        if ((t in vivo) || (k in vivo)) continue
        if (k ~ /_$/) {
          if (!(k in fam)) { fam[k] = 0; for (v in vivo) if (index(v, k) == 1) { fam[k] = 1; break } }
          if (fam[k]) continue
        }
        # el marcador se mira en la línea con las CITAS en blanco: un nombre muerto que contenga un
        # marcador (`prf_x_muerto`, `ax_medir`) no puede eximirse a sí mismo (tercera revisión)
        l = $0; gsub(CAND, "``", l)
        if (l ~ MARK) continue
        if (k in sond) {
          nf = split(substr(sond[k], 2), fs, "|"); ex = 0
          for (q = 1; q <= nf; q++) { b = fs[q]; sub(/[.]lean$/, "", b); if (match($0, b "([^A-Za-z0-9_]|$)")) ex = 1 }
          if (ex) continue
        }
        print k "|" t "|" FILENAME ":" FNR ":" $0
      }
    }' "$DECLS" "$DECLS_SOND" $B_DOCS > "$1/salida_$VAR.txt"
done
