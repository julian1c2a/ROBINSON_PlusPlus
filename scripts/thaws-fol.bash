#!/bin/bash
# scripts/thaws-fol.bash — cada THAW de FOL lo autorizó el propietario, por escrito, en un ADR de RPP; y el que se dijo
# «de sólo prosa» lo fue (T14, ADR-234).
#
# Un THAW es un commit de FOL que saca una entrada de su frozen_files.txt: descongela un módulo terminado, y eso sólo
# lo decide el propietario. Ningún control lo comprobaba (ADR-212 §1 lo dejó abierto: «un thaw sin control del
# propietario»). Nadie puede comprobar la VOLUNTAD del propietario, pero sí que esté ESCRITA:
#   1. Recorre la historia ENTERA de ../FOL/frozen_files.txt y lista los thaws (las entradas que salen, por commit).
#   2. Cada uno tiene que apoyarse en un ADR de RPP que EXISTA (su sección «## ADR-NNN:», en DECISIONS.md o en
#      doc/historia/DECISIONS-001-130.md) y que recoja una decisión (la palabra «propietario» o, en los antiguos,
#      «usuario»). El ADR sale del MENSAJE del commit («ADR-NNN de RPP», lo que exigen desde ADR-234 el gancho
#      commit-msg y check-congelados.bash de FOL) o, para los thaws de antes de la regla que no lo citan, de
#      doc/control/thaws-fol.tsv, revisada a mano y con fecha anterior a la regla.
#   3. El ALCANCE de cada fila de la tabla (prosa | código) se vuelve a medir con scripts/prosa.py, fichero a fichero:
#      «prosa» si NINGÚN fichero descongelado cambió de código (comentarios y docstrings fuera, literales dentro).
#      Tiene que ser el declarado, en los dos sentidos.
#   4. La tabla, exacta: una fila por thaw sin ADR en su mensaje, ni una de más, ninguna posterior a la regla.
#   5. La herramienta de congelación es la MISMA en los dos repos: git-lock.bash, .githooks/pre-commit y
#      .githooks/commit-msg, byte a byte (salvo los finales de línea).
# Sale con 0 si todo cuadra, 1 si no, 2 si no puede medir (sin ../FOL, un clon superficial, el autotest).
# ⚠️ La ventana de M-12: un thaw de FOL cita un ADR que llega a RPP DESPUÉS (FOL sube primero): hasta que llega, la
#    CI de RPP lanzada por el push de FOL sale roja aquí. Es la misma ventana de ADR-217 §9.
export PATH="/usr/bin:$PATH"
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

FOL=${1:-../FOL}
TABLA=doc/control/thaws-fol.tsv
REGLA=2026-10-31     # desde ADR-234, un thaw cita su ADR en el mensaje: la tabla no puede tener filas de esta fecha o más
PY=$(command -v python3 || true)
[ -n "$PY" ] || { echo "❌ NO PUEDO MEDIR: no hay python3 (scripts/prosa.py)"; exit 2; }

[ -d "$FOL/.git" ] || git -C "$FOL" rev-parse --git-dir > /dev/null 2>&1 \
  || { echo "❌ NO PUEDO MEDIR: no encuentro el repositorio de FOL en $FOL"; exit 2; }
if [ "$(git -C "$FOL" rev-parse --is-shallow-repository 2> /dev/null)" = true ]; then
  echo "❌ NO PUEDO MEDIR: $FOL es un clon superficial (sin la historia de frozen_files.txt): fetch-depth: 0"
  exit 2
fi
[ -s "$TABLA" ] || { echo "❌ NO PUEDO MEDIR: falta $TABLA"; exit 2; }
"$PY" scripts/prosa.py autotest > /dev/null || { echo "❌ NO PUEDO MEDIR: el autotest de scripts/prosa.py falla"; exit 2; }

# adr_decide <número> → 0 si su sección existe y recoge una decisión del propietario
adr_texto() {
  local a="## ADR-$1:"
  cat DECISIONS.md doc/historia/DECISIONS-001-130.md 2> /dev/null \
    | awk -v a="$a" '/^## / { en = (index($0, a) == 1) } en'
}
adr_decide() {
  local t
  t=$(adr_texto "$1")
  [ -n "$t" ] || return 1
  grep -qiE 'propietario|usuario' <<< "$t"
}
# adrs_de <texto> → los números de los ADR que el texto cita COMO AUTORIZACIÓN, uno por línea: los de una frase
# «ADR-NNN de RPP» («ADR-227 y ADR-229 de RPP»), con la MISMA expresión que el gancho commit-msg y check-congelados.bash
# de FOL. Otro ADR nombrado de paso en el mensaje (un antecedente, un ADR de FOL) no cuenta.
THAW_RE='ADR(-|‑)[0-9]+(( y |, )ADR(-|‑)[0-9]+)* de RPP'
adrs_de() { grep -oE "$THAW_RE" <<< "$1" | grep -oE '[0-9]+' | sort -u; }

# autotest: un ADR que existe y decide, uno que no existe, y el texto de un mensaje con dos
AUTO=""
adr_decide 227 && AUTO="${AUTO}s" || AUTO="${AUTO}n"
adr_decide 99999 && AUTO="${AUTO}s" || AUTO="${AUTO}n"
AUTO="$AUTO$(adrs_de 'Thaw autorizado (ADR-227 y ADR‑229 de RPP); antes, ADR-041 y ADR-010' | tr '\n' ',')"
if [ "$AUTO" != "sn227,229," ]; then
  echo "❌ NO PUEDO MEDIR: el autotest da «$AUTO» y debía dar «sn227,229,»"
  exit 2
fi

FALLO=0
DECL=$(grep -v '^#' "$TABLA" | tr -d '\r' | grep .)
VISTOS=""
N=0
echo "════ los thaws de FOL (toda la historia de frozen_files.txt) ════"
for c in $(git -C "$FOL" log --format=%H -- frozen_files.txt); do
  git -C "$FOL" cat-file -e "$c^" 2> /dev/null || continue
  QUITA=$(git -C "$FOL" diff --no-renames --unified=0 "$c^" "$c" -- frozen_files.txt | tr -d '\r' | grep '^-[^-]' \
          | sed 's/^-//' || true)
  [ -n "$QUITA" ] || continue
  N=$((N + 1))
  corto=$(git -C "$FOL" rev-parse --short=7 "$c")
  fecha=$(git -C "$FOL" log -1 --format=%ad --date=short "$c")
  msg=$(git -C "$FOL" log -1 --format=%B "$c")
  fila=$(awk -F'\t' -v s="$corto" '$1 == s' <<< "$DECL")
  # el alcance, medido: prosa si ningún fichero descongelado cambió de código
  alc=prosa
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    case "$f" in *.lean) ;; *) continue ;; esac
    if ! git -C "$FOL" cat-file -e "$c:$f" 2> /dev/null; then alc=código; continue; fi   # borrado o movido
    "$PY" scripts/prosa.py git "$FOL" "$c" "$f" > /dev/null 2>&1
    case $? in 0) ;; 1) alc=código ;; *) echo "  ❌ $corto: no pude medir $f con scripts/prosa.py"; FALLO=1 ;; esac
  done <<< "$QUITA"
  nf=$(grep -c . <<< "$QUITA")
  # la autorización: los ADR del mensaje; si no cita ninguno que decida, el de la tabla
  ok=""
  for n in $(adrs_de "$msg"); do adr_decide "$n" && ok="${ok}ADR-$n "; done
  if [ -n "$ok" ]; then
    if [ -n "$fila" ]; then
      echo "  ❌ $corto: su mensaje ya cita su ADR (${ok% }): la fila de $TABLA sobra"
      FALLO=1
    else
      echo "  ✓ $corto $fecha · $nf descongelados · $alc · ${ok% } (en el mensaje)"
    fi
  elif [ -n "$fila" ]; then
    VISTOS="$VISTOS $corto"
    t_fecha=$(cut -f2 <<< "$fila"); t_adr=$(cut -f3 <<< "$fila"); t_alc=$(cut -f4 <<< "$fila")
    n=$(grep -oE '[0-9]+$' <<< "$t_adr")
    if [ "$t_fecha" != "$fecha" ]; then
      echo "  ❌ $corto: la tabla dice $t_fecha y el commit es del $fecha"; FALLO=1
    elif [[ ! "$t_fecha" < "$REGLA" ]]; then
      echo "  ❌ $corto: un thaw del $t_fecha no va en la tabla: desde el $REGLA cita su ADR en el mensaje"; FALLO=1
    elif [ -z "$n" ] || ! adr_decide "$n"; then
      echo "  ❌ $corto: la tabla da «$t_adr», que no existe o no recoge una decisión del propietario"; FALLO=1
    elif [ "$t_alc" != "$alc" ]; then
      echo "  ❌ $corto: la tabla dice «$t_alc» y lo medido es «$alc»"; FALLO=1
    else
      echo "  ✓ $corto $fecha · $nf descongelados · $alc · $t_adr (en $TABLA)"
    fi
  else
    echo "  ❌ $corto $fecha: ni su mensaje cita un ADR de RPP que exista y recoja la decisión, ni está en $TABLA"
    echo "      $(head -1 <<< "$msg" | cut -c1-110)"
    FALLO=1
  fi
done
# las filas que no son un thaw (o sobran)
while IFS=$'\t' read -r s _; do
  [ -n "$s" ] || continue
  case " $VISTOS " in *" $s "*) ;; *) echo "  ❌ la fila «$s» de $TABLA no es un thaw sin ADR en su mensaje"; FALLO=1 ;; esac
done <<< "$DECL"
[ "$N" -gt 0 ] || { echo "  ❌ SIN MEDIR: no encontré ningún thaw en la historia de $FOL/frozen_files.txt"; exit 2; }

echo "════ la herramienta de congelación, la misma en RPP y en FOL ════"
for f in git-lock.bash .githooks/pre-commit .githooks/commit-msg; do
  if [ ! -f "$f" ] || [ ! -f "$FOL/$f" ]; then
    echo "  ❌ falta $f en RPP o en FOL"; FALLO=1
  elif cmp -s <(tr -d '\r' < "$f") <(tr -d '\r' < "$FOL/$f"); then
    echo "  ✓ $f"
  else
    echo "  ❌ $f y $FOL/$f ya no son el mismo fichero: unifícalos"; FALLO=1
  fi
done

if [ "$FALLO" = "0" ]; then
  echo "✅ LOS $N THAWS DE FOL, AUTORIZADOS POR ESCRITO (y el alcance de la tabla, medido); la herramienta, la misma"
  exit 0
fi
echo "❌ HAY THAWS SIN AUTORIZACIÓN ESCRITA, O LA TABLA NO CUADRA"
exit 1
