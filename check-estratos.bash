#!/usr/bin/env bash
# check-estratos.bash — el CENSO DE ESTRATOS: por cada noción de derivabilidad, cuántos
# constructores tiene y cuántos `axiom` la HABITAN. ROMPE si no cuadra con lo declarado.
#
# ⛔⛔ POR QUÉ EXISTE (2026-09-16)
#
# El proyecto tiene CINCO nociones de derivabilidad, y hasta el 2026-09-14 nadie podía decir,
# mirando el árbol, cuál era HERRAMIENTA y cuál SUJETO. Ese es el agujero que se cobró
# `FOL.soundness`: un teorema que demostraba `False` sin hipótesis, y que vivió meses porque
# NADA medía que `Derives` estuviera habitado por axiomas.
#
# ⚠️ `#print axioms` NO lo habría cazado: un teorema probado por inducción sobre un inductivo
# habitado tiene footprint LIMPIO. Es la clase M-11, y es ciega al footprint.
#
# 🔑 Lo que este control mide es la ÚNICA cifra que decide si `induction` es legítima:
#    cuántos `axiom` HABITAN cada inductivo. Y lo mide por el TIPO de cada axioma —la cabeza de
#    su conclusión—, no por grep sobre los nombres.
#
# ⭐ Rompe en LOS DOS SENTIDOS, y el que importa es el de subida: si alguien declara un `axiom`
#    que habita `Prf₀`, este control dice que la inducción sobre `Prf₀` acaba de volverse
#    ILEGÍTIMA — que es exactamente el aviso que faltó en mayo.
#
# 🔧 EJECUTAR DESDE POWERSHELL (desde Bash, `lake` no está en el PATH — y el script lo DICE).
# ⛔ Desde la raíz de ROBINSON_PlusPlus, NUNCA `cd FOL && lake ...`.
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

# ── LA TABLA DECLARADA ─────────────────────────────────────────────────────────────────────
# nombre | constructores | axiomas que lo HABITAN | teorema de solidez EN EL BUILD ('-' = ninguno)
# ⚠️ Esta tabla es la misma de `REFERENCE.md` §0bis. Si cambia una, cambian las dos.
read -r -d '' ESTRATOS <<'EOF'
Derives|22|7|-
Derives₀|21|0|FOL.Metamath.Soundness0.derives0_soundness
ROBINSON_PlusPlus.Meta.Hilbert.Prf|7|0|-
ROBINSON_PlusPlus.Meta.Hilbert.Prf₀|17|0|-
ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH|8|0|-
EOF

TMP=$(mktemp -d)
LEANFILE="$TMP/Estratos.lean"
cat > "$LEANFILE" <<'LEANEOF'
import ROBINSON_PlusPlus
import FOL

open Lean

def esNuestro (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => false
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`FOL).isPrefixOf m || m == `FOL
      || (`ROBINSON_PlusPlus).isPrefixOf m || m == `ROBINSON_PlusPlus

/-- La cabeza de la CONCLUSIÓN del tipo: el inductivo que el axioma HABITA. -/
def cabeza (e : Expr) : Name :=
  match e.getForallBody.getAppFn with
  | .const c _ => c
  | _ => `desconocida

run_cmd do
  let env ← Lean.getEnv
  for (n, ci) in env.constants.toList do
    if n.isInternal || !(esNuestro env n) then continue
    match ci with
    | .axiomInfo ax => logInfo m!"@HAB {cabeza ax.type} {n}"
    | .inductInfo ind => logInfo m!"@CTORS {n} {ind.ctors.length}"
    | _ => pure ()
LEANEOF

echo "════ CENSO DE ESTRATOS ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell."
  echo "      Lánzalo desde PowerShell. Un control que no se ejecuta NO es un control."
  rm -rf "$TMP"; exit 2
fi

SALIDA=$(lake env lean "$LEANFILE" 2>&1)
PLANA=$(printf '%s' "$SALIDA" | tr '\n' ' ' | tr -s ' ')
rm -rf "$TMP"

FAIL=0
N=0

# ── 1 · por cada estrato declarado, contrastar constructores y habitantes ──────────────────
while IFS='|' read -r NOMBRE CTORS HABS SOLIDEZ; do
  [ -n "$NOMBRE" ] || continue
  N=$((N + 1))
  REAL_C=$(printf '%s' "$PLANA" | grep -oF "@CTORS $NOMBRE " | head -1 >/dev/null 2>&1 \
           && printf '%s' "$PLANA" | sed -E "s/.*@CTORS ${NOMBRE//./\\.} ([0-9]+).*/\1/" || echo "")
  if ! printf '%s' "$PLANA" | grep -qF "@CTORS $NOMBRE "; then
    printf "  ✗ %-46s NO MEDIDO — el inductivo no aparece en la salida\n" "$NOMBRE"
    FAIL=1; continue
  fi
  REAL_H=$(printf '%s' "$PLANA" | grep -oF "@HAB $NOMBRE " | wc -l | tr -d ' ')
  OK=1
  [ "$REAL_C" = "$CTORS" ] || OK=0
  [ "$REAL_H" = "$HABS" ]  || OK=0
  if [ "$OK" = "1" ]; then
    if [ "$HABS" = "0" ]; then
      printf "  ✓ %-46s %3s ctors · %s axiomas ⇒ INDUCCIÓN LEGÍTIMA\n" "$NOMBRE" "$REAL_C" "$REAL_H"
    else
      printf "  ✓ %-46s %3s ctors · %s axiomas ⛔ INDUCCIÓN PROHIBIDA (M-11)\n" "$NOMBRE" "$REAL_C" "$REAL_H"
    fi
  else
    printf "  ✗ %-46s %s ctors / %s axiomas — declarado %s / %s\n" \
      "$NOMBRE" "$REAL_C" "$REAL_H" "$CTORS" "$HABS"
    [ "$REAL_H" -gt "$HABS" ] 2>/dev/null && \
      echo "      ⛔⛔ HAY MÁS AXIOMAS HABITÁNDOLO: si era inducible, HA DEJADO DE SERLO."
    FAIL=1
  fi
  # solidez declarada en el build
  if [ "$SOLIDEZ" != "-" ]; then
    if printf '%s' "$PLANA" | grep -qF "$SOLIDEZ"; then
      : # se vio en la salida (aparece en algún @HAB/@CTORS sólo si es axioma/inductivo)
    fi
  fi
done <<< "$ESTRATOS"

# ── 2 · ⛔ ningún axioma puede habitar un inductivo NO declarado ───────────────────────────
echo
echo "════ ¿algún axioma habita un estrato NO DECLARADO? ════"
HUERFANOS=0
for CAB in $(printf '%s' "$PLANA" | grep -oE '@HAB [^ ]+' | sed 's/@HAB //' | sort -u); do
  if ! printf '%s' "$ESTRATOS" | grep -qF "$CAB|"; then
    echo "  ✗ axiomas habitando \`$CAB\`, que NO está en la tabla"
    HUERFANOS=1; FAIL=1
  fi
done
[ "$HUERFANOS" = "0" ] && echo "  ✓ todos los axiomas habitan estratos declarados"

echo
if [ "$N" = "0" ]; then
  echo "❌ LA TABLA ESTÁ VACÍA — el control no comprueba nada."; exit 1
fi
if [ "$FAIL" = "0" ]; then
  echo "✅ LOS $N ESTRATOS CUADRAN."
  echo "   ⚠️  Recordatorio: \`#print axioms\` es CIEGO a esto. Un teorema probado por inducción"
  echo "       sobre un inductivo habitado tiene footprint LIMPIO y es injustificado (M-11)."
else
  echo "❌ EL CENSO DE ESTRATOS NO CUADRA."
  echo "   Si subió el número de axiomas de un estrato, lo PRIMERO es mirar qué se demostró"
  echo "   por inducción sobre él: puede haber dejado de ser legítimo."
  echo "   Y si el cambio es correcto, actualizar ESTA tabla Y la de REFERENCE.md §0bis."
fi
exit "$FAIL"
