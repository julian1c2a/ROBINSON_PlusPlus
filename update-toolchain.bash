#!/bin/bash
# update-toolchain.bash — PROBAR el par (RPP, FOL) con otra versión de Lean, sin tocar los árboles de trabajo
#                         y SIN COMMIT (T42, ADR‑176). El bump, si se decide, lo hace un ADR, a mano.
#
# Uso (desde PowerShell, en la raíz de RPP: `lake` y los controles se lanzan desde allí):
#   bash update-toolchain.bash                  # la última estable publicada (GitHub releases/latest)
#   bash update-toolchain.bash v4.35.0          # una versión concreta (también rc o nightly-AAAA-MM-DD)
#   bash update-toolchain.bash --check          # sólo dice si hay una estable más nueva que la del par
#   bash update-toolchain.bash v4.35.0 --salida DIR   # deja allí los registros (por defecto, un temporal)
#   bash update-toolchain.bash v4.35.0 --conservar    # no borra los árboles de prueba al acabar
#   bash update-toolchain.bash v4.35.0 --en-sitio     # en la CI: cambia `lean-toolchain` en ESTOS checkouts
#
# Qué hace (sin `--en-sitio`):
#   1. Crea dos `git worktree` HERMANOS en un directorio temporal, `ROBINSON_PlusPlus` y `FOL`, en el HEAD de cada
#      repo (lo no commiteado NO entra: se imprime de qué SHA sale cada uno). Los árboles de trabajo y sus `.lake`
#      no se tocan: un cambio de toolchain invalida todos los `.olean`, y rehacerlos aquí costaría el build entero.
#   2. Escribe la versión en los dos `lean-toolchain` (los dos repos se compilan SIEMPRE con la misma: M‑3), y
#      COMPRUEBA que el `lake` que corre usa esa versión (si no, sale con 2: la prueba no mediría nada).
#   3. Compila, desde la raíz de RPP, `@FOL/FOL` y `@FOL/TheoryFramework` y después RPP (⛔ nunca `cd FOL && lake
#      build`, que usaría el toolchain de FOL), y pasa `leanchecker` sobre los tres, como la CI.
#   4. Si compila, pasa los controles que dependen del toolchain: footprints, warnings, estratos, sorry y los
#      sondeos de control (`IteSimboloNucleo` fija con `#guard_msgs` un mensaje del núcleo: T77).
#   5. Escribe `resumen.txt` (las líneas `error:` de cada build, y el veredicto de cada control) y borra los
#      worktrees.
# Sale con 0 si todo pasa y con 1 si algo falla. NUNCA commitea, NUNCA toca `lean-toolchain` del árbol de trabajo.
#
# ✏️ 2026‑10‑20 (T42, ADR‑176): la versión anterior de este fichero leía `lean-toolchain` con su CR (en Windows la
#    comparación con la versión nueva nunca daba igual), compilaba sólo RPP, de FOL sólo avisaba, cambiaba el
#    `lean-toolchain` del árbol de trabajo (y con él sus `.olean`) y, si compilaba, COMMITEABA ella sola.
#
# ⚠️ Un bump que rompe el build casi nunca es un problema matemático: suele ser `simp`/`omega` con otra forma
#    normal, o un mensaje distinto en un `#guard_msgs`. Se arregla en la prueba concreta, no revirtiendo la matemática.

set -euo pipefail
cd "$(dirname "$0")"
RPP=$(pwd -P)

# ═══ PATH HIGIÉNICO ═════════════════════════════════════════════════════════
# ⚠️ Lanzado desde una consola de Windows, `bash` hereda un PATH en el que `head`, `grep` o `sed` pueden resolver
# a binarios AJENOS (en esta máquina, el HEAD de Quantum ESPRESSO en ucrt64). Se antepone el /usr/bin de MSYS2.
[ -d /usr/bin ] && export PATH="/usr/bin:/bin:$PATH"
# ⛔ Y los PROXIES de elan, delante de todo (medido el 2026‑10‑20, ADR‑176): en esta máquina el PATH lleva el `bin`
# de v4.31.0 ANTES que `~/.elan/bin`, y con ese `lake` cambiar `lean-toolchain` no cambia nada: la primera prueba de
# v4.35.0 compiló y pasó todos los controles… con v4.31.0. Por eso, además, se COMPRUEBA abajo la versión que corre.
ELAN_BIN="${ELAN_HOME:-$HOME/.elan}/bin"
[ -d "$ELAN_BIN" ] && export PATH="$ELAN_BIN:$PATH"

TARGET=""; CHECK_ONLY=0; EN_SITIO=0; CONSERVAR=0; SALIDA=""
while [ $# -gt 0 ]; do
    case "$1" in
        --check) CHECK_ONLY=1 ;;
        --en-sitio) EN_SITIO=1 ;;
        --conservar) CONSERVAR=1 ;;
        --salida) shift; SALIDA="$1" ;;
        -*) echo "❌ opción desconocida: $1" >&2; exit 2 ;;
        *) TARGET="$1" ;;
    esac
    shift
done

# `tr -d '\r'`: con autocrlf, el fichero llega con CR y la comparación de abajo no daba nunca «igual».
CURRENT=$(tr -d '\r' < lean-toolchain)
CURRENT_FOL=$(tr -d '\r' < ../FOL/lean-toolchain)
if [ "$CURRENT" != "$CURRENT_FOL" ]; then
    echo "⚠️  El par NO está en la misma versión: RPP $CURRENT, FOL $CURRENT_FOL (M‑3)."
fi

if [ -z "$TARGET" ]; then
    TARGET=$(curl -fsSL https://api.github.com/repos/leanprover/lean4/releases/latest \
        | sed -n 's/.*"tag_name": *"\([^"]*\)".*/\1/p' | head -1)
    if [ -z "$TARGET" ]; then
        echo "❌ No se pudo obtener la última estable (¿sin red o límite de la API?)." >&2
        exit 2
    fi
fi
case "$TARGET" in
    nightly-*) NEW="leanprover/lean4-nightly:$TARGET" ;;
    *) NEW="leanprover/lean4:$TARGET" ;;
esac

echo "El par:   $CURRENT"
echo "Objetivo: $NEW"
if [ "$NEW" = "$CURRENT" ]; then
    echo "✅ El par ya está en $TARGET."
    exit 0
fi
if [ "$CHECK_ONLY" -eq 1 ]; then
    echo "ℹ️  Hay otra versión: $TARGET (sin --check, se prueba en árboles aparte; nada se commitea)."
    exit 0
fi

# ── El toolchain: se instala si falta (la versión anterior ABORTABA si ya estaba instalado) ──
if ! elan toolchain list 2>/dev/null | tr -d '\r' | grep -Fq "$NEW"; then
    echo "Instalando $NEW..."
    elan toolchain install "$NEW"
fi

# ── Los árboles de prueba ───────────────────────────────────────────────────
if [ "$EN_SITIO" -eq 1 ]; then
    BASE=$(cd .. && pwd -P)
else
    BASE=$(mktemp -d "${TMPDIR:-/tmp}/tcprueba.XXXXXX")
    git -C "$RPP" worktree add --detach "$BASE/ROBINSON_PlusPlus" HEAD >/dev/null 2>&1
    git -C "$RPP/../FOL" worktree add --detach "$BASE/FOL" HEAD >/dev/null 2>&1
fi
[ -n "$SALIDA" ] || SALIDA="$BASE/registro"
mkdir -p "$SALIDA"
SALIDA=$(cd "$SALIDA" && pwd -P)

limpiar() {
    if [ "$EN_SITIO" -eq 0 ] && [ "$CONSERVAR" -eq 0 ]; then
        git -C "$RPP" worktree remove --force "$BASE/ROBINSON_PlusPlus" >/dev/null 2>&1 || true
        git -C "$RPP/../FOL" worktree remove --force "$BASE/FOL" >/dev/null 2>&1 || true
    fi
}
trap limpiar EXIT

RES="$SALIDA/resumen.txt"
{
    echo "Prueba del toolchain $NEW (el par estaba en $CURRENT) — $(date -u '+%Y-%m-%d %H:%M UTC')"
    echo "RPP @ $(git -C "$BASE/ROBINSON_PlusPlus" rev-parse --short HEAD) · FOL @ $(git -C "$BASE/FOL" rev-parse --short HEAD)"
    echo "Árboles: $BASE ($( [ "$EN_SITIO" -eq 1 ] && echo 'en sitio' || echo 'worktrees aparte'))"
    echo
} > "$RES"

echo "$NEW" > "$BASE/ROBINSON_PlusPlus/lean-toolchain"
echo "$NEW" > "$BASE/FOL/lean-toolchain"

cd "$BASE/ROBINSON_PlusPlus"
FALLOS=0

# ⛔ La versión que de verdad corre: si no es la pedida, la prueba no mide nada (sale con 2, sin compilar).
CORRE=$(lake env lean --version 2>&1 | tr -d '\r' | head -1)
echo "Lean que corre: $CORRE" | tee -a "$RES"
case "$CORRE" in
    *"version ${TARGET#v}"*|*"$TARGET"*) ;;
    *) echo "❌ corre OTRA versión (se pedía $TARGET): la prueba no mediría nada." | tee -a "$RES"; exit 2 ;;
esac

paso() {   # paso NOMBRE FICHERO-DE-LOG comando…
    local nombre="$1" log="$2"; shift 2
    local t0=$(date +%s)
    if "$@" > "$log" 2>&1; then
        echo "✓ $nombre ($(( $(date +%s) - t0 )) s)" | tee -a "$RES"
        return 0
    else
        echo "✗ $nombre ($(( $(date +%s) - t0 )) s) — ${log##*/}" | tee -a "$RES"
        grep -E '(^|: )error' "$log" | head -40 | sed 's/^/    /' >> "$RES" || true
        FALLOS=$((FALLOS + 1))
        return 1
    fi
}

BUILD_OK=1
paso "build de FOL (@FOL/FOL @FOL/TheoryFramework)" "$SALIDA/build-fol.log" \
    lake build "@FOL/FOL" "@FOL/TheoryFramework" || BUILD_OK=0
if [ "$BUILD_OK" -eq 1 ]; then
    paso "build de RPP" "$SALIDA/build-rpp.log" lake build || BUILD_OK=0
fi
if [ "$BUILD_OK" -eq 1 ]; then
    paso "leanchecker (el núcleo, otra vez, sobre los tres)" "$SALIDA/leanchecker.log" \
        lake env leanchecker ROBINSON_PlusPlus FOL TheoryFramework || true
fi

if [ "$BUILD_OK" -eq 1 ]; then
    for c in check-footprints.bash check-warnings.bash check-estratos.bash check-sorry.bash; do
        paso "$c" "$SALIDA/${c%.bash}.log" bash "$c" || true
    done
    paso "check-sondeos.bash --controles" "$SALIDA/check-sondeos.log" bash check-sondeos.bash --controles || true
else
    echo "— los controles no se pasan: el build no compila" | tee -a "$RES"
fi

echo | tee -a "$RES"
if [ "$FALLOS" -eq 0 ]; then
    echo "✅ $NEW: el par compila y los controles pasan. El bump, si se decide, va por un ADR." | tee -a "$RES"
else
    echo "❌ $NEW: $FALLOS paso(s) fallan. Registros en $SALIDA." | tee -a "$RES"
fi
echo "Resumen: $RES"
[ "$FALLOS" -eq 0 ]
