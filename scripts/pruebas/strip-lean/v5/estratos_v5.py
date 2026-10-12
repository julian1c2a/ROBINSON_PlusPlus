# estratos_v5.py — RPP/check-estratos.bash tras la cuarta revisión: en el ENTORNO, @TRUST (axiomas de
# confianza del core usados por constantes nuestras), @NATIVO (implemented_by / extern) y @AJENO (módulos de
# librerías que ningún censo mira).
import io
P = 'E:/dropbox/github/lean4/ROBINSON_PlusPlus/check-estratos.bash'
s = io.open(P, encoding='utf-8', newline='').read()
assert '\r\n' not in s

def rep(old, new, tag, n=1):
    global s
    c = s.count(old)
    assert c == n, (tag, c, old[:90])
    s = s.replace(old, new)

rep('''{
  echo "import ROBINSON_PlusPlus"
  echo "import FOL"''', '''{
  echo "import Lean"
  echo "import ROBINSON_PlusPlus"
  echo "import FOL"''', 'import')
rep('''run_cmd do
  let env ← Lean.getEnv
  let mut tf := 0
  let mut nuestras := 0
  for (n, ci) in env.constants.toList do''', '''run_cmd do
  let env ← Lean.getEnv
  let mut tf := 0
  let mut nuestras := 0
  -- los tres axiomas de Lean que el proyecto acepta; cualquier OTRO axioma ajeno que use una constante
  -- nuestra (`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, …) es @TRUST
  let estandar : NameSet := ((({} : NameSet).insert ``propext).insert ``Classical.choice).insert ``Quot.sound
  for (n, ci) in env.constants.toList do''', 'head')
rep('''    -- tipo y valor, también el de un teorema (`getUsedConstantsAsSet` lee con `allowOpaque`)
    if ci.getUsedConstantsAsSet.contains ``sorryAx then logInfo m!"@SORRY {n}"
  logInfo m!"@TF {tf}"
  logInfo m!"@NUESTRAS {nuestras}"''', '''    -- tipo y valor, también el de un teorema (`getUsedConstantsAsSet` lee con `allowOpaque`)
    let usadas := ci.getUsedConstantsAsSet
    if usadas.contains ``sorryAx then logInfo m!"@SORRY {n}"
    for u in usadas do
      if let some (.axiomInfo _) := env.find? u then
        if !estandar.contains u && u != ``sorryAx && !(esNuestro env u) then logInfo m!"@TRUST {n} {u}"
    if (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n then logInfo m!"@NATIVO {n}"
  logInfo m!"@TF {tf}"
  logInfo m!"@NUESTRAS {nuestras}"
  -- ¿alguna librería cargada que ningún censo mira? (una nueva, importada por FOL o por RPP, quedaría fuera)
  for m in env.header.moduleNames do
    if !([`Init, `Std, `Lean, `Lake, `FOL, `TheoryFramework, `ROBINSON_PlusPlus].contains m.getRoot) then
      logInfo m!"@AJENO {m}"''', 'body')
rep('''# ── 3 · LA ESCALERA DE BINDERS ────────────────────────────────────────────────────────────''', '''# ── 2ter · CONFIANZA, código NATIVO y librerías AJENAS, en el ENTORNO ─────────────────────────
# ⭐ 2026-10-04 (cuarta revisión de ADR-116): el censo de `sorry` sólo miraba `sorryAx`. Una constante que
# use `Lean.ofReduceBool` (confiar en el compilador: con `implemented_by`, el compilador «demuestra» `False`,
# y el core lo avisa) pasaba por limpia; y una librería nueva, importada por FOL, no la censaba nadie.
echo
echo "════ CONFIANZA (axiomas del core fuera de los tres de Lean) · NATIVO (implemented_by / extern) · AJENO ════"
for par in "TRUST|constante(s) usan un axioma de confianza" "NATIVO|constante(s) con implemented_by o extern" "AJENO|módulo(s) de una librería que ningún censo mira"; do
  var="${par%%|*}"; txt="${par#*|}"
  case "$var" in TRUST) re="@TRUST [^ ]+ [^ ]+" ;; *) re="@$var [^ ]+" ;; esac
  val=$(printf '%s' "$PLANA" | grep -oE "$re" | sed "s/@$var //" | sort -u)
  if [ -z "$val" ]; then
    printf "  ✓ %-8s ninguno\\n" "$var"
  else
    printf "  ✗ %-8s %s %s:\\n" "$var" "$(printf '%s\\n' "$val" | wc -l | tr -d ' ')" "$txt"
    printf '%s\\n' "$val" | head -10 | sed 's/^/      · /'
    FAIL=1
  fi
done

# ── 3 · LA ESCALERA DE BINDERS ────────────────────────────────────────────────────────────''', 'sec')
io.open(P, 'w', encoding='utf-8', newline='').write(s)
print('ok')
