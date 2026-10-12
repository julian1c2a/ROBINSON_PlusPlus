# axioms_v5.py — FOL/check-axioms.bash tras la cuarta revisión de ADR-116 (RPP): el grep (frontera, «…», sed
# anclado, ficheros con espacios), el humo, y en el ENTORNO: @TRUST (axiomas de confianza del core),
# @NATIVO (implemented_by / extern) y @AJENO (módulos de librerías que nadie censa).
import io
P = 'E:/dropbox/github/lean4/FOL/check-axioms.bash'
s = io.open(P, encoding='utf-8', newline='').read()
assert '\r\n' not in s

def rep(old, new, tag, n=1):
    global s
    c = s.count(old)
    assert c == n, (tag, c, old[:90])
    s = s.replace(old, new)

rep('''AX_TOK="(^|[^A-Za-z0-9_'.«])axiom([[:space:]]+[^[:space:]:({]+|[[:space:]]*\\$)"
grep_axiomas () {
  for f in "$@"; do
    [ -f "$f" ] || continue
    STRIP "$f" | { LC_ALL=C grep -noE "$AX_TOK" || true; } \\
      | LC_ALL=C sed -E "s|^([0-9]+):.*axiom[[:space:]]*([^[:space:]:({]*).*|$f:\\1:\\2|; s|:\\$|:?|"
  done
}
lean_de () { find "$@" -name '*.lean' ! -path '*/.lake/*' 2>/dev/null | sort; }''',
'''# ⛔ Y desde la cuarta revisión: la frontera excluye la comilla invertida (`` `axiom `` es un literal de
# nombre) y los bytes de continuación UTF-8 (`αaxiom` es UN identificador); el nombre puede ser `«…»`; el
# sed se ANCLA a la frontera (con `.*` voraz, `axiom my_axiom` salía «?»); y los ficheros se pasan de uno en
# uno, nunca partidos por espacios («cuarentena/X - copia.lean» se saltaba en silencio). Un argumento que
# no es un fichero es SIN MEDIR.
AX_TOK="(^|[^A-Za-z0-9_'.«\\`"$'\\x80-\\xbf'"])axiom([[:space:]]+(«[^»]*»|[^[:space:]:({«]+)|«[^»]*»|[[:space:]]*\\$)"
grep_axiomas () {
  local f
  for f in "$@"; do
    [ -f "$f" ] || { echo "SIN-MEDIR:$f"; continue; }
    STRIP "$f" | { LC_ALL=C grep -noE "$AX_TOK" || true; } \\
      | LC_ALL=C sed -E "s|^([0-9]+):[^A-Za-z0-9_]?axiom[[:space:]]*(«[^»]*»\\|[^[:space:]:({«]*).*|$f:\\1:\\2|; s|:\\$|:?|"
  done
}
lean_de () { find "$@" -name '*.lean' ! -path '*/.lake/*' 2>/dev/null | sort; }
# grep_lista DIR… → grep_axiomas de cada `.lean` de los directorios, leídos por LÍNEAS (con espacios, bien)
grep_lista () { lean_de "$@" | while IFS= read -r f; do grep_axiomas "$f"; done; }''', 'grep')

rep('''HUMO_F=$(mktemp)
printf '%s\\n' '/-- axiom falso1 : X -/' '-- axiom falso2 : X' 'def s := "axiom falso3 : X"' \\
       '  private axiom real1 : True' '@[simp] axiom real2 : True' 'open Nat in axiom real3 : True' \\
       'def axiomInfo := 0' > "$HUMO_F"
HUMO=$(grep_axiomas "$HUMO_F" | sed 's/.*://' | tr '\\n' ' ')
rm -f "$HUMO_F"
if [ "$HUMO" != "real1 real2 real3 " ]; then''', '''HUMO_F=$(mktemp)
printf '%s\\n' '/-- axiom falso1 : X -/' '-- axiom falso2 : X' 'def s := "axiom falso3 : X"' \\
       '  private axiom real1 : True' '@[simp] axiom real2 : True' 'open Nat in axiom real3 : True' \\
       'def axiomInfo := 0' 'axiom real_axiom : True' 'axiom' '  real4 : True' 'def k := `axiom' \\
       'def αaxiom : Nat := 1' 'axiom«real5» : True' > "$HUMO_F"
HUMO=$(grep_axiomas "$HUMO_F" | sed 's/.*://' | tr '\\n' ' ')
rm -f "$HUMO_F"
if [ "$HUMO" != "real1 real2 real3 real_axiom ? «real5» " ]; then''', 'humo')
rep('''# PRUEBA DE HUMO (ADR-116): con un despojador roto, el contraste y la cuarentena daban «0» sin medir.
# Entrada fija: tres `axiom` reales (con sangría y modificador, con atributo, y tras `open … in`) y cuatro
# falsos (docstring, comentario, cadena y un identificador que empieza por `axiom`). Si no salen
# exactamente esos tres nombres, NO se mide.''', '''# PRUEBA DE HUMO (ADR-116): con un despojador roto, el contraste y la cuarentena daban «0» sin medir.
# Entrada fija: seis `axiom` reales (con sangría y modificador, con atributo, tras `open … in`, con
# «axiom» DENTRO del nombre, con el nombre en la línea siguiente —sale «?»— y con nombre `«…»`) y seis
# falsos (docstring, comentario, cadena, un identificador que empieza por `axiom`, un literal de nombre y
# un identificador que ACABA en `axiom` tras una letra griega). Si no salen exactamente esos, NO se mide.''', 'humo doc')

# el entorno: @TRUST, @NATIVO, @AJENO
rep('''  echo "import FOL"
  for f in $(lean_de TheoryFramework); do''', '''  echo "import Lean"
  echo "import FOL"
  for f in $(lean_de TheoryFramework); do''', 'import Lean')
rep('''run_cmd do
  let env ← Lean.getEnv
  let mut nFOL := 0
  let mut nTF := 0
  for (n, ci) in env.constants.toList do''', '''run_cmd do
  let env ← Lean.getEnv
  let mut nFOL := 0
  let mut nTF := 0
  -- los tres axiomas de Lean que el proyecto acepta; cualquier OTRO axioma ajeno que use una constante
  -- nuestra (`sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, …) es @TRUST
  let estandar : NameSet := ((({} : NameSet).insert ``propext).insert ``Classical.choice).insert ``Quot.sound
  for (n, ci) in env.constants.toList do''', 'run_cmd head')
rep('''        if ci.getUsedConstantsAsSet.contains ``sorryAx then logInfo m!"@SORRY {lib} {n}"
    | none => pure ()''', '''        let usadas := ci.getUsedConstantsAsSet
        if usadas.contains ``sorryAx then logInfo m!"@SORRY {lib} {n}"
        for u in usadas do
          if let some (.axiomInfo _) := env.find? u then
            if !estandar.contains u && u != ``sorryAx then
              match env.getModuleIdxFor? u with
              | some j =>
                let mu := env.header.moduleNames[j.toNat]!
                if !((`FOL).isPrefixOf mu || (`TheoryFramework).isPrefixOf mu) then logInfo m!"@TRUST {lib} {n} {u}"
              | none => logInfo m!"@TRUST {lib} {n} {u}"
        if (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n then logInfo m!"@NATIVO {lib} {n}"
    | none => pure ()''', 'run_cmd body')
rep('''  logInfo m!"@CONST {nFOL} {nTF}"''', '''  logInfo m!"@CONST {nFOL} {nTF}"
  -- ¿alguna librería cargada que ningún censo mira? (una nueva, importada por FOL, quedaría fuera)
  for m in env.header.moduleNames do
    if !([`Init, `Std, `Lean, `Lake, `FOL, `TheoryFramework].contains m.getRoot) then logInfo m!"@AJENO {m}"''', 'ajeno')

rep('''# ── 2 · La CUARENTENA, que no se compila: por grep, sin comentarios ──────────────────────────''',
    '''# ── 1ter · CONFIANZA y código NATIVO en el ENTORNO (cuarta revisión de ADR-116 de RPP) ─────────
# El censo de `sorry` sólo miraba `sorryAx`: una constante que use `Lean.ofReduceBool` (confiar en el
# compilador, y con `implemented_by` el compilador puede «demostrar» `False`) pasaba por limpia.
echo
echo "════ CONFIANZA (axiomas del core fuera de los tres de Lean) · NATIVO (implemented_by / extern) · AJENO ════"
TRUST=$(printf '%s' "$PLANA" | grep -oE "@TRUST (FOL|TF) [^ ]+ [^ ]+" | sed 's/@TRUST //' | sort -u)
NATIVO=$(printf '%s' "$PLANA" | grep -oE "@NATIVO (FOL|TF) [^ ]+" | sed 's/@NATIVO //' | sort -u)
AJENO=$(printf '%s' "$PLANA" | grep -oE "@AJENO [^ ]+" | sed 's/@AJENO //' | sort -u)
for par in "TRUST|constante(s) usan un axioma de confianza" "NATIVO|constante(s) con implemented_by o extern" "AJENO|módulo(s) de una librería que ningún censo mira"; do
  var="${par%%|*}"; txt="${par#*|}"
  val="${!var}"
  if [ -z "$val" ]; then
    printf "  ✓ %-8s ninguno\\n" "$var"
  else
    printf "  ✗ %-8s %s %s:\\n" "$var" "$(cuenta "$val")" "$txt"
    printf '%s\\n' "$val" | head -10 | sed 's/^/      · /'
    FAIL=1
  fi
done

# ── 2 · La CUARENTENA, que no se compila: por grep, sin comentarios ──────────────────────────''', 'sec 1ter')
rep('''GREP_FOL=$(grep_axiomas FOL.lean $(lean_de FOL))
GREP_TF=$(grep_axiomas TheoryFramework.lean $(lean_de TheoryFramework))''', '''GREP_FOL=$(grep_axiomas FOL.lean; grep_lista FOL)
GREP_TF=$(grep_axiomas TheoryFramework.lean; grep_lista TheoryFramework)''', 'grep libs')
rep('''  TODO_C=$(grep_axiomas $(lean_de cuarentena))
  RET_C=$(grep_axiomas $(lean_de cuarentena/librerias-retiradas))''', '''  TODO_C=$(grep_lista cuarentena)
  RET_C=$(grep_lista cuarentena/librerias-retiradas)''', 'grep cuar')
rep('''for l in FOLPure PropLogic FOL_poli; do
  if grep -q "lean_lib «$l»" lakefile.lean 2>/dev/null; then''', '''for l in FOLPure PropLogic FOL_poli; do
  # (con «» o sin ellas: `lean_lib FOLPure where` también es Lake válido — cuarta revisión)
  if grep -qE "lean_lib[[:space:]]+«?$l»?([[:space:]]|$)" lakefile.lean 2>/dev/null; then''', 'retiradas')
io.open(P, 'w', encoding='utf-8', newline='').write(s)
print('ok')
