# docsync_v5.py — cuarta revisión: AX_TOK (frontera y «), el fixture de [A] con tres casos más, y en RPP el
# trinquete de B_TOPE contra el MÍNIMO de su historia (con la excepción atada a un valor).
import io

def rep(s, old, new, tag, n=1):
    c = s.count(old)
    assert c == n, (tag, c, old[:90])
    return s.replace(old, new)

AX_OLD = '''AX_TOK="(^|[^A-Za-z0-9_'.«])axiom([[:space:]]|$)"'''
AX_NEW = '''# (cuarta revisión: la frontera excluye la comilla invertida —`` `axiom `` es un literal de nombre— y los
#  bytes de continuación UTF-8 —`αaxiom` es UN identificador—, y tras `axiom` vale también `«`)
AX_TOK="(^|[^A-Za-z0-9_'.«\\`"$'\\x80-\\xbf'"])axiom([[:space:]«]|$)"'''
FIX_OLD = '''open Nat in axiom real8 : True
theorem u : True := trivial -- axiom senuelo5
EOF
AXIOMS=""
if [ "$(cuenta_axiomas "$AX_FIX" || true)" = "8" ]; then'''
FIX_NEW = '''open Nat in axiom real8 : True
axiom«real9» : True
theorem u : True := trivial -- axiom senuelo5
def k := `axiom
def αaxiom : Nat := 1
EOF
AXIOMS=""
if [ "$(cuenta_axiomas "$AX_FIX" || true)" = "9" ]; then'''
MSG_OLD = 'el autotest de cuenta_axiomas no dio 8 (¿strip-lean.awk, LC_ALL?).'
MSG_NEW = 'el autotest de cuenta_axiomas no dio 9 (¿strip-lean.awk, LC_ALL?).'

for P in ('E:/dropbox/github/lean4/ROBINSON_PlusPlus/check-doc-sync.bash', 'E:/dropbox/github/lean4/FOL/check-doc-sync.bash'):
    s = io.open(P, encoding='utf-8', newline='').read()
    assert '\r\n' not in s
    s = rep(s, AX_OLD, AX_NEW, 'ax ' + P)
    s = rep(s, FIX_OLD, FIX_NEW, 'fix ' + P)
    s = rep(s, MSG_OLD, MSG_NEW, 'msg ' + P)
    if 'ROBINSON_PlusPlus/' in P:
        s = rep(s, '''B_TOPE_ADR=""   # sólo si un ADR SUBE el tope: su número («ADR-123»), que tiene que existir en DECISIONS.md''',
                '''B_TOPE_ADR=""   # sólo si un ADR SUBE el tope: «ADR-123:42» (el ADR, que tiene que existir, y el tope NUEVO)''', 'tope adr')
        a = s.index('''# ⛔ 2026-10-04 (tercera revisión): «el tope sólo baja» no lo comprobaba nada''')
        b = s.index('''B_DECL=$(sort -u "$B_VISTOS" | grep -c . || true)''')
        s = s[:a] + '''# ⛔ 2026-10-04 (tercera y cuarta revisión): «el tope sólo baja» no lo comprobaba nada (subir tabla y tope
# en la misma edición daba verde), y la primera comparación —con el commit padre— tampoco: tras el commit
# que lo subía, cualquier otro encima ya lo traía subido. Ahora la referencia es FIJA: el MÍNIMO de B_TOPE
# en toda la historia de este fichero. Subirlo exige `B_TOPE_ADR="ADR-NNN:valor"`, con el ADR existente y
# el valor igual al tope de ahora. Sin historia (un clon superficial) no se compara, y `[E]` ya da rojo.
B_TOPE_MIN=""
for c in $(git log --format=%H -- check-doc-sync.bash 2>/dev/null); do
  v=$(git show "$c:check-doc-sync.bash" 2>/dev/null | grep -oE '^B_TOPE=[0-9]+' | head -1 | cut -d= -f2)
  [ -n "$v" ] || continue
  if [ -z "$B_TOPE_MIN" ] || [ "$v" -lt "$B_TOPE_MIN" ]; then B_TOPE_MIN=$v; fi
done
if [ -n "$B_TOPE_MIN" ] && [ "$B_TOPE" -gt "$B_TOPE_MIN" ]; then
  B_ADR_ID="${B_TOPE_ADR%%:*}"; B_ADR_VAL="${B_TOPE_ADR#*:}"
  if [ -n "$B_TOPE_ADR" ] && [ "$B_ADR_VAL" = "$B_TOPE" ] && grep -qE "^## $B_ADR_ID:" DECISIONS.md; then
    echo "  ⚠️  el tope está por encima de su mínimo histórico ($B_TOPE_MIN): $B_TOPE, con $B_ADR_ID."
  else
    echo "  ❌ el tope de B_DEUDA ($B_TOPE) está por encima de su mínimo histórico ($B_TOPE_MIN) sin un ADR"
    echo "      que lo suba a ESE valor (B_TOPE_ADR=\\"ADR-NNN:$B_TOPE\\"): la deuda no puede crecer."
    B_FAIL=1
  fi
fi
''' + s[b:]
    io.open(P, 'w', encoding='utf-8', newline='').write(s)
    print('ok', P)
