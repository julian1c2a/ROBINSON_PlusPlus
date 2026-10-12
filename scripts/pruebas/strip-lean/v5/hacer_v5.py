# hacer_v5.py — strip-lean.awk v5: la v4 del árbol (copia de FOL) con los dos arreglos de la cuarta revisión.
import io, os
HERE = os.path.dirname(os.path.abspath(__file__))
s = io.open('E:/dropbox/github/lean4/FOL/strip-lean.awk', encoding='utf-8', newline='').read()
assert '\r\n' not in s

def rep(old, new):
    global s
    assert s.count(old) == 1, (old[:70], s.count(old))
    s = s.replace(old, new)

# 1 · máxima longitud antes de mirar comentarios
rep('''    # `\\/`, `//` y `<-` son tokens del core: Lean los lee enteros ANTES de mirar si sigue un
    # comentario (`p \\/-- c` es `\\/` y un comentario; `{ x // -x … }` sin espacio no abre ninguno)
    if (two == "\\\\/" || two == "//" || two == "<-") { out = out two; tb = tb two; i += 2; inid = 0; lastc = substr(two, 2, 1); continue }
''', '''    # Los tokens del core se leen ENTEROS y por MÁXIMA LONGITUD (como `matchPrefix`) antes de mirar si
    # sigue un comentario: `\\/`, `//` y `<-` acaban en `/` o `-` (`p \\/-- c` es `\\/` y un comentario;
    # `{ x // -x … }` sin espacio no abre ninguno), y `<<<` `=<<` `<=<` `...<` `*...<` `<...<` `/\\` ABSORBEN
    # el `<` de un `<-` o el `\\` de un `\\/` (`a <<<-- c` es `<<<` y un comentario); los de 2 que acaban en
    # `=` o `:` van con ellos, para que `:=<<<--` salga igual (cuarta revisión de ADR-116).
    tk = ""
    if ((t5 = substr(line, i, 5)) == "*...<" || t5 == "<...<") tk = t5
    else if (substr(line, i, 4) == "...<") tk = "...<"
    else if ((t3 = substr(line, i, 3)) == "<<<" || t3 == "=<<" || t3 == "<=<") tk = t3
    else if (two == "/\\\\" || two == "\\\\/" || two == "//" || two == "<-" || two == ":=" || two == "==" || two == "!=" || two == "<=" || two == ">=") tk = two
    if (tk != "") { out = out tk; tb = tb tk; i += length(tk); inid = 0; lastc = substr(tk, length(tk), 1); continue }
''')
# 2 · el término de `throwErrorAt`: tras un índice, más caracteres sin espacio (`]!`, `]?`, `].raw`, `][1]`)
viejo = '''[^ \\t()"[]+(\\[[^]]*\\])*)'''
nuevo = '''[^ \\t()"[]+(\\[[^]]*\\][^ \\t()"[]*)*)'''
assert s.count(viejo) == 2, s.count(viejo)
s = s.replace(viejo, nuevo)
# 3 · cabecera
rep('''# el término de `throwErrorAt` se reconoce si es un token, un token con índices `x[…]` o un paréntesis
# sin paréntesis dentro; y un token propio de un proyecto que acabe en `-`, `/` o `'` (hoy no hay).''',
    '''# el término de `throwErrorAt` se reconoce si es un token (también con índices: `x[i]`, `x[i]!`, `x[i].raw`)
# o un paréntesis sin paréntesis dentro; y un token propio de un proyecto que acabe en `-`, `/`, `<`, `\\`
# o `'` (hoy no hay ninguno: comprobado en los dos repos).''')
rep('''# modo byte, comentario = espacio); v4 (2026-10-04) tras la tercera: seis familias más, todas latentes
# (0 casos en los dos repos), la mitad con VERDE falso. Los casos están en el autotest de `check-sorry.bash`.''',
    '''# modo byte, comentario = espacio); v4 (2026-10-04) tras la tercera: seis familias más, todas latentes
# (0 casos en los dos repos), la mitad con VERDE falso; v5 el mismo día, tras la cuarta: dos regresiones de
# la v4 (la máxima longitud de los tokens, y `throwErrorAt x[i]!`). Los casos están en el autotest de
# `check-sorry.bash`, que compara el CONJUNTO de líneas con `sorry`, no la cuenta.''')
os.makedirs(HERE, exist_ok=True)
io.open(os.path.join(HERE, 'strip-lean.awk'), 'w', encoding='utf-8', newline='').write(s)
print('ok', len(s))
