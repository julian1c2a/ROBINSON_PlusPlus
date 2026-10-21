# ⛔ RESCATADO el 2026-10-21 (T47, ADR-180) del scratchpad de la sesión 85b0df6c (r4/regresiones-v4/oracle2.py, del
# 2026-10-04): T00 guardó leanlex.py pero NO esta capa, y sin ella el oráculo no es el de la validación de la v5
# (ADR-116). Sin cambios salvo estas dos líneas.
# oracle2.py — leanlex.py con los huecos conocidos tapados (siguiendo al fuente de Lean v4.31.0):
#  · tokens `//` (Init/Notation.lean:577) y `⊕'` (Init/Core.lean:234);
#  · tras `.` (proj / dotIdent) y `|>.` (pipeProj) Lean lee un rawIdent (Term.lean:899-951): `.r"…"` es
#    el identificador `r` y una cadena normal, no una cadena en bruto;
#  · throwErrorAt con referencia `x`, `x[…]` o `(…)` sin paréntesis dentro; throwNamedError* / logNamed*.
import os
os.environ['COMMENT_SPACE'] = '1'
import leanlex
from leanlex import is_id_first
leanlex.COMMENT_SPACE = True
for tk in ["//", "⊕'"]:
    if tk not in leanlex.TOKENS:
        leanlex.TOKENS.append(tk)
leanlex.TOKENS.sort(key=len, reverse=True)

NAMED1 = {'throwNamedError', 'logNamedError', 'logNamedWarning'}
NAMED2 = {'throwNamedErrorAt', 'logNamedErrorAt', 'logNamedWarningAt'}


class Lex2(leanlex.Lex):
    # leanlex no anota en toks la apertura de una interpolación: tras `s!"{` el último token seguía
    # siendo `s!`, y una cadena NORMAL al principio del código (`s!"{"a{b}"}"`) se leía interpolada.
    # Aquí se anota `{` al entrar en el código y `}` al salir.
    def whitespace(self, i):
        return super().whitespace(i)

    def interp_string(self, i):
        t, n = self.t, self.n
        j = i + 1
        start = i
        while j < n:
            c = t[j]
            j += 1
            if c == '"':
                self.mark(start, j, 'D')
                self.cls[start] = 'S' if start == i else self.cls[start]
                return j
            if c == '\\':
                j = self.quoted(j, True, True)
            elif c == '{':
                self.mark(start, j, 'D')
                if start == i:
                    self.cls[i] = 'S'
                self.cls[j - 1] = 'S'
                self.toks.append('{')
                j = self.whitespace(j)
                j = self.tokens(j, close_brace=True)
                if j >= n or t[j] != '}':
                    self.errors.append('interp without }')
                    return n
                self.cls[j] = 'S'
                self.toks.append('}')
                j += 1
                start = j
        self.errors.append('unterminated interp string')
        return n

    def token(self, i):
        t, n = self.t, self.n
        # `.ident` y `|>.ident`: rawIdent (sin mirar cadenas en bruto)
        if t[i] == '.' and i + 1 < n and (is_id_first(t[i + 1]) or t[i + 1] == '«') and not t.startswith('..', i):
            j = self.ident(i + 1)
            return j, t[i:j]
        if t.startswith('|>.', i) and i + 3 < n and (is_id_first(t[i + 3]) or t[i + 3] == '«'):
            j = self.ident(i + 3)
            return j, t[i:j]
        return super().token(i)

    def ref_len(self, k):
        # longitud (en tokens) de una referencia simple que empieza en toks[k]: x | x[…]… | (…) sin ( dentro
        tk = self.toks
        if k >= len(tk):
            return -1
        if tk[k] == '(':
            m = k + 1
            while m < len(tk) and tk[m] not in ('(', ')'):
                m += 1
            if m < len(tk) and tk[m] == ')':
                return m - k + 1
            return -1
        m = k + 1
        while m < len(tk) and tk[m] == '[':
            q = m + 1
            while q < len(tk) and tk[q] not in ('[', ']'):
                q += 1
            if q < len(tk) and tk[q] == ']':
                m = q + 1
            else:
                return -1
        return m - k

    def is_interp(self):
        tk = self.toks
        if tk and tk[-1] in leanlex.INTERP_PREV:
            return True
        if len(tk) >= 3 and tk[-1] == ']' and tk[-3] in leanlex.TRACE_OPEN:
            return True
        # throwErrorAt <ref>
        for k in range(len(tk) - 1, max(-1, len(tk) - 40), -1):
            if tk[k] == 'throwErrorAt':
                if self.ref_len(k + 1) == len(tk) - k - 1:
                    return True
                break
        if len(tk) >= 2 and tk[-2] in NAMED1:
            return True
        for k in range(len(tk) - 1, max(-1, len(tk) - 40), -1):
            if tk[k] in NAMED2:
                r = self.ref_len(k + 1)
                if r > 0 and k + 1 + r == len(tk) - 1:
                    return True
                break
        return False


def strip_text(t):
    t = t.replace(chr(13) + chr(10), chr(10))
    L = Lex2(t)
    return L.run(), L.errors
