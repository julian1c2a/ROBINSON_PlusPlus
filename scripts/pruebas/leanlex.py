# leanlex.py — lexer de referencia que sigue, función a función, al de Lean v4.31.0
# (src/lean/Lean/Parser/Basic.lean: whitespace, finishCommentBlock, tokenFnAux, strLitFnAux,
#  charLitFnAux, quotedCharCoreFn, rawStrLitFnAux, identFnAux, numberFnAux;
#  StrInterpolation.lean: interpolatedStrFn; Init/Meta/Defs.lean: isIdFirst/isIdRest).
# Emite el MISMO formato que strip-lean.awk: una línea por línea, código conservado, comentarios
# fuera, cada literal sustituido por un espacio (las interpolaciones: espacio en `{` y en `}`).
# La única parte que depende del PARSER (no del lexer) es qué cadenas son interpoladas: se decide
# por el token anterior (s! m! f! println! throwError dbg_trace trace[..] …), como en el core.
import sys

def letterlike(o):
    return ((0x3b1 <= o <= 0x3c9 and o != 0x3bb) or (0x391 <= o <= 0x3A9 and o not in (0x3A0, 0x3A3))
            or (0x3ca <= o <= 0x3fb) or (0x1f00 <= o <= 0x1ffe) or (0x2100 <= o <= 0x214f)
            or (0x1d49c <= o <= 0x1d59f) or (0xc0 <= o <= 0xff and o not in (0xd7, 0xf7))
            or (0x100 <= o <= 0x17f))

def subscript(o):
    return (0x2080 <= o <= 0x2089) or (0x2090 <= o <= 0x209c) or (0x1d62 <= o <= 0x1d6a) or o == 0x2c7c

def is_alpha(ch): return ('a' <= ch <= 'z') or ('A' <= ch <= 'Z')
def is_id_first(ch): return is_alpha(ch) or ch == '_' or letterlike(ord(ch))
def is_id_rest(ch):
    return is_alpha(ch) or ('0' <= ch <= '9') or ch in "_'!?" or letterlike(ord(ch)) or subscript(ord(ch))
def is_ws(ch): return ch in ' \t\r\n'

# tokens de símbolo con más de un carácter que importan para el corte (los que acaban en ' o -)
TOKENS = ["Σ'", "×'", "]'", "#'", "<->", "<-", "->", ":=", "=>", "::", "...", "..", "<|>", "<|", "|>.", "|>",
          ">>=", "++", "\\/", "/\\", "`(", "``(", "%[", "#[", "@[", "![", "?_", "<;>", "·", "≠", "≤", "≥"]
TOKENS.sort(key=len, reverse=True)
INTERP_PREV = {"s!", "m!", "f!", "println!", "throwError", "dbg_trace", "reportIssue!", "reportDbgIssue!",
               "reportEMatchIssue!"}
TRACE_OPEN = {"trace[", "Macro.trace[", "trace_goal["}
import os as _os
COMMENT_SPACE = _os.environ.get('COMMENT_SPACE') == '1'


class LexError(Exception):
    pass


class Lex:
    def __init__(self, t):
        self.t = t
        self.n = len(t)
        self.cls = ['C'] * self.n  # C código · D fuera · S espacio
        self.toks = []             # textos de los tokens significativos (para decidir interpolación)
        self.errors = []

    def mark(self, a, b, k):
        for x in range(a, min(b, self.n)):
            self.cls[x] = k

    # ── whitespace (Basic.lean:563) ──
    def whitespace(self, i):
        t, n = self.t, self.n
        while i < n:
            c = t[i]
            if is_ws(c):
                i += 1
            elif c == '-' and i + 1 < n and t[i + 1] == '-':
                j = t.find('\n', i)
                j = n if j < 0 else j
                self.mark(i, j, 'D')
                i = j
            elif c == '/' and i + 1 < n and t[i + 1] == '-':
                third = t[i + 2] if i + 2 < n else ''
                if third in ('-', '!'):
                    return i  # /-- y /-! son tokens
                a = i
                i = min(i + 3, n)
                i = self.finish_comment(i, 1)
                self.mark(a, i, 'D')
                if COMMENT_SPACE:
                    self.cls[a] = 'S'  # para Lean un comentario es ESPACIO: separa tokens
            else:
                return i
        return i

    # ── finishCommentBlock (Basic.lean:537) ──
    def finish_comment(self, i, nesting):
        t, n = self.t, self.n
        while True:
            if i >= n:
                self.errors.append('unterminated comment')
                return n
            curr = t[i]
            i += 1
            if curr == '-':
                if i >= n:
                    self.errors.append('unterminated comment')
                    return n
                if t[i] == '/':
                    i += 1
                    if nesting == 1:
                        return i
                    nesting -= 1
            elif curr == '/':
                if i >= n:
                    self.errors.append('unterminated comment')
                    return n
                if t[i] == '-':
                    i += 1
                    nesting += 1

    # ── quotedCharCoreFn (Basic.lean:657) ──
    def quoted(self, j, in_string, interp):
        t, n = self.t, self.n
        if j >= n:
            raise LexError('eoi in escape')
        c = t[j]
        if c in '\\"\'rnt' or (interp and c == '{'):
            return j + 1
        if c == 'x':
            return j + 3
        if c == 'u':
            return j + 5
        if in_string and c == '\n':
            k, seen = j, False
            while k < n:
                if t[k] == '\n':
                    if seen:
                        raise LexError('extra newline in gap')
                    seen = True
                    k += 1
                elif is_ws(t[k]):
                    k += 1
                else:
                    break
            return k
        raise LexError('invalid escape ' + repr(c))

    def plain_string(self, i):
        t, n = self.t, self.n
        j = i + 1
        while j < n:
            c = t[j]
            j += 1
            if c == '"':
                return j
            if c == '\\':
                j = self.quoted(j, True, False)
        self.errors.append('unterminated string')
        return n

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
                j = self.whitespace(j)
                j = self.tokens(j, close_brace=True)
                if j >= n or t[j] != '}':
                    self.errors.append('interp without }')
                    return n
                self.cls[j] = 'S'
                j += 1
                start = j
        self.errors.append('unterminated interp string')
        return n

    def char_lit(self, i):
        t, n = self.t, self.n
        j = i + 1
        if j >= n:
            raise LexError('eoi char')
        c = t[j]
        j += 1
        if c == '\\':
            j = self.quoted(j, False, False)
        if j < n and t[j] == "'":
            return j + 1
        raise LexError('missing end of char literal')

    def raw_start(self, i):
        t, n = self.t, self.n
        while i < n and t[i] == '#':
            i += 1
        return i < n and t[i] == '"'

    def raw_string(self, i):  # i en la 'r'
        t, n = self.t, self.n
        j = i + 1
        num = 0
        while t[j] == '#':
            num += 1
            j += 1
        j += 1  # la comilla
        while j < n:
            c = t[j]
            j += 1
            if c == '"':
                if num == 0:
                    return j
                k = 0
                while j < n and t[j] == '#' and k < num:
                    k += 1
                    j += 1
                if k == num:
                    return j
                # si hubo menos almohadillas, sigue (closingState vuelve a normalState o reinicia en ")
                if j < n and t[j] == '"':
                    continue
        self.errors.append('unterminated raw string')
        return n

    def ident(self, j):
        t, n = self.t, self.n
        while True:
            if j < n and t[j] == '«':
                k = t.find('»', j + 1)
                if k < 0:
                    raise LexError('unterminated ident escape')
                j = k + 1
            elif j < n and is_id_first(t[j]):
                j += 1
                while j < n and is_id_rest(t[j]):
                    j += 1
            else:
                return j
            if j + 1 < n and t[j] == '.' and (is_id_first(t[j + 1]) or t[j + 1] == '«'):
                j += 1
                continue
            return j

    def number(self, i):
        t, n = self.t, self.n
        j = i
        if t[j] == '0' and j + 1 < n and t[j + 1] in 'bBoOxX':
            j += 2
            while j < n and (t[j].isalnum() or t[j] == '_'):
                j += 1
            return j
        while j < n and (t[j].isdigit() or t[j] == '_'):
            j += 1
        if j + 1 < n and t[j] == '.' and t[j + 1] == '.':
            return j
        if j < n and t[j] == '.':
            j += 1
            while j < n and (t[j].isdigit() or t[j] == '_'):
                j += 1
        if j < n and t[j] in 'eE':
            k = j + 1
            if k < n and t[k] in '+-':
                k += 1
            if k < n and t[k].isdigit():
                j = k
                while j < n and t[j].isdigit():
                    j += 1
        return j

    def is_interp(self):
        tk = self.toks
        if tk and tk[-1] in INTERP_PREV:
            return True
        if len(tk) >= 3 and tk[-1] == ']' and tk[-3] in TRACE_OPEN:
            return True
        if len(tk) >= 2 and tk[-2] == 'throwErrorAt':
            return True
        return False

    def token(self, i):
        t, n = self.t, self.n
        c = t[i]
        if t.startswith('/--', i) or t.startswith('/-!', i):
            j = self.finish_comment(i + 3, 1)
            self.mark(i, j, 'D')
            if COMMENT_SPACE:
                self.cls[i] = 'S'
            return j, None
        if c == '"':
            if self.is_interp():
                j = self.interp_string(i)
            else:
                j = self.plain_string(i)
                self.mark(i, j, 'D')
                self.cls[i] = 'S'
            return j, '"str"'
        if c == "'" and i + 1 < n and t[i + 1] != "'":
            try:
                j = self.char_lit(i)
                self.mark(i, j, 'D')
                self.cls[i] = 'S'
                return j, "'chr'"
            except LexError as e:
                self.errors.append('char@%d: %s' % (i, e))
        if c.isdigit():
            j = self.number(i)
            return j, t[i:j]
        if c == '`' and i + 1 < n and (is_id_first(t[i + 1]) or t[i + 1] == '«'):
            j = self.ident(i + 1)
            return j, t[i:j]
        if c == 'r' and self.raw_start(i + 1):
            j = self.raw_string(i)
            self.mark(i, j, 'D')
            self.cls[i] = 'S'
            return j, '"raw"'
        tk = None
        for k in TOKENS:
            if t.startswith(k, i):
                tk = k
                break
        if c == '«' or is_id_first(c):
            j = self.ident(i)
            if tk is not None and len(tk) >= j - i:
                return i + len(tk), tk
            # tokens con forma de identificador seguidos de '[' (trace[ …)
            if j < n and t[j] == '[' and t[i:j + 1] in TRACE_OPEN:
                return j + 1, t[i:j + 1]
            return j, t[i:j]
        if tk is not None:
            return i + len(tk), tk
        return i + 1, c

    def tokens(self, i, close_brace=False):
        t, n = self.t, self.n
        depth = 0
        i = self.whitespace(i)
        while i < n:
            if close_brace:
                if t[i] == '{':
                    depth += 1
                elif t[i] == '}':
                    if depth == 0:
                        return i
                    depth -= 1
            try:
                i, tok = self.token(i)
            except LexError as e:
                self.errors.append('tok@%d: %s' % (i, e))
                i += 1
                tok = None
            if tok is not None:
                self.toks.append(tok)
            i = self.whitespace(i)
        return i

    def run(self):
        self.tokens(0)
        out = []
        for ch, k in zip(self.t, self.cls):
            if ch == '\n':
                out.append('\n')
            elif k == 'C':
                out.append(ch)
            elif k == 'S':
                out.append(' ')
        s = ''.join(out)
        if s.endswith('\n'):
            s = s[:-1]
        return s


def strip_text(t):
    t = t.replace(chr(13) + chr(10), chr(10))  # Lean: mkInputContext normaliza CRLF (Parser/Extension.lean:459)
    L = Lex(t)
    return L.run(), L.errors


if __name__ == '__main__':
    for p in sys.argv[1:]:
        with open(p, encoding='utf-8', newline='') as f:
            t = f.read()
        s, errs = strip_text(t)
        sys.stdout.write(s + '\n')
        for e in errs:
            print('LEXERR', p, e, file=sys.stderr)
