import re, os
H = os.path.expanduser('~/.elan/toolchains')
A = os.path.join(H, 'leanprover--lean4---v4.31.0', 'src', 'lean')
B = os.path.join(H, 'leanprover--lean4---v4.35.0', 'src', 'lean')
FILES = ['Lean/Parser/Basic.lean', 'Init/Meta/Defs.lean', 'Lean/Parser/StrInterpolation.lean']
FNS = ['whitespace', 'finishCommentBlock', 'tokenFnAux', 'strLitFnAux', 'charLitFnAux', 'quotedCharCoreFn',
       'quotedStringFn', 'rawStrLitFnAux', 'identFnAux', 'numberFnAux', 'isIdFirst', 'isIdRest', 'isLetterLike',
       'isSubScriptAlnum', 'isIdBeginEscape', 'isIdEndEscape', 'interpolatedStrFn', 'takeUntilFn', 'mkIdResult',
       'decimalNumberFn', 'binNumberFn', 'octalNumberFn', 'hexNumberFn', 'nameLitAux', 'splitNameLitAux']
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|partial|noncomputable|unsafe|nonrec)\s+)*(?:def|theorem|abbrev|instance|structure|inductive|opaque|macro|syntax|@\[)')
def body(root, fn):
    for f in FILES:
        t = open(os.path.join(root, f), encoding='utf-8').read().split('\n')
        for i, l in enumerate(t):
            if re.match(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|partial|noncomputable|unsafe)\s+)*def ' + re.escape(fn) + r'\b', l):
                j = i + 1
                while j < len(t) and not (t[j] and not t[j][0].isspace() and DECL.match(t[j])) and not t[j].startswith('end ') and not t[j].startswith('/--') and not t[j].startswith('namespace'):
                    j += 1
                return f, '\n'.join(t[i:j]).rstrip()
    return None, None
for fn in FNS:
    fa, ba = body(A, fn); fb, bb = body(B, fn)
    if ba is None and bb is None:
        print('%-20s no está en ninguno' % fn)
    elif ba is None or bb is None:
        print('%-20s SÓLO en %s' % (fn, 'v4.35' if ba is None else 'v4.31'))
    else:
        print('%-20s %-36s %4d líneas  %s' % (fn, fa, ba.count('\n') + 1, 'igual' if ba == bb else 'DISTINTA'))
