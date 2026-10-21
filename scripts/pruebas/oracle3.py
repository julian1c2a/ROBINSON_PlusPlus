# ⛔ RESCATADO el 2026-10-21 (T47, ADR-180) del scratchpad de la sesión 85b0df6c (r4/regresiones-v4/oracle3.py, del
# 2026-10-04): es el oráculo con el que se validó strip-lean.awk v5 (ADR-116). Sin cambios salvo estas dos líneas.
# oracle3.py — oracle2 con los tokens del core que terminan en `<` o en `\` (y `==`), que oracle2 no
# tenía: con ellos, el corte de máxima longitud (`tokenFnAux`/`matchPrefix`) decide dónde empieza un
# comentario tras `<<<`, `=<<`, `<=<`, `...<`, `*...<`, `<...<` (Init/Notation.lean:289,
# Init/Control/Basic.lean:432-433, Init/Data/Range/Polymorphic/PRange.lean:157-171).
import os
os.environ['COMMENT_SPACE'] = '1'
import leanlex
import oracle2
EXTRA = ['<<<', '=<<', '<=<', '...<', '*...<', '<...<', '==', '>>>', '>>', '<*>', '<*', '*>', '<$>', '<&>',
         '^^^', '&&&', '|||', '<=', '>=', '!=', '&&', '||']
for tk in EXTRA:
    if tk not in leanlex.TOKENS:
        leanlex.TOKENS.append(tk)
leanlex.TOKENS.sort(key=len, reverse=True)
strip_text = oracle2.strip_text
