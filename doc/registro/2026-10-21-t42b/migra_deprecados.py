# migra_deprecados.py RAIZ... — T42b (v4.35): los seis nombres que v4.35 depreca (`Init/Core.lean`, `Init/ByCases.lean`,
# «since 2026-07-21»), por sus sustitutos, con la MISMA firma: if_pos → ite_eq_left, if_neg → ite_eq_right,
# dif_pos → dite_eq_left, dif_neg → dite_eq_right, if_true → ite_true, if_false → ite_false. Por palabra (sin tocar
# `prf_if_pos` ni `if_posX`), en los `.lean` de las raíces, conservando CRLF. Imprime cuántos cambia por fichero.
import io, os, re, sys
MAPA = {'if_pos': 'ite_eq_left', 'if_neg': 'ite_eq_right', 'dif_pos': 'dite_eq_left', 'dif_neg': 'dite_eq_right',
        'if_true': 'ite_true', 'if_false': 'ite_false'}
PAT = re.compile(r"(?<![A-Za-z0-9_'.])(" + '|'.join(MAPA) + r")(?![A-Za-z0-9_'!?])")
tot = 0
for raiz in sys.argv[1:]:
    fs = [raiz] if os.path.isfile(raiz) else [os.path.join(d, f) for d, _, ff in os.walk(raiz) if '.lake' not in d for f in ff if f.endswith('.lean')]
    for p in sorted(fs):
        raw = io.open(p, encoding='utf-8', newline='').read()
        new, n = PAT.subn(lambda m: MAPA[m.group(1)], raw)
        if n:
            io.open(p, 'w', encoding='utf-8', newline='').write(new)
            print('%5d  %s' % (n, p))
            tot += n
print('total:', tot)
