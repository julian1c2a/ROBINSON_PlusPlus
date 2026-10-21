# renombres_en_comentarios.py — T42b: de los renombres de la migración (if_pos → ite_eq_left…), ¿cuántos cayeron en
# CÓDIGO y cuántos en comentarios o cadenas? (los segundos pueden ser CITAS de un mensaje viejo, que no se renombran).
# Para cada .lean modificado en los dos worktrees: las líneas cambiadas (alineadas con difflib), la nueva despojada con
# strip-lean.awk (una línea de salida por línea de entrada) frente a la cruda. Imprime los renombres fuera del código.
import difflib, os, re, subprocess, sys
sys.stdout.reconfigure(encoding='utf-8')
B = os.path.dirname(os.path.abspath(__file__))
AWK = os.path.join(B, 'ROBINSON_PlusPlus', 'strip-lean.awk')
NUEVOS = re.compile(r"(?<![A-Za-z0-9_'.])(ite_eq_left|ite_eq_right|dite_eq_left|dite_eq_right|ite_true|ite_false)"
                    r"(?![A-Za-z0-9_'!?])")
tot_cod = tot_com = 0
ficheros = 0
for repo in ('FOL', 'ROBINSON_PlusPlus'):
    R = os.path.join(B, repo)
    nombres = subprocess.run(['git', '-C', R, 'diff', '--name-only', 'HEAD', '--', '*.lean'], capture_output=True,
                             text=True, check=True).stdout.split()
    for f in nombres:
        ficheros += 1
        viejo = subprocess.run(['git', '-C', R, 'show', 'HEAD:' + f], capture_output=True, check=True).stdout
        viejo = viejo.decode('utf-8').replace('\r\n', '\n').split('\n')
        nuevo_raw = open(os.path.join(R, f), 'rb').read()
        nuevo = nuevo_raw.decode('utf-8').replace('\r\n', '\n').split('\n')
        env = dict(os.environ, LC_ALL='C')
        desp = subprocess.run(['awk', '-f', AWK], input=nuevo_raw, capture_output=True, env=env, check=True).stdout
        desp = desp.decode('utf-8', errors='replace').replace('\r\n', '\n').split('\n')
        sm = difflib.SequenceMatcher(a=viejo, b=nuevo, autojunk=False)
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == 'equal':
                continue
            for j in range(j1, j2):
                l = nuevo[j]
                n_crudo = len(NUEVOS.findall(l))
                if n_crudo == 0:
                    continue
                n_cod = len(NUEVOS.findall(desp[j] if j < len(desp) else ''))
                tot_cod += n_cod
                if n_crudo > n_cod:
                    tot_com += n_crudo - n_cod
                    print('%s/%s:%d: %d fuera del código: %s' % (repo, f, j + 1, n_crudo - n_cod, l.strip()[:160]))
print('ficheros .lean modificados: %d' % ficheros)
print('nombres nuevos en líneas cambiadas — en CÓDIGO: %d; en comentarios o cadenas: %d' % (tot_cod, tot_com))
