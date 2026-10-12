import io, re, sys, glob, os

# Busca en los scripts de control las huellas de la cadena de herramientas que «come» escapes:
#   (1) un `\n` LITERAL seguido de espacios y código (una continuación de línea convertida en texto);
#   (2) caracteres de control (0x00-0x08, 0x0b, 0x0c, 0x0e-0x1f) — p. ej. el 0x01 de un `\1`;
#   (3) una cadena entre comillas dobles que se parte en dos líneas justo tras `%s` o similar
#       (un `\n` convertido en salto real dentro de un printf).
roots = sys.argv[1:]
pat_cont = re.compile(r'\\n[ \t]{2,}(\||&&|\|\||[A-Za-z])')
pat_ctrl = re.compile(r'[\x00-\x08\x0b\x0c\x0e-\x1f]')
for root in roots:
    for f in sorted(glob.glob(os.path.join(root, '*.bash')) + glob.glob(os.path.join(root, '*.awk'))
                    + glob.glob(os.path.join(root, '.github', 'workflows', '*.yml'))):
        b = io.open(f, 'rb').read()
        t = b.decode('utf-8', 'replace')
        for i, line in enumerate(t.split('\n'), 1):
            s = line.rstrip('\r')
            if pat_ctrl.search(s):
                print('%s:%d: CONTROL %r' % (f, i, s[:120]))
            if not s.lstrip().startswith('#') and pat_cont.search(s):
                print('%s:%d: CONT-LITERAL %s' % (f, i, s[:160]))
            st = s.strip()
            if re.match(r'^(printf|echo)\b', st) and st.count('"') % 2 == 1 and not st.endswith('\\'):
                print('%s:%d: COMILLA-ABIERTA %s' % (f, i, s[:160]))
