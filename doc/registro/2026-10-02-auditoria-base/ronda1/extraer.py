# -*- coding: utf-8 -*-
"""Extrae de la salida de la ronda 1 los hallazgos, los veredictos y las sondas Lean."""
import io, json, os, re

BASE = '<tmp>'
SRC = BASE + '/tasks/w76ryrfep.output'
OUT = BASE + '/scratchpad/ronda1'

obj = json.load(io.open(SRC, encoding='utf-8'))
print('claves:', list(obj.keys()))
data = None
for k, v in obj.items():
    if isinstance(v, list) and v and isinstance(v[0], dict) and 'lente' in v[0]:
        data = v
        print('resultado en la clave:', k)
        break
assert data is not None, 'no encuentro el array de resultados'

resumen = []
for r in data:
    lente = r.get('lente')
    a = r.get('auditoria') or {}
    v = r.get('verificacion') or {}
    vid = {x.get('id'): x for x in (v.get('veredictos') or [])}
    resumen.append('=' * 100)
    resumen.append('LENTE %s — %s' % (lente, a.get('lente')))
    resumen.append('RESUMEN: ' + (a.get('resumen') or ''))
    for h in a.get('hallazgos') or []:
        hid = h.get('id')
        ver = vid.get(hid, {})
        resumen.append('-' * 100)
        resumen.append('[%s] %s | %s/%s | %s | conf=%s' % (hid, h.get('titulo'), h.get('gravedad'), h.get('nivel'),
                                                       h.get('medido_o_estimado'), h.get('confianza')))
        resumen.append('  AFIRMACION: ' + (h.get('afirmacion') or ''))
        resumen.append('  POR QUE FRENA: ' + (h.get('por_que_frena') or ''))
        resumen.append('  RELACION F1: ' + (h.get('relacion_con_F1') or ''))
        resumen.append('  ARREGLO: ' + (h.get('arreglo_propuesto') or ''))
        resumen.append('  EVIDENCIA: ' + ' || '.join(h.get('evidencia') or []))
        resumen.append('  VEREDICTO: %s (grav. corregida: %s; compilar: %s)' % (ver.get('veredicto'), ver.get('gravedad_corregida'),
                                                                               ver.get('necesita_compilacion')))
        resumen.append('  RAZON VERIF: ' + (ver.get('razon') or ''))
        if ver.get('evidencia_contraria'):
            resumen.append('  CONTRA: ' + ' || '.join(ver.get('evidencia_contraria')))
        sonda = (h.get('sonda_lean') or '').strip()
        if sonda:
            fn = os.path.join(OUT, 'sonda_%s.lean' % re.sub(r'[^A-Za-z0-9_-]', '_', hid))
            io.open(fn, 'w', encoding='utf-8').write(sonda + '\n')
            resumen.append('  SONDA -> ' + fn + ' (%d lineas)' % (sonda.count('\n') + 1))
    resumen.append('-' * 100)
    resumen.append('OMISIONES (verificador): ' + ' || '.join(v.get('omisiones') or []))
    resumen.append('NO EXAMINADO (auditor): ' + ' || '.join(a.get('no_examinado') or []))

io.open(os.path.join(OUT, 'resumen.txt'), 'w', encoding='utf-8').write('\n'.join(resumen) + '\n')
print('lentes: %d' % len(data))
for r in data:
    a = r.get('auditoria') or {}
    v = r.get('verificacion') or {}
    cuenta = {}
    for x in v.get('veredictos') or []:
        cuenta[x.get('veredicto')] = cuenta.get(x.get('veredicto'), 0) + 1
    print('  %-14s hallazgos=%2d  veredictos=%s' % (r.get('lente'), len(a.get('hallazgos') or []), cuenta))
