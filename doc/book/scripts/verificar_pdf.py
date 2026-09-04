#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
verificar_pdf.py — comprueba que el código IMPRESO es el código del repo.

Por qué existe. El 2026-09-03, `listings` imprimía `φ( : Formula)` donde el
fuente dice `(φ : Formula)`: alteraba el código en silencio, exactamente lo que
PLAN-LIBRO.md §2.1 prohíbe, y sólo se detectó leyendo el PDF a ojo. Que un
principio editorial dependa de que alguien mire no es un control.

Este script cierra el ciclo ENTERO: lee la declaración DEL MÓDULO .lean (no del
fichero intermedio de extraido/, que podría estar corrupto o desactualizado) y
comprueba que cada una de sus líneas aparece en el texto del PDF. Compara sin
espacios, porque el salto de línea de fvextra introduce '↪' y sangrado propios.

Control positivo: corrompe un extraido/*.tex, recompila, y esto DEBE fallar.
"""

import json, io, os, re, subprocess, sys

AQUI = os.path.dirname(os.path.abspath(__file__))
LIBRO = os.path.dirname(AQUI)
RAIZ = os.path.abspath(os.path.join(LIBRO, "..", ".."))
PDF = os.path.join(LIBRO, "libro.pdf")
LOG = os.path.join(LIBRO, "libro.log")

# Tolerancia de maquetación, en puntos. Una caja que se sale de la caja de texto
# es un defecto visible; se detectó uno de 88 pt (una tabla del cap. 2) MIRANDO
# el PDF, y depender de que alguien mire no es un control.
TOL_PT = float(os.environ.get("MAQUETA_TOL", "0.1"))


def revisar_maquetacion():
    """Falla si LaTeX ha dejado material fuera de la caja de texto."""
    if not os.path.isfile(LOG):
        return 0
    txt = io.open(LOG, encoding="utf-8", errors="replace").read()
    malos = [(float(m.group(1)), m.group(0))
             for m in re.finditer(r"Overfull \\hbox \(([0-9.]+)pt too wide\)[^\n]*", txt)
             if float(m.group(1)) > TOL_PT]
    for pt, linea in malos:
        print("  ✗ maquetación: %s" % linea)
    if malos:
        print("\n✗ %d caja(s) fuera de la caja de texto. Suele ser una tabla: pásala a\n"
              "  `tabularx` con una columna X, y saca de la tabla cualquier cabecera\n"
              "  \\multicolumn larga (en una celda `l` no parte líneas)." % len(malos),
              file=sys.stderr)
    return len(malos)


# «›» (U+203A) es el símbolo de continuación de línea del preámbulo. Se eligió
# precisamente porque NO aparece en el código Lean del proyecto ni de FOL, así
# que quitarlo aquí no puede ocultar una diferencia real.
CONTINUACION = "\u203a"
# «…» marca la prueba elidida por `solo_firma`. NO se puede ignorar en todo el
# texto: aparece en 43 ficheros .lean del proyecto. Sólo se quita cuando CIERRA
# la línea, que es donde el extractor lo pone; lo de su izquierda es verbatim.
ELISION = "\u2026"


def normalizar(t):
    return re.sub(r"[\s" + CONTINUACION + "]+", "", t)


def main():
    if not os.path.isfile(PDF):
        print("✗ no hay libro.pdf: compila antes", file=sys.stderr); return 2
    try:
        txt = subprocess.check_output(["pdftotext", "-layout", PDF, "-"]).decode("utf-8", "replace")
    except FileNotFoundError:
        print("⚠ pdftotext no disponible: no se ha podido verificar el PDF"); return 0
    plano = normalizar(txt)

    sys.path.insert(0, AQUI)
    from extraer import codigo_para  # MISMA lectura del .lean que el extractor

    man = json.load(io.open(os.path.join(LIBRO, "fragmentos.json"), encoding="utf-8"))
    fallos = 0
    for fr in man["fragmentos"]:
        ruta = os.path.join(RAIZ, fr["modulo"])
        codigo, _ = codigo_para(fr, ruta)
        if codigo is None:
            print("  ✗ [%s] la declaración ya no está en %s" % (fr["clave"], fr["modulo"]))
            fallos += 1
            continue
        for ln in codigo.split("\n"):
            if not ln.strip():
                continue
            if ln.rstrip().endswith(ELISION):
                ln = ln.rstrip()[:-len(ELISION)]
            if normalizar(ln) not in plano:
                print("  ✗ [%s] el PDF NO imprime esta línea del repo:\n      %s"
                      % (fr["clave"], ln.strip()))
                fallos += 1
    fallos += revisar_maquetacion()

    if fallos:
        print("\n✗ VERIFICACIÓN DEL PDF FALLIDA — %d línea(s) del repo que el PDF "
              "no imprime tal cual, o defectos de maquetación (PLAN-LIBRO.md §2.1)."
              % fallos, file=sys.stderr)
        return 1
    print("✓ el código impreso coincide con el del repo (%d fragmentos) "
          "y nada se sale de la caja de texto" % len(man["fragmentos"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
