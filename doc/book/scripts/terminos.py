#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
terminos.py — ningún término técnico se usa antes de estar definido.

PLAN-LIBRO.md §2.7. La regla es del lector, no del autor: alguien con bases
tiene que poder avanzar desde la primera página sin encontrarse una palabra que
el libro aún no le ha dado. **Sin exenciones.**

Cada término del vocabulario (`terminos.json`) tiene que:
  (a) introducirse en algún sitio con \\defterm{...}, y
  (b) no aparecer literalmente en el texto ANTES de esa introducción,
en el orden de lectura real, que se toma de los \\input/\\include de libro.tex.

    python3 scripts/terminos.py
"""

import io, json, os, re, sys

AQUI = os.path.dirname(os.path.abspath(__file__))
LIBRO = os.path.dirname(AQUI)

RE_INCLUIDO = re.compile(r"^\s*\\(?:input|include)\{((?:capitulos|extraido)/[^}]+)\}", re.M)
RE_DEFTERM = re.compile(r"\\defterm\{([^}]*)\}")


def expandir(fichero, vistos=None, marcas=None, base=0):
    """Devuelve el texto en el ORDEN REAL de lectura.

    Los \\input se sustituyen EN SU SITIO, no se concatenan al final: si un
    capítulo mete una sección por \\input a mitad, lo que va después de esa
    llamada se lee después de la sección, y el control tiene que verlo así.
    """
    vistos = vistos if vistos is not None else set()
    marcas = marcas if marcas is not None else []
    p0 = os.path.join(LIBRO, fichero)
    if p0 in vistos or not os.path.isfile(p0):
        return "", marcas
    vistos.add(p0)
    bruto = io.open(p0, encoding="utf-8").read()
    salida, pos = [], 0
    largo = 0
    for m in RE_INCLUIDO.finditer(bruto):
        trozo = bruto[pos:m.start()]
        salida.append(trozo)
        marcas.append((base + largo, base + largo + len(trozo), os.path.basename(p0)))
        largo += len(trozo)
        r = m.group(1)
        if not r.endswith(".tex"):
            r += ".tex"
        hijo, marcas = expandir(r, vistos, marcas, base + largo)
        salida.append(hijo)
        largo += len(hijo)
        pos = m.end()
    cola = bruto[pos:]
    salida.append(cola)
    marcas.append((base + largo, base + largo + len(cola), os.path.basename(p0)))
    return "".join(salida), marcas


def texto_ordenado():
    texto, marcas = expandir("libro.tex")
    return texto, marcas


def donde(marcas, i):
    for a, b, nombre in marcas:
        if a <= i < b:
            return nombre
    return "?"


NIVELES = {"meta", "objeto", "meta\u2192objeto", "ambos", "proyecto"}


def generar_glosario(voc):
    """El glosario se GENERA del vocabulario, no se escribe a mano.

    Así la etiqueta de nivel no puede faltar ni desviarse: la pregunta «¿esto es
    objeto o es meta?» queda contestada por construcción para cada término."""
    out = ["%% GENERADO por scripts/terminos.py — NO EDITAR (PLAN-LIBRO.md §2.7)",
           "\\begin{description}[leftmargin=0pt, style=nextline, font=\\normalfont]"]
    for e in voc["terminos"]:
        out.append("\\item[\\defterm{%s}\\hspace{0.4em}\\nivelterm{%s}] %s"
                   % (e["t"], e["nivel"], e["glosa"]))
    out.append("\\end{description}")
    destino = os.path.join(LIBRO, "extraido", "_glosario.tex")
    io.open(destino, "w", encoding="utf-8").write("\n".join(out) + "\n")


def main():
    voc = json.load(io.open(os.path.join(LIBRO, "terminos.json"), encoding="utf-8"))

    # el nivel es OBLIGATORIO: es la pregunta que no se puede dejar implícita
    sin_nivel = [e["t"] for e in voc["terminos"]
                 if e.get("nivel") not in NIVELES]
    if sin_nivel:
        for t in sin_nivel:
            print("  ✗ «%s» no declara un nivel válido %s" % (t, sorted(NIVELES)))
        print("\n✗ Todo término del glosario debe decir de qué lado está lo que nombra.\n"
              "  §2.7: la pregunta «¿esto es objeto o es meta?» no se deja implícita.",
              file=sys.stderr)
        return 1
    generar_glosario(voc)
    texto, marcas = texto_ordenado()

    # posición de cada \defterm
    definido = {}
    for m in RE_DEFTERM.finditer(texto):
        definido.setdefault(m.group(1).strip(), m.start())
    # el texto sin las llamadas a \defterm, para buscar USOS
    sin_def = RE_DEFTERM.sub(lambda m: "\x00" * (len(m.group(0))), texto)

    fallos = 0
    for entrada in voc["terminos"]:
        t = entrada["t"]
        formas = [t] + entrada.get("variantes", [])
        idef = definido.get(t)
        if idef is None:
            print("  ✗ «%s» está en el vocabulario y no se introduce con \\defterm en ninguna parte" % t)
            fallos += 1
            continue
        primer_uso, forma_usada = None, None
        for f in formas:
            for m in re.finditer(r"(?<![\w-])" + re.escape(f) + r"(?![\w-])", sin_def, re.I):
                if primer_uso is None or m.start() < primer_uso:
                    primer_uso, forma_usada = m.start(), f
                break
        if primer_uso is not None and primer_uso < idef:
            print("  ✗ «%s» se usa («%s», en %s) ANTES de definirse (en %s)"
                  % (t, forma_usada, donde(marcas, primer_uso), donde(marcas, idef)))
            fallos += 1

    if fallos:
        print("\n✗ %d término(s) del vocabulario sin introducir a tiempo.\n"
              "  §2.7 no admite exenciones: mueve el \\defterm{} antes del primer uso,\n"
              "  o introduce el término en el capítulo de Nomenclatura." % fallos,
              file=sys.stderr)
        return 1
    print("✓ %d término(s) del vocabulario, todos definidos antes de su primer uso"
          % len(voc["terminos"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
