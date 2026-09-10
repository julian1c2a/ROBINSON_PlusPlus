#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
simbolos.py — todo identificador que el libro nombra tiene que EXISTIR.

Por qué. `verificar_pdf.py` comprueba que el código IMPRESO es el del repo, y
`extraer.py` que los teoremas citados están en el build. Ninguno de los dos mira
la PROSA: un capítulo puede nombrar tranquilamente un símbolo que no existe.

Y no es un riesgo teórico. El 2026-09-03 aparecieron cuatro afirmaciones falsas
en docstrings de producción —`DescMutua`, `S_Descenso`, `prf_isTermCodeE1_of_In`
entre ellas—, y esos docstrings son material fuente del libro. `lake build` en
verde garantiza los teoremas, no la prosa que los rodea. Ver
DOCSTRINGS-NO-FIABLES.md y PLAN-LIBRO.md §2.6.

Este script recoge cada \\ident{...} y \\modulo{...} de los capítulos y comprueba
que nombra algo real, diciendo dónde: producción, sondeos, o en ninguna parte.

    python3 scripts/simbolos.py            # informe
    python3 scripts/simbolos.py --estricto # falla si hay desconocidos
"""

import io, json, os, re, sys

AQUI = os.path.dirname(os.path.abspath(__file__))
LIBRO = os.path.dirname(AQUI)
RAIZ = os.path.abspath(os.path.join(LIBRO, "..", ".."))
EXENTOS = os.path.join(LIBRO, "simbolos-exentos.json")

sys.path.insert(0, AQUI)
from extraer import cierre_de_imports, PAQUETES, PROYECTOS_CITADOS  # noqa: E402

RE_IDENT = re.compile(r"\\ident\{([^}]*)\}")
# \ident{} admite expresiones; se trocea en identificadores y se comprueban todos.
RE_TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*[?!]?")
RE_MODULO = re.compile(r"\\modulo\{([^}]*)\}")
RE_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|instance|structure|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'₀-₉]*[?!]?)")
RE_ESPACIO = re.compile(r"^(?:namespace|section)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
RE_CTOR = re.compile(r"^\s*\|\s*([a-zA-Z_][A-Za-z0-9_'₀-₉]*[?!]?)")


def sin_comentarios(texto):
    """Quita los comentarios de LaTeX (un % no escapado hasta fin de línea).

    Conserva los saltos de línea para que los números de línea no se muevan.
    """
    fuera = []
    for linea in texto.split("\n"):
        i, corte = 0, None
        while i < len(linea):
            c = linea[i]
            if c == "\\":
                i += 2
                continue
            if c == "%":
                corte = i
                break
            i += 1
        fuera.append(linea if corte is None else linea[:corte])
    return "\n".join(fuera)


def nombres_de(ruta):
    out = set()
    try:
        txt = io.open(ruta, encoding="utf-8", errors="replace").read()
    except OSError:
        return out
    for ln in txt.split("\n"):
        for rx in (RE_DECL, RE_ESPACIO, RE_CTOR):
            m = rx.match(ln)
            if m:
                out.add(m.group(1))
                out.add(m.group(1).split(".")[-1])
    return out


def censo():
    """Todo lo declarado, en tres capas: producción, fuera del build, y otros
    proyectos citados como evidencia (que no sostienen nada de este libro)."""
    prod, fuera, citados = set(), set(), set()
    for rel in cierre_de_imports():
        prod |= nombres_de(os.path.join(RAIZ, rel))
    for sub in ("sondeos", "cuarentena", "Probe"):
        d = os.path.join(RAIZ, sub)
        if not os.path.isdir(d):
            continue
        for f in os.listdir(d):
            if f.endswith(".lean"):
                fuera |= nombres_de(os.path.join(d, f))
    for base in PROYECTOS_CITADOS.values():
        raiz = os.path.normpath(os.path.join(RAIZ, base))
        for dir_, _, ficheros in os.walk(raiz):
            if ".lake" in dir_.split(os.sep):
                continue
            for f in ficheros:
                if f.endswith(".lean"):
                    citados |= nombres_de(os.path.join(dir_, f))
    return prod, fuera, citados


def main():
    estricto = "--estricto" in sys.argv
    exentos = {}
    if os.path.isfile(EXENTOS):
        exentos = json.load(io.open(EXENTOS, encoding="utf-8")).get("exentos", {})

    caps = os.path.join(LIBRO, "capitulos")
    idents, modulos = {}, {}
    for f in sorted(os.listdir(caps)):
        if not f.endswith(".tex"):
            continue
        txt = io.open(os.path.join(caps, f), encoding="utf-8").read()
        for bruto in RE_IDENT.findall(txt):
            for n in RE_TOKEN.findall(bruto):
                idents.setdefault(n, set()).add(f)
        for n in RE_MODULO.findall(txt):
            modulos.setdefault(n.strip(), set()).add(f)

    prod, fuera, citados = censo()
    desconocidos, en_sondeos, en_otros = [], [], []
    for n, ficheros in sorted(idents.items()):
        # Las metavariables de una o dos letras (`h`, `t`, `Γ`) no son
        # declaraciones y no se pueden comprobar; tampoco son nunca el tipo de
        # afirmación que se descubre falsa.
        if not n or len(n) <= 2 or n in exentos:
            continue
        corto = n.split(".")[-1]
        if corto in prod or n in prod:
            continue
        if corto in fuera or n in fuera:
            en_sondeos.append((n, ficheros))
        elif corto in citados or n in citados:
            en_otros.append((n, ficheros))
        else:
            desconocidos.append((n, ficheros))

    # los \modulo{} que parecen rutas de fichero deben existir
    rutas_malas = []
    for n, ficheros in sorted(modulos.items()):
        cand = n.rstrip("/:").replace("\\", "/")
        if not cand.endswith(".lean"):
            continue
        posibles = [os.path.join(RAIZ, cand)]
        for pkg, base in list(PAQUETES.items()) + list(PROYECTOS_CITADOS.items()):
            posibles.append(os.path.normpath(os.path.join(RAIZ, base, cand)))
            if cand.startswith(pkg + "/"):
                posibles.append(os.path.normpath(os.path.join(RAIZ, base, cand)))
        if not any(os.path.isfile(p) for p in posibles):
            rutas_malas.append((n, ficheros))

    if en_sondeos:
        print("· %d identificador(es) que sólo existen FUERA del build "
              "(sondeos/cuarentena) — el texto debe decirlo:" % len(en_sondeos))
        for n, f in en_sondeos:
            print("    %-38s %s" % (n, ", ".join(sorted(f))))
    if en_otros:
        print("· %d identificador(es) de OTRO proyecto citado —evidencia, no base:"
              % len(en_otros))
        for n, f in en_otros:
            print("    %-38s %s" % (n, ", ".join(sorted(f))))
    for n, f in rutas_malas:
        print("  ✗ \\modulo{%s} no corresponde a ningún fichero (%s)" % (n, ", ".join(sorted(f))))
    for n, f in desconocidos:
        print("  ✗ \\ident{%s} no nombra nada declarado en el repo (%s)"
              % (n, ", ".join(sorted(f))))

    # --- números de capítulo escritos a mano (§2.9) --------------------------
    # Un «capítulo 13» en el texto deja de ser cierto en cuanto se reordena el
    # libro, y nada lo avisa. Se usa \\ref/\\cref si el capítulo existe, y
    # \\capfuturo{...} si todavía no.
    # Números ÁRABES en capítulos y partes, y además ROMANOS en las partes: el
    # 2026-09-09 tres capítulos decían «Parte IV» después de que esa parte
    # pasara a ser la V, y la primera versión de este control no lo veía.
    # También los CONTADOS con palabras («los tres capítulos siguientes»): un
    # recuento a mano deriva igual que un número, y además calla al hacerlo.
    # Sólo «capítulos», no «partes»: «las dos partes se reduzcan al mismo
    # término» habla de una ecuación, y ese falso positivo es más caro que el
    # riesgo que cubre — las partes del libro se cuentan con los ojos.
    RE_CAPNUM = re.compile(r"(?:cap[ií]tulo)s?~? *[0-9]+"
                           r"|[Pp]artes?~? *(?:[0-9]+|[IVX]+\b)"
                           r"|(?:dos|tres|cuatro|cinco|seis|siete|ocho|nueve|diez)"
                           r" +cap[ií]tulos\b")
    a_mano = []
    for f in sorted(os.listdir(caps)):
        if not f.endswith(".tex"):
            continue
        # Los comentarios de LaTeX no llegan al lector: un «Parte I» dentro de
        # un %% es una nota para nosotros, no una referencia que pueda quedar
        # desfasada ante nadie. Se descartan antes de buscar.
        texto = sin_comentarios(io.open(os.path.join(caps, f), encoding="utf-8").read())
        for m in RE_CAPNUM.finditer(texto):
            a_mano.append((m.group(0), f))
    for t, f in a_mano:
        print("  ✗ «%s» es un número de capítulo escrito a mano (%s): usa "
              "\\ref{} o \\capfuturo{}" % (t, f))

    # --- Markdown que se cuela en el LaTeX ----------------------------------
    # Todo el material de partida de este libro está en Markdown, y copiar un
    # párrafo trae su sintaxis: `**negrita**` sale IMPRESA con los asteriscos,
    # y nadie lo ve porque LaTeX no protesta. El 2026-09-09 había tres casos en
    # tres capítulos distintos. Los acentos graves también, aunque hoy no haya
    # ninguno: en los capítulos el código va por \ident/\leanfrag, nunca en crudo.
    # `[^*]` y no `[^*\n]`: una negrita de Markdown copiada de un `.md` acaba
    # partida en dos líneas al reajustar el párrafo, y así NO se veía. Pasó
    # el 2026-09-10, en el capítulo de autorreferencia.
    RE_MD = re.compile(r"\*\*[^*]{1,200}\*\*"           # **negrita**, aunque parta línea
                       r"|`[^`\n]*`"                 # `código`
                       r"|^#{1,6} ", re.M)           # # encabezado
    md = []
    for f in sorted(os.listdir(caps)):
        if not f.endswith(".tex"):
            continue
        texto = sin_comentarios(io.open(os.path.join(caps, f), encoding="utf-8").read())
        for m in RE_MD.finditer(texto):
            md.append((m.group(0).strip()[:44], f))
    for t, f in md:
        print("  ✗ «%s» es sintaxis Markdown dentro del LaTeX (%s): se imprime "
              "tal cual" % (t, f))

    malos = len(desconocidos) + len(rutas_malas) + len(a_mano) + len(md)
    if malos and estricto:
        print("\n✗ %d símbolo(s) sin respaldo. Un identificador que el libro nombra tiene\n"
              "  que existir, o estar declarado en simbolos-exentos.json con su razón\n"
              "  (histórico, retirado, propuesto, palabra de Lean…). PLAN-LIBRO.md §2.6."
              % malos, file=sys.stderr)
        return 1
    print("✓ %d identificador(es) y %d módulo(s) citados; %d sin respaldo%s"
          % (len(idents), len(modulos), malos, "" if estricto else " (informativo)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
