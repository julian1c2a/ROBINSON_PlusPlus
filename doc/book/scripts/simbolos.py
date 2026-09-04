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
from extraer import cierre_de_imports, PAQUETES  # noqa: E402

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
    """Todo lo declarado, separado en producción y fuera del build."""
    prod, fuera = set(), set()
    for rel in cierre_de_imports():
        prod |= nombres_de(os.path.join(RAIZ, rel))
    for sub in ("sondeos", "cuarentena", "Probe"):
        d = os.path.join(RAIZ, sub)
        if not os.path.isdir(d):
            continue
        for f in os.listdir(d):
            if f.endswith(".lean"):
                fuera |= nombres_de(os.path.join(d, f))
    return prod, fuera


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

    prod, fuera = censo()
    desconocidos, en_sondeos = [], []
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
        else:
            desconocidos.append((n, ficheros))

    # los \modulo{} que parecen rutas de fichero deben existir
    rutas_malas = []
    for n, ficheros in sorted(modulos.items()):
        cand = n.rstrip("/:").replace("\\", "/")
        if not cand.endswith(".lean"):
            continue
        posibles = [os.path.join(RAIZ, cand)]
        for pkg, base in PAQUETES.items():
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
    for n, f in rutas_malas:
        print("  ✗ \\modulo{%s} no corresponde a ningún fichero (%s)" % (n, ", ".join(sorted(f))))
    for n, f in desconocidos:
        print("  ✗ \\ident{%s} no nombra nada declarado en el repo (%s)"
              % (n, ", ".join(sorted(f))))

    malos = len(desconocidos) + len(rutas_malas)
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
