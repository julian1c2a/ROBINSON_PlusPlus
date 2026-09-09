#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
revisar.py — el bucle de revisión: LaTeX → Markdown → tus retoques → LaTeX.

PLAN-LIBRO.md §2.10. El LaTeX sigue siendo LA FUENTE; este Markdown es una
VISTA para leer y anotar. Lo que escribes no se pierde nunca, porque no vive en
el fichero: vive en la bitácora, que es acumulativa.

    python3 scripts/revisar.py generar    # LaTeX → revision/LIBRO.md
    python3 scripts/revisar.py recoger    # tus cambios → bitácora
    python3 scripts/revisar.py responder N-0003 "texto" --estado aplicada
    python3 scripts/revisar.py estado     # qué hay abierto

CÓMO SE ANOTA. Escribe donde quieras una línea que empiece por `>>`:

    >> esto no se entiende: ¿un reflector es meta u objeto?

Varias líneas seguidas con `>>` son una sola nota. Y si prefieres reescribir la
prosa directamente, hazlo: `recoger` saca el diff y yo lo llevo al LaTeX.

QUÉ NO SE PUEDE TOCAR. Los bloques de código son código EXTRAÍDO del repo
(§2.1). Editarlos ahí no tiene ningún efecto: la próxima extracción los vuelve
a poner como están en el código. `recoger` avisa si el diff los toca.

POR QUÉ NO SE PIERDE NADA SI TE DESFASAS. `recoger` compara tu fichero con la
copia exacta de lo último que se generó (`.base.md`), no con el LaTeX de hoy.
Si anotas sobre una versión vieja, tus notas se recogen igual; las que quedan
sin sitio se re-emiten al principio, marcadas como huérfanas, con su extracto
para poder recolocarlas. Y la bitácora conserva la conversación entera
—tus notas y mis respuestas— aunque el párrafo que las motivó ya no exista.
"""

import io, json, os, re, sys, difflib, datetime

AQUI = os.path.dirname(os.path.abspath(__file__))
LIBRO = os.path.dirname(AQUI)
REV = os.path.join(LIBRO, "revision")
MD = os.path.join(REV, "LIBRO.md")
BASE = os.path.join(REV, ".base.md")
JSON_BIT = os.path.join(REV, "bitacora.json")
MD_BIT = os.path.join(REV, "BITACORA.md")

sys.path.insert(0, AQUI)
from extraer import codigo_para, RAIZ  # noqa: E402

HOY = datetime.date.today().isoformat()

RE_INCLUIDO = re.compile(r"^\s*\\(?:input|include)\{((?:capitulos|extraido)/[^}]+)\}", re.M)
RE_NOTA = re.compile(r"^>>.*(?:\n>>.*)*", re.M)
RE_ANCLA = re.compile(r"^<!-- @([A-Za-z0-9_\-]+):(\d+) -->$", re.M)

# La marca de nota es `>>`, pero el autocorrector de LibreOffice/Word convierte
# `>>` en `»` en cuanto escribes detrás. Se aceptan las dos, y también el `»`
# que queda a mitad de línea cuando el procesador reflowea el párrafo.
RE_MARCA = re.compile(r"^\s*(?:>>|»)\s?")
RE_MARCA_INTERNA = re.compile(r"\s*»\s*")


def es_marca(linea):
    return bool(RE_MARCA.match(linea))


def limpia_nota(lineas):
    """Quita la marca inicial y los `»` que el reflow dejó dentro."""
    fuera = []
    for l in lineas:
        l = RE_MARCA.sub("", l)
        l = RE_MARCA_INTERNA.sub(" ", l)
        fuera.append(re.sub(r"[ \t]+", " ", l).strip())
    return "\n".join(x for x in fuera if x).strip()


# ---------------------------------------------------------------------------
# LaTeX -> Markdown
# ---------------------------------------------------------------------------

ENTORNOS = {
    "leccion": ("[LECCION]", "Lección"),
    "muro": ("[MURO]", "Muro"),
    "refutado": ("[REFUTADO]", "Refutado"),
    "matematica": ("[MATEMATICA]", "Matemática"),
    "observacion": ("[OBSERVACION]", "Observación"),
    "teorema": ("[TEOREMA]", "Teorema"),
}

RE_CMD1 = [
    (re.compile(r"\\ident\{([^{}]*)\}"), r"`\1`"),
    (re.compile(r"\\modulo\{([^{}]*)\}"), r"`\1`"),
    (re.compile(r"\\doc\{([^{}]*)\}"), r"`\1`"),
    (re.compile(r"\\texttt\{([^{}]*)\}"), r"`\1`"),
    (re.compile(r"\\textbf\{([^{}]*)\}"), r"**\1**"),
    (re.compile(r"\\emph\{([^{}]*)\}"), r"*\1*"),
    (re.compile(r"\\textit\{([^{}]*)\}"), r"*\1*"),
    (re.compile(r"\\textsc\{([^{}]*)\}"), r"\1"),
    (re.compile(r"\\defterm\{([^{}]*)\}"), r"**\1**"),
    (re.compile(r"\\defnot\{([^{}]*)\}"), r"\1"),
    (re.compile(r"\\nivelterm\{([^{}]*)\}"), r" (nivel: \1)"),
    (re.compile(r"\\adr\{([^{}]*)\}"), r"ADR-\1"),
    (re.compile(r"\\capfuturo\{([^{}]*)\}"), r"«el capítulo dedicado a \1» (aún sin escribir)"),
    (re.compile(r"\\partefutura\{([^{}]*)\}"), r"«la parte dedicada a \1» (aún sin escribir)"),
    (re.compile(r"\\selee\{«?(.*?)»?\}", re.S), r"→ *se lee:* «\1»"),
    (re.compile(r"\\printaxioms"), r"`#print axioms`"),
    (re.compile(r"\\noindent\s*"), r""),
    (re.compile(r"\\texorpdfstring\{([^{}]*)\}\{[^{}]*\}"), r"\1"),
    (re.compile(r"\\label\{[^}]*\}"), r""),
    (re.compile(r"~"), " "),
]


def sin_comentarios(texto):
    fuera = []
    for linea in texto.split("\n"):
        i, corte = 0, None
        while i < len(linea):
            if linea[i] == "\\":
                i += 2
                continue
            if linea[i] == "%":
                corte = i
                break
            i += 1
        fuera.append(linea if corte is None else linea[:corte].rstrip())
    return "\n".join(fuera)


def inline(t, refs):
    """Traduce lo que va DENTRO de un párrafo. La matemática se deja intacta."""
    def ref(m):
        clave = m.group(1)
        return "[-> %s]" % refs.get(clave, "«" + clave + "», sin resolver")
    t = re.sub(r"\\(?:c?ref)\{([^}]*)\}", ref, t)
    for _ in range(3):                      # macros anidadas: \textbf{\ident{x}}
        for rx, rep in RE_CMD1:
            t = rx.sub(rep, t)
    t = re.sub(r"[ \t]+", " ", t)
    return t.strip()


def tabla_markdown(cuerpo, refs):
    """tabular/tabularx -> tabla de Markdown. Devuelve None si no cuadra."""
    cuerpo = re.sub(r"\\(?:top|mid|bottom)rule|\\hline", "", cuerpo)
    filas = [f.strip() for f in cuerpo.split("\\\\") if f.strip()]
    if not filas:
        return None
    out, ancho = [], None
    for f in filas:
        celdas = [inline(c, refs) for c in f.split("&")]
        if ancho is None:
            ancho = len(celdas)
            out.append("| " + " | ".join(celdas) + " |")
            out.append("|" + "---|" * ancho)
            continue
        if len(celdas) != ancho:
            return None
        out.append("| " + " | ".join(celdas) + " |")
    return "\n".join(out) if len(out) > 2 else None


def convertir(ruta, slug, refs, contador):
    """Un fichero .tex -> lista de bloques Markdown, cada uno con su ancla."""
    texto = sin_comentarios(io.open(ruta, encoding="utf-8").read())
    bloques = []
    lineas = texto.split("\n")
    i = 0

    def emitir(md, anclable=True):
        md = md.strip()
        if not md:
            return
        if anclable:
            contador[0] += 1
            bloques.append(("<!-- @%s:%d -->" % (slug, contador[0]), md))
        else:
            bloques.append((None, md))

    parrafo = []

    def cerrar():
        if parrafo:
            emitir(inline(" ".join(parrafo), refs))
            del parrafo[:]

    while i < len(lineas):
        s = lineas[i].strip()

        m = re.match(r"\\(chapter|section|subsection)\*?\{(.*)\}\s*$", s)
        if m:
            cerrar()
            nivel = {"chapter": "##", "section": "###", "subsection": "####"}[m.group(1)]
            emitir("%s %s" % (nivel, inline(m.group(2), refs)), anclable=False)
            i += 1
            continue

        m = re.match(r"\\leanfrag\{([^}]*)\}", s)
        if m:
            cerrar()
            emitir(fragmento_md(m.group(1)), anclable=False)
            i += 1
            continue

        m = re.match(r"\\begin\{(\w+)\}(?:\[(.*)\])?", s)
        if m:
            cerrar()
            ent = m.group(1)
            j, cuerpo, hondura = i + 1, [], 1
            while j < len(lineas):
                if lineas[j].strip().startswith("\\begin{%s}" % ent):
                    hondura += 1
                if lineas[j].strip().startswith("\\end{%s}" % ent):
                    hondura -= 1
                    if hondura == 0:
                        break
                cuerpo.append(lineas[j])
                j += 1
            emitir(entorno_md(ent, m.group(2), "\n".join(cuerpo), refs))
            i = j + 1
            continue

        if not s:
            cerrar()
            i += 1
            continue

        parrafo.append(s)
        i += 1

    cerrar()
    return bloques


def entorno_md(ent, titulo, cuerpo, refs):
    if ent in ("center", "small"):
        return entorno_interior(cuerpo, refs)
    if ent in ("tabular", "tabularx"):
        cuerpo = re.sub(r"^\s*(\{[^}]*\}|\[[^\]]*\]|\\linewidth)+", "", cuerpo, count=1)
        t = tabla_markdown(cuerpo, refs)
        return t if t else "```latex\n" + cuerpo.strip() + "\n```"
    if ent in ("itemize", "enumerate"):
        vinieta = "-" if ent == "itemize" else "1."
        trozos = [t.strip() for t in re.split(r"\\item", cuerpo) if t.strip()]
        return "\n".join("%s %s" % (vinieta, inline(t, refs)) for t in trozos)
    if ent in ENTORNOS:
        icono, nombre = ENTORNOS[ent]
        cab = "%s **%s%s**" % (icono, nombre, (" — " + inline(titulo, refs)) if titulo else "")
        dentro = entorno_interior(cuerpo, refs)
        return "\n".join(["> " + cab, ">"] + ["> " + l for l in dentro.split("\n")])
    return entorno_interior(cuerpo, refs)


def entorno_interior(cuerpo, refs):
    """El interior de un entorno: puede traer tablas, listas y párrafos."""
    salida, i = [], 0
    lineas = cuerpo.split("\n")
    parrafo = []
    while i < len(lineas):
        s = lineas[i].strip()
        m = re.match(r"\\begin\{(\w+)\}(?:\[(.*)\])?", s)
        if m:
            if parrafo:
                salida.append(inline(" ".join(parrafo), refs)); parrafo = []
            ent = m.group(1)
            j, dentro, hondura = i + 1, [], 1
            while j < len(lineas):
                if lineas[j].strip().startswith("\\begin{%s}" % ent):
                    hondura += 1
                if lineas[j].strip().startswith("\\end{%s}" % ent):
                    hondura -= 1
                    if hondura == 0:
                        break
                dentro.append(lineas[j]); j += 1
            salida.append(entorno_md(ent, m.group(2), "\n".join(dentro), refs))
            i = j + 1
            continue
        if not s:
            if parrafo:
                salida.append(inline(" ".join(parrafo), refs)); parrafo = []
            i += 1
            continue
        parrafo.append(s)
        i += 1
    if parrafo:
        salida.append(inline(" ".join(parrafo), refs))
    return "\n\n".join(x for x in salida if x.strip())


def fragmento_md(clave):
    """El código, LEÍDO DEL REPO — no del .tex generado. Es §2.1 otra vez."""
    man = json.load(io.open(os.path.join(LIBRO, "fragmentos.json"), encoding="utf-8"))
    for fr in man["fragmentos"]:
        if fr["clave"] != clave:
            continue
        ruta = os.path.join(RAIZ, fr["modulo"])
        codigo, linea = codigo_para(fr, ruta)
        if codigo is None:
            return "```lean\n(no se encuentra `%s` en %s)\n```" % (fr["decl"], fr["modulo"])
        cab = "%s . %s (linea %d) -- CODIGO DEL REPO, no se edita aqui" % (
            fr["modulo"], fr["decl"], linea)
        return "```lean\n-- %s\n%s\n```" % (cab, codigo)
    return "```lean\n(fragmento `%s` no esta en fragmentos.json)\n```" % clave


def referencias():
    """\\ref{} -> el numero real, leido del .aux; si no hay .aux, el nombre."""
    refs = {}
    caps = os.path.join(LIBRO, "capitulos")
    ficheros = [os.path.join(LIBRO, "libro.aux")]
    if os.path.isdir(caps):
        ficheros += [os.path.join(caps, x) for x in os.listdir(caps) if x.endswith(".aux")]
    for f in ficheros:
        if not os.path.isfile(f):
            continue
        bruto = io.open(f, encoding="utf-8", errors="replace").read()
        for m in re.finditer(r"\\newlabel\{([^}]+)\}\{\{([^}]*)\}", bruto):
            clave, num = m.group(1), m.group(2)
            if clave.endswith("@cref"):
                continue
            tipo = ("parte" if clave.startswith("parte:")
                    else "cap." if clave.startswith("cap:") else "§")
            refs[clave] = "%s %s" % (tipo, num)
    return refs


# ---------------------------------------------------------------------------
# La bitácora: el estado que sobrevive a todo
# ---------------------------------------------------------------------------

def cargar():
    if os.path.isfile(JSON_BIT):
        return json.load(io.open(JSON_BIT, encoding="utf-8"))
    return {"_comentario": [
        "LA BITÁCORA de la revisión (PLAN-LIBRO.md §2.10). Es el ESTADO, y es",
        "acumulativa: nada se borra nunca. BITACORA.md es su lectura humana, y",
        "se regenera de aquí — no se edita a mano.",
        "  estado: abierta | aplicada | discutida | descartada",
    ], "siguiente": 1, "entradas": []}


def guardar(b):
    os.makedirs(REV, exist_ok=True)
    json.dump(b, io.open(JSON_BIT, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    io.open(JSON_BIT, "a", encoding="utf-8").write("\n")
    escribir_bitacora_md(b)


def escribir_bitacora_md(b):
    L = ["# Bitácora de la revisión", "",
         "Generado por `scripts/revisar.py` — **no se edita a mano**: sale de "
         "`bitacora.json`.", "",
         "Aquí está la conversación entera sobre el texto, en orden. Nada se borra: "
         "una nota descartada sigue estando, con la razón. Si en `LIBRO.md` no "
         "encuentras una nota tuya, es que está cerrada — búscala aquí.", ""]
    abiertas = [e for e in b["entradas"] if e.get("estado") == "abierta"]
    L += ["**Abiertas ahora mismo: %d.** Total de entradas: %d."
          % (len(abiertas), len(b["entradas"])), "", "---", ""]
    for e in b["entradas"]:
        if e.get("tipo") == "edicion":
            L += ["## %s · %s — retoque de prosa" % (e["id"], e["fecha"]), "",
                  "*Estado: %s.* %s" % (e.get("estado", "abierta"), e.get("resumen", "")), "",
                  "```diff", e["diff"].rstrip(), "```", ""]
        else:
            L += ["## %s · %s — %s" % (e["id"], e["fecha"], e.get("capitulo", "?")), "",
                  "*Estado: **%s**. Ancla: `%s`.*" % (e.get("estado", "abierta"),
                                                      e.get("ancla", "—")), "",
                  "> Contexto: %s" % e.get("extracto", "").replace("\n", " ")[:200], "",
                  "**JULIÁN:**", ""]
            L += ["> " + l for l in e["nota"].split("\n")]
            L += [""]
        for r in e.get("respuestas", []):
            L += ["**%s** (%s):" % (r["autor"].upper(), r["fecha"]), ""]
            L += ["> " + l for l in r["texto"].split("\n")]
            L += [""]
        L += ["---", ""]
    io.open(MD_BIT, "w", encoding="utf-8").write("\n".join(L))


# ---------------------------------------------------------------------------
# generar
# ---------------------------------------------------------------------------

CABECERA = """<!-- GENERADO por scripts/revisar.py — esta es una VISTA del libro.
     La fuente sigue siendo el LaTeX de capitulos/. -->

# Incompletitud, formalizada — copia de revisión

*Generado el %s. %d páginas en el PDF, %d fragmentos de código.*

**Cómo usar este fichero.**

- Para **comentar**, escribe una línea que empiece por `>>`. Varias seguidas son
  una sola nota. Escribe donde quieras: la nota se ancla al bloque anterior.
- Para **retocar la prosa**, edítala aquí directamente. Se recoge como diff y yo
  la llevo al LaTeX (que es lo único que se imprime).
- Los bloques ```lean``` **no se editan**: son código extraído del repositorio.
  Si algo está mal ahí, es el código lo que hay que cambiar, no el libro.
- Cuando termines, dímelo y ejecuto `make recoger`.

Nada de lo que escribas se pierde aunque yo regenere este fichero, y aunque lo
escribas sobre una versión vieja: todo va a `BITACORA.md`, que es acumulativa.

---
"""


def generar():
    b = cargar()
    refs = referencias()
    libro = sin_comentarios(io.open(os.path.join(LIBRO, "libro.tex"), encoding="utf-8").read())

    partes = []
    for m in re.finditer(r"\\part\{(.+?)\}|" + RE_INCLUIDO.pattern, libro, re.M):
        if m.group(1):
            partes.append(("part", m.group(1)))
        elif m.group(2):
            partes.append(("cap", m.group(2)))

    # notas abiertas, indexadas por el extracto que las ancló
    abiertas = [e for e in b["entradas"]
                if e.get("estado") == "abierta" and e.get("tipo") != "edicion"]
    colocadas = set()

    cuerpo, contador = [], [0]
    for tipo, val in partes:
        if tipo == "part":
            cuerpo.append(("\n# %s\n" % inline(val, refs), None))
            continue
        rel = val if val.endswith(".tex") else val + ".tex"
        ruta = os.path.join(LIBRO, rel)
        if not os.path.isfile(ruta) or "/extraido/" in rel.replace("\\", "/"):
            continue
        slug = os.path.splitext(os.path.basename(rel))[0]
        contador[0] = 0
        for ancla, md in convertir(ruta, slug, refs, contador):
            cuerpo.append((md, ancla))
            if ancla is None:
                continue
            clave = normaliza(md)
            for e in abiertas:
                if e["id"] in colocadas:
                    continue
                if e.get("clave_extracto") and e["clave_extracto"] == clave:
                    cuerpo.append((render_nota(e), None))
                    colocadas.add(e["id"])

    huerfanas = [e for e in abiertas if e["id"] not in colocadas]

    salida = [CABECERA % (HOY, paginas(), n_fragmentos())]
    if huerfanas:
        salida.append("## ⚠️ Notas sin sitio\n\n"
                      "El párrafo al que iban ya no está como estaba —lo he tocado, o lo has "
                      "tocado tú—. Siguen abiertas y siguen contando; las dejo aquí con su "
                      "contexto para que puedas recolocarlas o darlas por cerradas.\n")
        for e in huerfanas:
            salida.append(render_nota(e, huerfana=True))
        salida.append("\n---\n")

    for md, ancla in cuerpo:
        if ancla:
            salida.append(ancla)
        salida.append(md)

    os.makedirs(REV, exist_ok=True)
    texto = "\n\n".join(salida).rstrip() + "\n"
    io.open(MD, "w", encoding="utf-8").write(texto)
    io.open(BASE, "w", encoding="utf-8").write(texto)
    odt = generar_odt()
    escribir_bitacora_md(b)
    print("✓ revision/LIBRO.md%s generado: %d bloques, %d nota(s) abierta(s) "
          "recolocada(s), %d huérfana(s)"
          % (" y LIBRO.odt" if odt else "",
             sum(1 for _, a in cuerpo if a), len(colocadas), len(huerfanas)))
    return 0


def generar_odt():
    """Deja el .odt al día a partir del .md, para poder revisar en Writer.

    Se regenera SIEMPRE que se genera el .md: si se quedara viejo, `recoger`
    lo tomaría por bueno —es el más reciente— y se perderían los retoques.
    """
    import subprocess
    destino = os.path.join(REV, "LIBRO.odt")
    try:
        r = subprocess.run(["pandoc", "-f", "markdown", "-t", "odt",
                            "-o", destino, MD], capture_output=True, timeout=300)
        if r.returncode != 0:
            return False
        os.utime(destino, None)
        return True
    except Exception:
        return False


def render_nota(e, huerfana=False):
    L = []
    if huerfana:
        L.append("**%s** · %s · *(el contexto era:* %s *)*"
                 % (e["id"], e.get("capitulo", ""), e.get("extracto", "")[:120]))
    else:
        L.append("**%s** · %s" % (e["id"], e["fecha"]))
    for l in e["nota"].split("\n"):
        L.append(">> " + l)
    for r in e.get("respuestas", []):
        for l in r["texto"].split("\n"):
            L.append(">> %s: %s" % (r["autor"].upper(), l))
    return "\n".join(L)


def normaliza(md):
    return re.sub(r"\s+", " ", re.sub(r"[^\w\s]", "", md)).strip().lower()[:120]


def paginas():
    log = os.path.join(LIBRO, "libro.log")
    if os.path.isfile(log):
        m = re.findall(r"libro\.xdv \((\d+) pages", io.open(log, encoding="utf-8",
                                                            errors="replace").read())
        if m:
            return int(m[-1])
    return 0


def n_fragmentos():
    p = os.path.join(LIBRO, "fragmentos.json")
    return len(json.load(io.open(p, encoding="utf-8"))["fragmentos"]) if os.path.isfile(p) else 0


# ---------------------------------------------------------------------------
# recoger
# ---------------------------------------------------------------------------

def texto_odt(ruta):
    """Los párrafos de un .odt. Con pandoc si está; si no, leyendo el XML."""
    import subprocess, zipfile
    from xml.etree import ElementTree as ET
    try:
        r = subprocess.run(["pandoc", "-f", "odt", "-t", "markdown-raw_html",
                            "--wrap=none", ruta],
                           capture_output=True, text=True, timeout=120)
        if r.returncode == 0 and r.stdout.strip():
            return [l for l in r.stdout.split("\n")]
    except Exception:
        pass
    T = "{urn:oasis:names:tc:opendocument:xmlns:text:1.0}"
    raiz = ET.fromstring(zipfile.ZipFile(ruta).read("content.xml"))
    cuerpo = raiz.find("{urn:oasis:names:tc:opendocument:xmlns:office:1.0}body")
    parr = []
    for el in cuerpo.iter():
        if el.tag not in (T + "p", T + "h"):
            continue
        trozos = []
        for nodo in el.iter():
            if nodo.tag == T + "s":
                trozos.append(" " * int(nodo.get(T + "c", 1)))
            if nodo.tag == T + "tab":
                trozos.append("\t")
            if nodo.text:
                trozos.append(nodo.text)
            if nodo.tail:
                trozos.append(nodo.tail)
        parr.append("".join(trozos))
    return parr


def fuente_de_revision():
    """De dónde se lee: del .md, o del .odt si es más reciente.

    Se admite el .odt porque es como se revisa de verdad —se abre el Markdown
    con un procesador de textos y se guarda—. Lo que se pierde por el camino
    (el marcado inline, las anclas) se recupera contra `.base.md`.
    """
    odt = os.path.join(REV, "LIBRO.odt")
    if os.path.isfile(odt) and (not os.path.isfile(MD)
                                or os.path.getmtime(odt) > os.path.getmtime(MD)):
        return "odt", "\n".join(texto_odt(odt)).replace("\xa0", " ")
    return "md", io.open(MD, encoding="utf-8").read()


def bloques_base():
    """`.base.md` partido en (ancla, texto). Es el mapa para recolocar notas."""
    fuera, ancla = [], None
    for trozo in io.open(BASE, encoding="utf-8").read().split("\n\n"):
        m = RE_ANCLA.match(trozo.strip())
        if m:
            ancla = "%s:%s" % (m.group(1), m.group(2))
            continue
        if trozo.strip():
            fuera.append((ancla, trozo.strip()))
    return fuera


def ancla_por_contexto(contexto, mapa):
    """El ancla del bloque de `.base.md` que más se parece al contexto dado."""
    if not contexto:
        return None, None
    import difflib as _d
    objetivo = normaliza(contexto)
    mejor, mejor_r = (None, None), 0.0
    for ancla, texto in mapa:
        r = _d.SequenceMatcher(None, objetivo, normaliza(texto)).ratio()
        if r > mejor_r:
            mejor, mejor_r = (ancla, texto), r
    return mejor if mejor_r >= 0.6 else (None, None)


def quitar_notas(texto):
    """El texto sin las líneas `>>`: es lo que se compara para ver retoques.

    Las líneas en blanco consecutivas se colapsan: al quitar una nota queda su
    hueco, y sin esto cada nota ensuciaba el diff con un cambio que no hiciste.
    """
    fuera = [l for l in texto.split("\n") if not es_marca(l)]
    salida = []
    for l in fuera:
        if not l.strip() and salida and not salida[-1].strip():
            continue
        salida.append(l)
    return "\n".join(salida)


def notas_con_ancla(texto):
    """Cada bloque `>>` con el ancla y el bloque de texto que lo precede."""
    lineas = texto.split("\n")
    fuera, i = [], 0
    ancla = None
    bloque, anterior = [], []
    while i < len(lineas):
        l = lineas[i]
        m = RE_ANCLA.match(l.strip())
        if m:
            ancla = "%s:%s" % (m.group(1), m.group(2))
            bloque = []
            i += 1
            continue
        if es_marca(l):
            nota = []
            while i < len(lineas) and es_marca(lineas[i]):
                nota.append(lineas[i])
                i += 1
            ctx = bloque if bloque else anterior
            fuera.append((ancla, "\n".join(ctx).strip(), limpia_nota(nota)))
            continue
        if l.strip():
            bloque.append(l)
        else:
            # línea en blanco = fin de párrafo. El contexto de una nota es el
            # párrafo que la precede, no todo el documento hasta ella: sin esto,
            # sobre un .odt (que no trae anclas) el extracto salía siendo la
            # portada, y ninguna nota se podía recolocar.
            if bloque:
                anterior, bloque = bloque, []
        i += 1
    return fuera


def diff_por_parrafos(base, actual):
    """Compara por párrafos normalizados. Devuelve sólo los cambios REALES.

    Un cambio real es un párrafo que existe en los dos lados y cuyas palabras
    difieren; los que sólo cambian de forma —marcado perdido, párrafo partido—
    se descartan, porque no los has escrito tú: los ha hecho el conversor.
    """
    # La portada la escribo yo en cada generación y el conversor la reescapa:
    # compararla sólo produce ruido.
    portada = {normaliza(x) for x in re.split(r"\n\s*\n", CABECERA) if x.strip()}

    def trocear(t):
        out = []
        t = re.sub(r"\n>\s*\n", "\n\n", t)   # los recuadros, por su línea vacía
        for trozo in re.split(r"\n\s*\n", t):
            z = re.sub(r"\s*\n\s*", " ", trozo.strip())
            z = re.sub(r"^\s*[-*]\s+", "", z)
            if len(normaliza(z)) <= 40 or z.startswith("```") or z.startswith("<!--"):
                continue
            # Las tablas no se comparan: el conversor las reescribe enteras en
            # su propio formato de rejilla y saldrían todas como cambiadas.
            if z.lstrip().startswith("|") or re.search(r"-{6,}", z):
                continue
            if any(normaliza(z) in h or h in normaliza(z) for h in portada if h):
                continue
            out.append(z)
        return out
    pb, pa = trocear(base), trocear(actual)
    nb, na = [normaliza(x) for x in pb], [normaliza(x) for x in pa]
    sm = difflib.SequenceMatcher(None, nb, na, autojunk=False)
    fuera = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag != "replace":
            continue
        for x in range(i1, i2):
            mejor, r_mejor = None, 0.0
            for y in range(j1, j2):
                r = difflib.SequenceMatcher(None, nb[x], na[y]).ratio()
                if r > r_mejor:
                    mejor, r_mejor = y, r
            if mejor is None or r_mejor < 0.55 or r_mejor > 0.995:
                continue
            fuera.append("--- generado")
            fuera.append("-" + pb[x])
            fuera.append("+++ tuyo")
            fuera.append("+" + pa[mejor])
            fuera.append("")
    return fuera


def recoger():
    if not os.path.isfile(MD):
        print("✗ no hay revision/LIBRO.md — ejecuta primero `make revision`", file=sys.stderr)
        return 2
    if not os.path.isfile(BASE):
        print("✗ no hay revision/.base.md — no puedo saber qué has cambiado", file=sys.stderr)
        return 2
    b = cargar()
    origen, actual = fuente_de_revision()
    base = io.open(BASE, encoding="utf-8").read()
    if origen == "odt":
        print("· leyendo revision/LIBRO.odt (es más reciente que el .md)")
    mapa = bloques_base()

    ya = {(e.get("ancla"), e["nota"]) for e in b["entradas"] if e.get("tipo") != "edicion"}
    mias = set()
    for e in b["entradas"]:
        for r in e.get("respuestas", []):
            mias.add(r["texto"])

    nuevas = 0
    for ancla, extracto, nota in notas_con_ancla(actual):
        # mis propias respuestas vuelven en el fichero: no son notas nuevas
        if re.match(r"^(CLAUDE|JULI[ÁA]N):", nota) or nota in mias:
            continue
        nota = "\n".join(l for l in nota.split("\n")
                         if not re.match(r"^(CLAUDE|JULI[ÁA]N):", l)).strip()
        if not nota:
            continue
        # Un .odt pierde las anclas (son comentarios HTML): se recuperan
        # buscando en `.base.md` el bloque que más se parece al contexto.
        if ancla is None and extracto:
            ancla, mejor = ancla_por_contexto(extracto, mapa)
            if mejor:
                extracto = mejor
        if (ancla, nota) in ya:
            continue
        b["entradas"].append({
            "id": "N-%04d" % b["siguiente"], "fecha": HOY,
            "capitulo": (ancla or "?").split(":")[0], "ancla": ancla,
            "extracto": extracto[:400], "clave_extracto": normaliza(extracto),
            "nota": nota, "estado": "abierta", "respuestas": []})
        b["siguiente"] += 1
        nuevas += 1

    # --- retoques de prosa --------------------------------------------------
    # Desde un .odt no vale un diff de líneas: el procesador de textos ha
    # perdido el marcado inline y ha vuelto a partir los párrafos, así que
    # TODO saldría cambiado. Se comparan párrafos NORMALIZADOS y sólo se
    # recoge lo que de verdad cambia de palabras.
    edicion = 0
    if origen == "odt":
        d = diff_por_parrafos(quitar_notas(base), quitar_notas(actual))
    else:
        d = list(difflib.unified_diff(quitar_notas(base).split("\n"),
                                      quitar_notas(actual).split("\n"),
                                      "generado", "tuyo", lineterm="", n=2))
    if d:
        diff = "\n".join(d)
        toca_lean = any(l.startswith(("+", "-")) and "```lean" in l for l in d)
        b["entradas"].append({
            "id": "E-%04d" % b["siguiente"], "fecha": HOY, "tipo": "edicion",
            "resumen": "%d línea(s) tocada(s)%s"
                       % (sum(1 for l in d if l[:1] in "+-" and l[:3] not in ("+++", "---")),
                          " — ⚠️ el diff toca un bloque de código" if toca_lean else ""),
            "diff": diff, "estado": "abierta", "respuestas": []})
        b["siguiente"] += 1
        edicion = 1

    guardar(b)
    print("✓ recogido: %d nota(s) nueva(s), %d bloque(s) de retoques de prosa."
          % (nuevas, edicion))
    if nuevas or edicion:
        print("  Todo está en revision/BITACORA.md. Abiertas: %d."
              % sum(1 for e in b["entradas"] if e.get("estado") == "abierta"))
    return 0


# ---------------------------------------------------------------------------
# responder / estado
# ---------------------------------------------------------------------------

def responder(argv):
    if len(argv) < 2:
        print("uso: revisar.py responder <ID> \"texto\" [--estado aplicada]", file=sys.stderr)
        return 2
    ident, texto = argv[0], argv[1]
    estado = None
    if "--estado" in argv:
        estado = argv[argv.index("--estado") + 1]
    b = cargar()
    for e in b["entradas"]:
        if e["id"] == ident:
            e.setdefault("respuestas", []).append(
                {"fecha": HOY, "autor": "claude", "texto": texto})
            if estado:
                e["estado"] = estado
            guardar(b)
            print("✓ %s: respuesta añadida%s" % (ident, ", estado → " + estado if estado else ""))
            return 0
    print("✗ no existe la entrada %s" % ident, file=sys.stderr)
    return 2


def estado():
    b = cargar()
    ab = [e for e in b["entradas"] if e.get("estado") == "abierta"]
    if not ab:
        print("✓ nada abierto (%d entrada(s) en total)" % len(b["entradas"]))
        return 0
    print("· %d entrada(s) abierta(s):" % len(ab))
    for e in ab:
        if e.get("tipo") == "edicion":
            print("    %s  [retoque de prosa] %s" % (e["id"], e.get("resumen", "")))
        else:
            print("    %s  %-22s %s" % (e["id"], e.get("capitulo", ""),
                                        e["nota"].replace("\n", " ")[:60]))
    return 0


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "generar"
    if cmd == "generar":
        return generar()
    if cmd == "recoger":
        return recoger()
    if cmd == "responder":
        return responder(sys.argv[2:])
    if cmd == "estado":
        return estado()
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
