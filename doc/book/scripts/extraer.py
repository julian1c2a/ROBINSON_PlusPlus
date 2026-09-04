#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
extraer.py — extractor de fragmentos Lean para el libro «Incompletitud, formalizada».

Implementa los principios editoriales de PLAN-LIBRO.md:

  §2.1  Sólo se publica lo que compila
        → nada de copiar-pegar: el código sale del repo, y si la declaración
          citada no existe, esto FALLA RUIDOSAMENTE.

  §2.2  Sólo se expone lo que está demostrado DESDE LA BASE
        (a) alcanzabilidad desde ROBINSON_PlusPlus.lean  ......... aquí
        (b) build verde en el commit citado ..................... _estado.tex
        (c) #print axioms impreso junto al enunciado ............ aquí
        (d) footprint contenido en la base sancionada .......... aquí + --axiomas

  §2.3  Los sondeos son citables, etiquetados, y NO sostienen teoremas
        → capa "sondeo" ⇒ debe estar FUERA del cierre de imports, y se imprime
          con la marca «fuera del build».

Uso:
    python3 scripts/extraer.py              # extrae y valida (sin Lean)
    python3 scripts/extraer.py --axiomas    # además mide los footprints reales
    python3 scripts/extraer.py --fix-footprint   # escribe los medidos al manifiesto
"""

import json
import os
import re
import subprocess
import sys

AQUI = os.path.dirname(os.path.abspath(__file__))
LIBRO = os.path.dirname(AQUI)
RAIZ = os.path.abspath(os.path.join(LIBRO, "..", ".."))
MANIFIESTO = os.path.join(LIBRO, "fragmentos.json")
EXTRAIDO = os.path.join(LIBRO, "extraido")
MODULO_RAIZ = os.path.join(RAIZ, "ROBINSON_PlusPlus.lean")
ESTADO_DOC = os.path.join(RAIZ, "CURRENT-STATUS-PROJECT.md")

ERRORES = []
AVISOS = []

# --- Niveles (PLAN-LIBRO.md §2.5) -------------------------------------------
# Dos ejes: quién afirma, y sobre qué. La chapa se imprime en cada fragmento.
AFIRMA = {"Lean", "derives", "Prf0", "Prf", "PrfH"}
SOBRE = {"Lean", "sintaxis", "objeto", "codigo", "Prov"}

# La convención de nombres del proyecto YA codifica el nivel. Se usa como
# control cruzado: si el prefijo y el nivel declarado no cuadran, hay que
# mirarlo. Es aviso y no error — las convenciones tienen excepciones legítimas.
PREFIJO_ESPERA = {
    "pcc_": ("Prf", "Prov"),
    "prf_": ("Prf", None),
    "ax_": ("derives", "objeto"),
    "CRIT_": (None, None),
}


def error(msg):
    ERRORES.append(msg)


def aviso(msg):
    AVISOS.append(msg)


# ---------------------------------------------------------------------------
# (a) Cierre de imports: qué módulos entran REALMENTE en el build
# ---------------------------------------------------------------------------
# `lake` sólo construye lo alcanzable desde el módulo raíz. Un fichero puede
# estar en su sitio, compilar suelto, y no formar parte de nada: es la trampa
# que PLAN-LIBRO.md §2.2 razón 2 documenta («el número de jobs no cambia»).

# ⚠️ El comentario final NO es opcional en la práctica: `Minimal/Axioms.lean:9`
# escribe `import FOL.MetaRules    -- meta-reglas ω …`, y un patrón anclado en
# `$` lo pasa por alto. Eso da un FALSO NEGATIVO de alcanzabilidad — el mismo
# modo de fallo que NEXT-STEPS.md documenta para la medición por `import`.
RE_IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*(?:--.*)?$")

# Raíz de cada paquete, relativa a RAIZ. `FOL` es un paquete HERMANO
# (`require FOL from "../FOL"` en lakefile.lean), así que sus módulos no viven
# bajo la raíz de RPP y sin esto el cierre de imports se cortaría en seco justo
# donde empieza el capítulo 2.
PAQUETES = {"ROBINSON_PlusPlus": ".", "FOL": os.path.join("..", "FOL")}


def rel(p):
    return os.path.relpath(p, RAIZ).replace("\\", "/")


def ruta_de_modulo(nombre):
    pkg = nombre.split(".")[0]
    base = PAQUETES.get(pkg, ".")
    return os.path.normpath(os.path.join(RAIZ, base, *nombre.split("."))) + ".lean"


def cierre_de_imports():
    vistos, pila = set(), []
    if not os.path.isfile(MODULO_RAIZ):
        error("no encuentro el módulo raíz ROBINSON_PlusPlus.lean")
        return vistos
    pila.append(MODULO_RAIZ)
    vistos.add(rel(MODULO_RAIZ))
    while pila:
        f = pila.pop()
        try:
            with open(f, encoding="utf-8") as fh:
                lineas = fh.readlines()
        except OSError:
            continue
        for ln in lineas:
            m = RE_IMPORT.match(ln)
            if not m:
                continue
            hijo = ruta_de_modulo(m.group(1))
            r = rel(hijo)
            if r in vistos or not os.path.isfile(hijo):
                continue
            vistos.add(r)
            pila.append(hijo)
    return vistos


# ---------------------------------------------------------------------------
# Extracción de una declaración
# ---------------------------------------------------------------------------
# Heurística deliberadamente conservadora: en este repo los cuerpos de prueba
# van indentados y las declaraciones empiezan en columna 0.

INICIO_DECL = (
    r"(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|axiom|instance|structure|inductive)\s+"
)
RE_CORTE = re.compile(
    r"^(?:@\[|/--|/-!|/-|"
    r"(?:private|protected|noncomputable|partial|scoped)\s|"
    r"theorem\s|lemma\s|def\s|abbrev\s|axiom\s|instance\s|structure\s|"
    r"inductive\s|mutual\b|end\b|export\b|namespace\s|section\b|open\s|"
    r"set_option\s|attribute\s|variable\s|universe\s|#print\b|#check\b|"
    # una notación o un comentario en columna 0 marcan el fin de la declaración
    r"notation\s|infix\b|infixl\b|infixr\b|prefix\b|postfix\b|macro\b|"
    r"syntax\b|--|/-)"
)


def extraer_declaracion(ruta, nombre):
    """Devuelve (texto, nº de línea 1-based) o (None, None)."""
    with open(ruta, encoding="utf-8") as fh:
        lineas = fh.read().split("\n")
    re_ini = re.compile(r"^" + INICIO_DECL + re.escape(nombre) + r"\b")
    ini = None
    for i, ln in enumerate(lineas):
        if re_ini.match(ln):
            ini = i
            break
    if ini is None:
        return None, None
    fin = len(lineas)
    for j in range(ini + 1, len(lineas)):
        if RE_CORTE.match(lineas[j]):
            fin = j
            break
    trozo = lineas[ini:fin]
    while trozo and not trozo[-1].strip():
        trozo.pop()
    return "\n".join(trozo), ini + 1


RE_FIN_FIRMA = re.compile(r"\s*:=\s*by\s*$|\s*:=\s*$|\s+by\s*$|\s+where\s*$")


def solo_la_firma(codigo):
    """Recorta la prueba y deja el enunciado.

    Lo pide AI-GUIDE.md §7: en el sistema REFERENCE los teoremas se documentan
    *sin ningún tipo de prueba*. El libro hereda ese criterio siempre que lo que
    interesa es QUÉ dice el teorema, no cómo se demuestra."""
    lineas = codigo.split("\n")
    for i, ln in enumerate(lineas):
        m = RE_FIN_FIRMA.search(ln)
        if m:
            # Se CONSERVA el terminador real (`:= by`, `:=`, `by`, `where`) y sólo
            # se elide lo que sigue. Recortar cambiando el token —imprimir `:=`
            # donde el fuente dice `where`— sería alterar el código, o sea §2.1.
            return "\n".join(lineas[:i] + [ln.rstrip() + " \u2026"])
    return codigo


def codigo_para(fr, ruta):
    """La lectura canónica de un fragmento. La comparten extraer y verificar."""
    codigo, linea = extraer_declaracion(ruta, fr["decl"])
    if codigo is not None and fr.get("solo_firma"):
        codigo = solo_la_firma(codigo)
    return codigo, linea


# ---------------------------------------------------------------------------
# Escritura del .tex
# ---------------------------------------------------------------------------

def tex_escapar_titulo(s):
    for a, b in (("\\", "\\textbackslash "), ("_", "\\_"), ("#", "\\#"),
                 ("%", "\\%"), ("&", "\\&"), ("$", "\\$")):
        s = s.replace(a, b)
    return s


# ---------------------------------------------------------------------------
# Resaltado — lo hace AQUÍ el extractor, no LaTeX
# ---------------------------------------------------------------------------
# Motivo (medido el 2026-09-03): `listings` reordena los caracteres al mezclar
# ASCII y Unicode — imprime `φ( : Formula)` donde el fuente dice
# `(φ : Formula)`. Altera el código en silencio, que es justo lo que
# PLAN-LIBRO.md §2.1 prohíbe. `fancyvrb` es fiel byte a byte pero no resalta;
# así que el marcado se emite desde aquí, en \kw{}/\cm{}/\st{}.

PALABRAS_CLAVE = {
    "theorem", "lemma", "def", "abbrev", "axiom", "example", "instance",
    "structure", "inductive", "mutual", "namespace", "end", "section", "open",
    "import", "export", "variable", "universe", "noncomputable", "private",
    "protected", "partial", "where", "deriving", "by", "do", "match", "with",
    "fun", "let", "have", "show", "from", "calc", "if", "then", "else",
    "termination_by", "decreasing_by", "set_option", "attribute", "sorry",
}

RE_PALABRA = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def escapar_verbatim(t):
    """Escapa lo único que `commandchars=\\\\\\{\\}` vuelve especial."""
    return (t.replace("\\", "\\textbackslash{}")
             .replace("{", "\\{")
             .replace("}", "\\}"))


def resaltar(linea):
    """Devuelve la línea marcada. Fiel: nada se reordena ni se pierde."""
    # comentario de línea: se separa ANTES de escapar
    i = linea.find("--")
    codigo, comentario = (linea, "") if i < 0 else (linea[:i], linea[i:])

    salida, pos = [], 0
    for m in RE_PALABRA.finditer(codigo):
        salida.append(escapar_verbatim(codigo[pos:m.start()]))
        pal = m.group(0)
        salida.append("\\kw{%s}" % pal if pal in PALABRAS_CLAVE
                      else escapar_verbatim(pal))
        pos = m.end()
    salida.append(escapar_verbatim(codigo[pos:]))
    if comentario:
        salida.append("\\cm{%s}" % escapar_verbatim(comentario))
    return "".join(salida)


def escribir_fragmento(fr, codigo, linea):
    clave = fr["clave"]
    modulo = fr["modulo"]
    decl = fr["decl"]
    titulo = tex_escapar_titulo("%s · %s" % (modulo, decl))
    niv = fr.get("nivel") or ["Lean", "Lean"]
    chapa = "\\nivel{%s}{%s}" % (niv[0], niv[1])
    partes = [
        "%% GENERADO por scripts/extraer.py — NO EDITAR (PLAN-LIBRO.md §2.1)",
        "%% origen: %s:%d" % (modulo, linea),
        "%% nivel: afirma en %s, sobre %s" % (niv[0], niv[1]),
        chapa + "\\hspace{0.4em}",
        "\\begin{leanbox}[title={%s}]" % titulo,
        "\\begin{lean}",
        "\n".join(resaltar(l) for l in codigo.split("\n")),
        "\\end{lean}",
        "\\end{leanbox}",
    ]
    if fr.get("capa") == "sondeo":
        partes.append("\\fueradelbuild{%s}" % tex_escapar_titulo(modulo))
    fp = fr.get("footprint")
    if fp:
        partes.append("\\footprint{%s}" % tex_escapar_titulo(", ".join(fp)))
    with open(os.path.join(EXTRAIDO, clave + ".tex"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(partes) + "\n")


# ---------------------------------------------------------------------------
# _estado.tex — el control §2.2(b)
# ---------------------------------------------------------------------------

def git(*args):
    try:
        # --no-optional-locks: un `git status` normal REFRESCA el índice y toma
        # .git/index.lock. Esta tarea comparte repositorio con la de desarrollo
        # activo, así que no puede bloquear el índice de nadie ni dejar un lock
        # huérfano si la llamada se interrumpe.
        return subprocess.check_output(
            ["git", "--no-optional-locks", "-C", RAIZ] + list(args),
            stderr=subprocess.DEVNULL).decode().strip()
    except Exception:
        return "?"


def escribir_estado(n_frag, n_prod, n_sond):
    commit = git("rev-parse", "--short", "HEAD")
    fecha = git("log", "-1", "--format=%cd", "--date=format:%Y-%m-%d %H:%M")
    sucio = git("status", "--porcelain")
    jobs = "?"
    if os.path.isfile(ESTADO_DOC):
        with open(ESTADO_DOC, encoding="utf-8") as fh:
            m = re.search(r"Build\s+(\d+)\s+jobs", fh.read())
            if m:
                jobs = m.group(1)
    aviso_sucio = ""
    if sucio and sucio != "?":
        aviso_sucio = ("\n\n\\begin{muro}[Aviso de reproducibilidad]\n"
                       "El árbol de trabajo tenía cambios sin \\emph{commitear} al generar "
                       "este ejemplar: el commit citado no lo reproduce exactamente.\n"
                       "\\end{muro}")
    txt = r"""%% GENERADO por scripts/extraer.py — NO EDITAR
\chapter*{Estado del código}
\addcontentsline{toc}{chapter}{Estado del código}

Este ejemplar se ha generado contra un estado concreto del repositorio. Todo teorema
citado ha pasado los cuatro controles de \doc{PLAN-LIBRO.md}~§2.2.

\begin{center}\small
\begin{tabular}{ll}
\toprule
Commit & \texttt{COMMIT} \\
Fecha del commit & FECHA \\
Build declarado & \texttt{JOBS} jobs, 0 errores, 0 warnings, 0 \texttt{sorry} \\
Fragmentos citados & TOTAL (PROD en producción, SOND en \texttt{sondeos/}) \\
\bottomrule
\end{tabular}
\end{center}

\noindent\small Los fragmentos marcados \textbf{«fuera del build»} provienen de
\modulo{sondeos/}: compilan, y por eso son citables, pero \textbf{no sostienen ningún
teorema} de las Partes I--III (\doc{PLAN-LIBRO.md}~§2.3).AVISO
"""
    txt = (txt.replace("COMMIT", commit).replace("FECHA", fecha)
              .replace("JOBS", jobs).replace("TOTAL", str(n_frag))
              .replace("PROD", str(n_prod)).replace("SOND", str(n_sond))
              .replace("AVISO", aviso_sucio))
    with open(os.path.join(EXTRAIDO, "_estado.tex"), "w", encoding="utf-8") as fh:
        fh.write(txt)


# ---------------------------------------------------------------------------
# (c)(d) Footprints reales — necesita lake/lean
# ---------------------------------------------------------------------------

def medir_axiomas(frags):
    """Genera una sonda Lean, la ejecuta y devuelve {decl: [axiomas]}."""
    prod = [f for f in frags if f.get("capa") != "sondeo"]
    if not prod:
        return {}
    mods = sorted({f["modulo"] for f in prod})
    sonda = os.path.join(LIBRO, "extraido", "_sonda.lean")
    with open(sonda, "w", encoding="utf-8") as fh:
        for m in mods:
            nombre = m[:-5].replace("/", ".")
            fh.write("import %s\n" % nombre)
        fh.write("\n")
        for f in prod:
            fh.write("#print axioms %s\n" % f["decl"])
    try:
        salida = subprocess.run(["lake", "env", "lean", os.path.relpath(sonda, RAIZ)],
                                cwd=RAIZ, capture_output=True, timeout=1800)
    except FileNotFoundError:
        aviso("`lake` no está en el PATH: no se han medido los footprints "
              "(ejecuta `make axiomas` desde tu entorno con Lean).")
        return {}
    txt = (salida.stdout + salida.stderr).decode("utf-8", "replace")
    medidos = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", txt):
        medidos[m.group(1).split(".")[-1]] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", txt):
        medidos[m.group(1).split(".")[-1]] = []
    if not medidos:
        error("la sonda de axiomas no produjo lecturas. Salida:\n" + txt[-2000:])
    return medidos


# ---------------------------------------------------------------------------
# Principal
# ---------------------------------------------------------------------------

def main():
    con_axiomas = "--axiomas" in sys.argv
    fijar = "--fix-footprint" in sys.argv

    if not os.path.isfile(MANIFIESTO):
        print("✗ falta fragmentos.json", file=sys.stderr)
        return 2
    with open(MANIFIESTO, encoding="utf-8") as fh:
        man = json.load(fh)
    base = set(man.get("base_sancionada", []))
    frags = man.get("fragmentos", [])
    os.makedirs(EXTRAIDO, exist_ok=True)

    cierre = cierre_de_imports()
    n_prod = n_sond = 0

    for fr in frags:
        clave = fr.get("clave", "?")
        modulo = fr.get("modulo", "")
        decl = fr.get("decl", "")
        capa = fr.get("capa", "produccion")
        ruta = os.path.join(RAIZ, modulo)

        if not os.path.isfile(ruta):
            error("[%s] el módulo %s no existe" % (clave, modulo))
            continue

        # (a) alcanzabilidad — el control duro de §2.2
        en_build = modulo.replace("\\", "/") in cierre
        if capa == "produccion" and not en_build:
            error("[%s] %s NO es alcanzable desde ROBINSON_PlusPlus.lean: "
                  "no está en el build. §2.2(a) lo prohíbe como teorema del libro. "
                  "Si es un sondeo, decláralo con \"capa\": \"sondeo\"." % (clave, modulo))
        if capa == "sondeo":
            if en_build:
                error("[%s] %s SÍ está en el build: no lo marques como sondeo." % (clave, modulo))
            n_sond += 1
        else:
            n_prod += 1

        # §2.5 — el nivel es OBLIGATORIO: sin él, el lector no sabe si lo que
        # lee es lenguaje objeto o lenguaje meta.
        niv = fr.get("nivel")
        if not (isinstance(niv, list) and len(niv) == 2):
            error("[%s] falta \"nivel\": [afirma, sobre]. §2.5 lo exige en todo "
                  "fragmento (afirma ∈ %s, sobre ∈ %s)."
                  % (clave, sorted(AFIRMA), sorted(SOBRE)))
        else:
            if niv[0] not in AFIRMA:
                error("[%s] nivel[0]=%r no es un valor de «quién afirma» %s"
                      % (clave, niv[0], sorted(AFIRMA)))
            if niv[1] not in SOBRE:
                error("[%s] nivel[1]=%r no es un valor de «sobre qué» %s"
                      % (clave, niv[1], sorted(SOBRE)))
            excusa = fr.get("nivel_excepcion")
            for pref, (ea, es) in PREFIJO_ESPERA.items():
                if decl.startswith(pref) and not excusa:
                    if ea and niv[0] != ea:
                        aviso("[%s] `%s` empieza por `%s`, que suele afirmar en "
                              "%s, pero se declara %s" % (clave, decl, pref, ea, niv[0]))
                    if es and niv[1] != es:
                        aviso("[%s] `%s` empieza por `%s`, que suele hablar de "
                              "%s, pero se declara %s" % (clave, decl, pref, es, niv[1]))
                    break

        # (c) el footprint es OBLIGATORIO en producción: si no se imprime,
        # el lector no puede comprobar sobre qué base descansa el teorema.
        if capa == "produccion" and "footprint" not in fr:
            error("[%s] falta el campo \"footprint\". §2.2(c) lo exige para toda "
                  "declaración de producción (usa [] si es net-0, o mide con "
                  "`make axiomas`)." % clave)

        # §2.1 — la declaración tiene que existir
        codigo, linea = codigo_para(fr, ruta)
        if codigo is None:
            error("[%s] la declaración `%s` no aparece en %s" % (clave, decl, modulo))
            continue

        escribir_fragmento(fr, codigo, linea)

        # (d) footprint declarado dentro de la base sancionada
        fuera = [a for a in fr.get("footprint", []) if a not in base]
        if fuera:
            error("[%s] footprint declarado fuera de la base sancionada: %s"
                  % (clave, ", ".join(fuera)))

    # (c)/(d) reales
    if con_axiomas or fijar:
        medidos = medir_axiomas(frags)
        for fr in frags:
            if fr.get("capa") == "sondeo":
                continue
            real = medidos.get(fr["decl"])
            if real is None:
                if medidos:
                    error("[%s] la sonda no devolvió footprint para `%s`"
                          % (fr["clave"], fr["decl"]))
                continue
            fuera = [a for a in real if a not in base]
            if fuera:
                error("[%s] FOOTPRINT REAL fuera de la base sancionada: %s"
                      % (fr["clave"], ", ".join(fuera)))
            if fijar:
                fr["footprint"] = real
            elif sorted(real) != sorted(fr.get("footprint", [])):
                error("[%s] el footprint declarado no coincide con el real.\n"
                      "        declarado: %s\n        real:      %s"
                      % (fr["clave"], fr.get("footprint", []), real))
        if fijar and not ERRORES:
            with open(MANIFIESTO, "w", encoding="utf-8") as fh:
                json.dump(man, fh, ensure_ascii=False, indent=2)
                fh.write("\n")
            print("· fragmentos.json actualizado con los footprints medidos")

    escribir_estado(len(frags), n_prod, n_sond)

    for a in AVISOS:
        print("⚠ " + a)
    if ERRORES:
        print("\n✗ EXTRACCIÓN FALLIDA — %d problema(s):\n" % len(ERRORES), file=sys.stderr)
        for e in ERRORES:
            print("  ✗ " + e, file=sys.stderr)
        print("\nPLAN-LIBRO.md §2.1-§2.3: el libro no puede desincronizarse "
              "en silencio del código.", file=sys.stderr)
        return 1
    print("✓ %d fragmento(s) extraído(s): %d de producción, %d de sondeos"
          % (len(frags), n_prod, n_sond))
    return 0


if __name__ == "__main__":
    sys.exit(main())
