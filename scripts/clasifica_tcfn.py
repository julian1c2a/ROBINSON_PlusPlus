#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FASE 1 — Clasificador de los sitios de `tcFn`.

Extrae CADA aplicación `tcFn <arg>` (argumento con paréntesis balanceados),
y clasifica por el SÍMBOLO CABEZA del argumento.

Regla de clasificación (papel del argumento):
  NUM   -> el argumento denota un NÚMERO  ⟹ debe ir a `tcNum`
  CODE  -> el argumento denota un CÓDIGO  ⟹ debe ir a `tcCode`
  AMBIG -> el papel NO está determinado estáticamente ⟹ exige rediseño
"""
import os, re, sys, collections, json

ROOT = r"e:\Dropbox\GitHub\lean4\ROBINSON_PlusPlus\ROBINSON_PlusPlus"

# ---------------------------------------------------------------- extracción
def strip_comments(src):
    """Quita comentarios de bloque /- -/ y de línea --, preservando offsets."""
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth > 0:
                if src.startswith("/-", j): depth += 1; j += 2
                elif src.startswith("-/", j): depth -= 1; j += 2
                else: j += 1
            for k in range(i, min(j, n)):
                if out[k] != "\n": out[k] = " "
            i = j
        elif src.startswith("--", i):
            j = src.find("\n", i)
            if j == -1: j = n
            for k in range(i, j): out[k] = " "
            i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                if src[j] == "\\": j += 1
                j += 1
            i = j + 1
        else:
            i += 1
    return "".join(out)

def read_arg(src, pos):
    """Lee el argumento de una aplicación que empieza en `pos` (tras 'tcFn')."""
    n = len(src)
    while pos < n and src[pos] in " \t\n": pos += 1
    if pos >= n: return None, pos
    if src[pos] == "(":
        depth, j = 1, pos + 1
        while j < n and depth > 0:
            if src[j] == "(": depth += 1
            elif src[j] == ")": depth -= 1
            j += 1
        return src[pos + 1 : j - 1].strip(), j
    m = re.match(r"[^\s()\[\],;:]+", src[pos:])
    if not m: return None, pos
    return m.group(0), pos + m.end()

# ------------------------------------------------------------ clasificación
# Cabeza del argumento -> papel.  Basado en el TIPO SEMÁNTICO del resultado.
NUM = {
    # aritmética pura: el resultado es un número
    "zero", "succ", "add", "mul", "pred", "numeral", "numeralM", "sub",
    "div2", "mod2", "pow", "cantor_func", "cantor_poly", "pair",
    # funciones de código cuyo RESULTADO es un número (longitud, índice, contador)
    "lenc", "strCode", "strCodeM", "tagOf", "sizeOf",
}
CODE = {
    # constructores de código: el resultado es un cons-árbol
    "cons", "nil", "implc", "andc", "orc", "exc", "allc", "eqc", "atomc",
    "botc", "varc", "funcc", "formCode", "termCode", "termsCode",
    "provCodeC", "provCodeC'", "negc", "substfc", "liftfc", "substtc",
    "liftc", "substtsc", "liftsc", "concatc", "listc", "axiomsCodeT",
}
AMBIG = {
    # proyecciones de lista: el papel depende del CONTENIDO de la lista
    "carc", "cdrc", "nthc", "headc", "tailc", "runFn", "lastc",
}

def head_of(arg):
    if arg is None: return None
    a = arg.strip()
    while a.startswith("("):
        # ya venía sin el paréntesis exterior; esto captura ((f x) y)
        depth, j = 1, 1
        while j < len(a) and depth > 0:
            if a[j] == "(": depth += 1
            elif a[j] == ")": depth -= 1
            j += 1
        if j >= len(a): a = a[1:-1].strip()
        else: break
    m = re.match(r"[A-Za-z_ω⌜⌝σ][A-Za-z0-9_'!?ω.]*", a)
    if m: return m.group(0)
    if a.startswith("#") or a.startswith(".var"): return "#var"
    if re.match(r"^\d", a): return "<lit>"
    return "<expr:" + a[:12] + ">"

def role(head):
    if head is None: return "PARSE"
    base = head.split(".")[-1]
    if head in NUM or base in NUM: return "NUM"
    if head in CODE or base in CODE: return "CODE"
    if head in AMBIG or base in AMBIG: return "AMBIG"
    if head == "#var" or re.match(r"^(x|y|z|n|m|k|i|j|t|s|u|v|a|b|c|f|g|h|p|q|w|e|d)[0-9']*$", head):
        return "VAR"          # variable/hipótesis abstracta: hay que mirar el binder
    if head == "tcFn": return "TCFN"      # tcFn (tcFn ...) — anidado
    return "OTRO:" + head

# ------------------------------------------------------------------- barrido
rows = []
for dirpath, _, files in os.walk(ROOT):
    for fn in files:
        if not fn.endswith(".lean"): continue
        path = os.path.join(dirpath, fn)
        rel = os.path.relpath(path, ROOT).replace("\\", "/")
        src = strip_comments(open(path, encoding="utf-8").read())
        for m in re.finditer(r"(?<![A-Za-z0-9_'])tcFn(?![A-Za-z0-9_'])", src):
            arg, _ = read_arg(src, m.end())
            h = head_of(arg)
            line = src.count("\n", 0, m.start()) + 1
            rows.append((rel, line, h, role(h), (arg or "")[:60]))

# ------------------------------------------------------------------ informes
print(f"TOTAL de aplicaciones `tcFn <arg>`: {len(rows)}\n")

byrole = collections.Counter(r[3].split(":")[0] for r in rows)
print("=== POR PAPEL ===")
for k, v in byrole.most_common():
    print(f"  {k:8} {v:5}   {100*v/len(rows):5.1f}%")

print("\n=== POR CABEZA DEL ARGUMENTO (top 40) ===")
byhead = collections.Counter((r[2], r[3].split(':')[0]) for r in rows)
for (h, rl), v in byhead.most_common(40):
    print(f"  {v:5}  {rl:6}  {h}")

print("\n=== MÓDULOS con AMBIG / VAR / OTRO (los que exigen revisión) ===")
prob = [r for r in rows if r[3].split(":")[0] in ("AMBIG", "VAR", "OTRO", "TCFN", "PARSE")]
bymod = collections.Counter(r[0] for r in prob)
for mod, v in bymod.most_common():
    print(f"  {v:5}  {mod}")

print(f"\n=== TOTAL sitios que exigen revisión manual: {len(prob)} / {len(rows)} ===")

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "tcfn_sites.json"), "w", encoding="utf-8") as f:
    json.dump([{"file": r[0], "line": r[1], "head": r[2], "role": r[3], "arg": r[4]} for r in rows], f, ensure_ascii=False, indent=1)
print("\n(detalle en tcfn_sites.json)")
