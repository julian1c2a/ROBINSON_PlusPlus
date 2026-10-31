#!/usr/bin/env python3
"""scripts/prosa.py — ¿un cambio de un `.lean` es SÓLO PROSA (comentarios y docstrings)? (T14, ADR-234)

Un thaw «de sólo prosa» (los de FOL en ADR-116 y en D2) tocó comentarios y docstrings y ningún código. Esto lo
comprueba: compara el CÓDIGO de las dos versiones de un fichero, con los comentarios fuera y los literales DENTRO (un
cambio dentro de una cadena o de un carácter es código). Usa el lexer de referencia del proyecto
(`scripts/pruebas/leanlex.py`, el oráculo contra el que se valida `strip-lean.awk`), con una sola diferencia: allí cada
literal se sustituye por un espacio, y aquí se conserva. Del resultado se quitan las líneas que quedan vacías y los
espacios del final de cada línea: así un comentario que pasa de una línea a tres no cuenta como código. La sangría del
código sí cuenta (en Lean tiene significado).

Uso:
  prosa.py comparar <antes.lean> <después.lean>   sale con 0 si el código es el mismo y con 1 si no
  prosa.py git <repo> <commit> <fichero>           lo mismo, entre <commit>^ y <commit>
  prosa.py autotest                                los cuatro casos de abajo
Sale con 2 si no puede medir: un fichero que no está, o un error del lexer (un comentario o una cadena sin cerrar).
"""
import os
import subprocess
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "pruebas"))
from leanlex import Lex  # noqa: E402


class LexCodigo(Lex):
    """El lexer de referencia, con los literales conservados: sólo lo que empieza por `--` o `/-` (comentarios de
    línea y de bloque, docstrings `/--` y `/-!`) sale del texto."""

    def mark(self, a, b, k):
        if k == "D" and not (self.t.startswith("--", a) or self.t.startswith("/-", a)):
            k = "C"
        Lex.mark(self, a, b, k)


def codigo(texto):
    t = texto.replace("\r\n", "\n")
    lx = LexCodigo(t)
    s = lx.run()
    if lx.errors:
        raise ValueError("; ".join(lx.errors[:3]))
    return [l.rstrip() for l in s.split("\n") if l.strip()]


def comparar(a, b):
    ca, cb = codigo(a), codigo(b)
    if ca == cb:
        return 0, ""
    for i, (x, y) in enumerate(zip(ca, cb)):
        if x != y:
            return 1, f"línea de código {i + 1}: «{x.strip()[:80]}» → «{y.strip()[:80]}»"
    return 1, f"{len(ca)} líneas de código antes y {len(cb)} después"


def git_show(repo, rev, f):
    r = subprocess.run(["git", "-C", repo, "show", f"{rev}:{f}"], capture_output=True)
    if r.returncode != 0:
        raise FileNotFoundError(f"{rev}:{f}")
    return r.stdout.decode("utf-8")


A = 'theorem t : True := by\n  -- un comentario\n  trivial\n/-- doc -/\ndef x := "hola"\n'
CASOS = [
    ("sólo prosa", A, 'theorem t : True := by\n  -- otro comentario,\n  -- en dos líneas\n  trivial  -- y uno al final\n'
                      '/-- documentación nueva,\n    en dos líneas -/\ndef x := "hola"\n', 0),
    ("un literal", A, A.replace('"hola"', '"adiós"'), 1),
    ("código", A, A.replace("  trivial", "  exact trivial"), 1),
    ("sangría", A, A.replace("  trivial", "    trivial"), 1),
]


def autotest():
    mal = []
    for nombre, x, y, esperado in CASOS:
        rc, _ = comparar(x, y)
        if rc != esperado:
            mal.append(f"{nombre}: {rc}, esperado {esperado}")
    return mal


def main(a):
    try:
        if a[:1] == ["autotest"]:
            mal = autotest()
            if mal:
                print("❌ el autotest de prosa.py falla: " + "; ".join(mal))
                return 2
            print(f"✓ prosa.py: {len(CASOS)} de {len(CASOS)} casos")
            return 0
        if a[:1] == ["comparar"] and len(a) == 3:
            x = open(a[1], encoding="utf-8", newline="").read()
            y = open(a[2], encoding="utf-8", newline="").read()
        elif a[:1] == ["git"] and len(a) == 4:
            repo, c, f = a[1], a[2], a[3]
            x, y = git_show(repo, c + "^", f), git_show(repo, c, f)
        else:
            print(__doc__)
            return 2
        mal = autotest()
        if mal:
            print("❌ NO PUEDO MEDIR: el autotest de prosa.py falla: " + "; ".join(mal))
            return 2
        rc, donde = comparar(x, y)
        print("sólo prosa" if rc == 0 else f"CÓDIGO ({donde})")
        return rc
    except (OSError, ValueError, UnicodeDecodeError) as e:
        print(f"❌ NO PUEDO MEDIR: {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
