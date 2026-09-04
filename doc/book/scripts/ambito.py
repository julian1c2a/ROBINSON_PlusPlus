#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ambito.py — guardián del ámbito de escritura de la tarea del LIBRO.

Q++ está en desarrollo activo. Esta tarea sólo puede escribir:

    PLAN-LIBRO.md        el plan del libro
    Sobre_el_libro.md    la nota histórica de intención
    doc/book/**          todo el libro

Cualquier otra cosa —los `.lean`, los `.md` de estado, los scripts de la raíz—
es de SÓLO LECTURA aquí, y pertenece a la tarea de programación y prueba. Así
las dos tareas no se pisan y cada commit tiene un único dueño.

Este script comprueba el ÁREA DE STAGING, que es lo que de verdad se sube. Los
ficheros modificados fuera del ámbito no son un error —son el trabajo en curso
del autor— pero se listan, para que nadie los arrastre por descuido.

    python3 scripts/ambito.py            # comprueba
    python3 scripts/ambito.py --añadir   # añade al staging SÓLO lo permitido
"""

import os
import subprocess
import sys

AQUI = os.path.dirname(os.path.abspath(__file__))
LIBRO = os.path.dirname(AQUI)
RAIZ = os.path.abspath(os.path.join(LIBRO, "..", ".."))

PERMITIDO_FICHEROS = {"PLAN-LIBRO.md", "Sobre_el_libro.md"}
PERMITIDO_ARBOL = ("doc/book/",)


def git(*a):
    # --no-optional-locks: leer el estado no debe tomar .git/index.lock (ver
    # el comentario homólogo en extraer.py).
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-C", RAIZ] + list(a)).decode("utf-8", "replace")


def en_ambito(ruta):
    return ruta in PERMITIDO_FICHEROS or ruta.startswith(PERMITIDO_ARBOL)


def puede_borrar():
    """¿Estamos en un montaje donde se pueden borrar ficheros?

    Medido el 2026-09-03: en el montaje de esta tarea, `rm` está prohibido. git
    CREA `.git/index.lock` en cada escritura del índice y luego NO PUEDE
    borrarlo, así que cada `git add`/`commit` deja un lock huérfano que bloquea
    el siguiente — incluidos los del propio autor desde su shell. Por eso el
    commit se hace desde SU shell, no desde aquí."""
    probe = os.path.join(RAIZ, "doc", "book", ".probe-borrado")
    try:
        with open(probe, "w") as fh:
            fh.write("x")
        os.remove(probe)
        return True
    except OSError:
        return False


def revisar_lock():
    """Un .git/index.lock huérfano bloquea cualquier `git add`/`commit`."""
    lock = os.path.join(RAIZ, ".git", "index.lock")
    if not os.path.exists(lock):
        return False
    import time
    edad = int(time.time() - os.path.getmtime(lock))
    print("\n⚠ Hay un .git/index.lock de hace %d min. Si no tienes ningún git abierto,\n"
          "  está huérfano y bloquea `git add` y `git commit`. Bórralo tú:\n"
          "      rm .git/index.lock          (o `del .git\\index.lock` en cmd)"
          % (edad // 60), file=sys.stderr)
    return True


def main():
    anadir = "--añadir" in sys.argv or "--anadir" in sys.argv
    hay_lock = revisar_lock()
    if anadir and hay_lock:
        print("✗ no se prepara nada mientras el índice esté bloqueado", file=sys.stderr)
        return 2
    if anadir and not puede_borrar():
        print("\n✗ Aquí no se puede borrar ficheros, y git necesita borrar\n"
              "  `.git/index.lock` al terminar cada escritura del índice. Si preparo o\n"
              "  commiteo desde aquí, el lock queda huérfano y BLOQUEA tu git también.\n\n"
              "  El commit del libro se hace desde TU shell:\n"
              "      cd doc/book && make subir MSG='...'\n\n"
              "  Desde aquí sí funcionan `make`, `make verificar` y `make ambito`,\n"
              "  que sólo leen (con --no-optional-locks).", file=sys.stderr)
        return 3
    if anadir:
        for r in sorted(PERMITIDO_FICHEROS):
            if os.path.exists(os.path.join(RAIZ, r)):
                subprocess.run(["git", "-C", RAIZ, "add", "--", r], check=True)
        subprocess.run(["git", "-C", RAIZ, "add", "--", "doc/book"], check=True)
        print("· añadido al staging sólo el ámbito del libro")

    intrusos, fuera_sin_preparar = [], []
    for ln in git("status", "--porcelain").splitlines():
        if not ln.strip():
            continue
        x, y, ruta = ln[0], ln[1], ln[3:].strip().strip('"')
        if " -> " in ruta:                      # renombrados
            ruta = ruta.split(" -> ")[-1]
        if en_ambito(ruta):
            continue
        if x != " " and x != "?":               # HAY algo preparado para subir
            intrusos.append(ruta)
        else:
            fuera_sin_preparar.append(ruta)

    if fuera_sin_preparar:
        print("· %d fichero(s) modificados FUERA del ámbito del libro, sin preparar "
              "(trabajo de la otra tarea; no se tocan):" % len(fuera_sin_preparar))
        for r in fuera_sin_preparar[:6]:
            print("    %s" % r)
        if len(fuera_sin_preparar) > 6:
            print("    … y %d más" % (len(fuera_sin_preparar) - 6))

    if intrusos:
        print("\n✗ ÁMBITO VIOLADO — hay %d fichero(s) PREPARADOS que no son del libro:"
              % len(intrusos), file=sys.stderr)
        for r in intrusos:
            print("    ✗ %s" % r, file=sys.stderr)
        print("\nEsta tarea sólo escribe PLAN-LIBRO.md, Sobre_el_libro.md y doc/book/**.\n"
              "Sácalos del staging con:  git restore --staged <fichero>", file=sys.stderr)
        return 1

    print("✓ ámbito correcto: sólo el libro está preparado para subir")
    return 0


if __name__ == "__main__":
    sys.exit(main())
