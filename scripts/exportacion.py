#!/usr/bin/env python3
"""scripts/exportacion.py — lee una exportación NDJSON de `leanexport` (T23, ADR-222).

`scripts/segundo-nucleo.bash` exporta el cierre de los titulares y lo pasa por núcleos que no son el de Lean. Esto
lee la exportación sin ningún núcleo: qué constantes lleva, cuáles son `axiom`, y si están los titulares. Y fabrica
el MUTANTE con el que se ve a cada núcleo rechazar algo.

Uso:
  exportacion.py resumen  <exportación> <titulares.txt> <axiomas esperados, separados por comas>
      Cuenta las constantes por clase, lista los `axiom` y rompe (exit 1) si falta un titular (como `thm`) o si los
      `axiom` no son EXACTAMENTE los esperados: la unión de los footprints de los titulares, que `#print axioms`
      mide por su lado (check-footprints.bash).
  exportacion.py mutante  <exportación> <salida>
      Copia la exportación con el VALOR del primer `thm` cambiado por su propio TIPO: la prueba deja de probar lo
      que dice, y todo núcleo que compruebe algo tiene que rechazarla. El primero, para que el rechazo llegue pronto.
      El índice del tipo ya está definido en esa línea (se escribe antes que el teorema).

El formato (`doc/dev/export_format.md` de Lean; LeanExport/Basic.lean del toolchain): una línea JSON por objeto; un
nombre es {"in": i, "str"|"num": {"pre": j, …}}, un nivel lleva "il", una expresión "ie", y una constante es un
objeto con una de las claves axiom, def, thm, opaque, quot o inductive (types, ctors y recs juntos).
Sale con 2 si no puede leer la exportación: un control que no mide no da verde.
"""
import json
import sys

CLASES = ("axiom", "def", "thm", "opaque", "quot")


def leer(ruta):
    nombres = {0: ""}
    constantes = []
    lineas = 0
    with open(ruta, encoding="utf-8") as h:
        for linea in h:
            lineas += 1
            o = json.loads(linea)
            if "in" in o:
                if "str" in o:
                    pre, s = o["str"]["pre"], o["str"]["str"]
                else:
                    pre, s = o["num"]["pre"], str(o["num"]["i"])
                base = nombres[pre]
                nombres[o["in"]] = base + "." + s if base else s
                continue
            if "il" in o or "ie" in o or "meta" in o:
                continue
            hallada = False
            for clase in CLASES:
                if clase in o:
                    constantes.append((clase, nombres[o[clase]["name"]]))
                    hallada = True
            if "inductive" in o:
                for clave, clase in (("types", "inductive"), ("ctors", "ctor"), ("recs", "rec")):
                    for t in o["inductive"][clave]:
                        constantes.append((clase, nombres[t["name"]]))
                hallada = True
            if not hallada:
                raise ValueError(f"línea {lineas}: un objeto que no es nombre, nivel, expresión ni constante")
    return lineas, constantes


def resumen(ruta, ruta_titulares, esperados):
    lineas, constantes = leer(ruta)
    titulares = [t.strip() for t in open(ruta_titulares, encoding="utf-8") if t.strip()]
    cuenta = {}
    for clase, _ in constantes:
        cuenta[clase] = cuenta.get(clase, 0) + 1
    print(f"  {lineas} líneas; {len(constantes)} constantes: "
          + ", ".join(f"{cuenta[c]} {c}" for c in sorted(cuenta)))
    teoremas = {n for c, n in constantes if c == "thm"}
    faltan = [t for t in titulares if t not in teoremas]
    axiomas = sorted(n for c, n in constantes if c == "axiom")
    esperados = sorted(a for a in esperados.split(",") if a)
    print(f"  axiom en la exportación: {', '.join(axiomas) or '(ninguno)'}")
    print(f"  axiom esperados (la unión de los footprints de los {len(titulares)} titulares): "
          f"{', '.join(esperados) or '(ninguno)'}")
    fallo = 0
    if not titulares:
        print("  ❌ la lista de titulares está vacía")
        fallo = 1
    if faltan:
        print(f"  ❌ faltan {len(faltan)} titulares en la exportación: {' '.join(faltan)}")
        fallo = 1
    else:
        print(f"  ✓ los {len(titulares)} titulares están en la exportación, como teoremas")
    if axiomas != esperados:
        print("  ❌ los axiom de la exportación no son los de los footprints")
        fallo = 1
    else:
        print("  ✓ los axiom de la exportación son exactamente los de los footprints")
    return fallo


def mutante(ruta, salida):
    hecho = None
    with open(ruta, encoding="utf-8") as h, open(salida, "w", encoding="utf-8", newline="\n") as w:
        nombres = {0: ""}
        for linea in h:
            o = json.loads(linea)
            if "in" in o:
                if "str" in o:
                    pre, s = o["str"]["pre"], o["str"]["str"]
                else:
                    pre, s = o["num"]["pre"], str(o["num"]["i"])
                base = nombres[pre]
                nombres[o["in"]] = base + "." + s if base else s
            elif hecho is None and "thm" in o:
                o["thm"]["value"] = o["thm"]["type"]
                hecho = nombres[o["thm"]["name"]]
                linea = json.dumps(o, ensure_ascii=False, separators=(",", ":")) + "\n"
            w.write(linea)
    if hecho is None:
        print("  ❌ la exportación no tiene ningún thm: no hay mutante")
        return 2
    print(f"  mutante: el valor de {hecho} (el primer thm) es ahora su tipo")
    return 0


def main(args):
    try:
        if len(args) == 4 and args[0] == "resumen":
            return resumen(args[1], args[2], args[3])
        if len(args) == 3 and args[0] == "mutante":
            return mutante(args[1], args[2])
    except (OSError, ValueError, KeyError) as e:
        print(f"  ❌ NO PUDE LEER la exportación: {e}")
        return 2
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
