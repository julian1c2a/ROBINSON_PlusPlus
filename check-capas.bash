#!/bin/bash
# check-capas.bash — las CAPAS de RPP: el manifiesto (módulo → capa) y la dirección de los imports (B1 paso 5, ADR-271).
#
# ⛔ POR QUÉ EXISTE. El diseño de las capas (ADR-266, decidido por el propietario el 2026-11-16) se ejecutó en cuatro
# pasos (ADR-267…270) hasta que ningún import sube de capa y ningún módulo con titulares de la clase (i) ve la semántica.
# Eso se MIDIÓ con scripts del registro, una vez; sin un control, el siguiente import lo deshace sin que nadie lo vea: el
# build compila igual. T08 (`#pureza`) vigila la pureza constante a constante; esto, módulo a módulo.
#
# QUÉ COMPRUEBA, contra doc/control/capas.tsv (el manifiesto; su cabecera dice el formato y la regla):
#   FALTA / DOS_VECES / NO_EXISTE  cada módulo de la librería (los ficheros de ROBINSON_PlusPlus/ y el barril
#                       ROBINSON_PlusPlus.lean) tiene una fila y sólo una, y cada fila nombra un módulo que existe;
#   CAPA                la capa de cada fila es una de las declaradas (las filas `capa`, que tienen que ser las de la regla);
#   SUBE / BARRIL       cada import entre módulos de RPP va a una capa que la del importador puede importar (ADR-266 §2:
#                       C7.i, ni C5 ni C6; la regla NO es un orden —C5 está «debajo» de C7.i y C7.i no puede importarla—),
#                       o tiene una excepción `sube`; nadie importa un barril;
#   SIN_RAZON / SOBRA   cada excepción tiene su razón, y hace falta: el import existe y la regla no lo permite;
#   TITULAR             los titulares de T07 (TITULARES, Meta/ContratoTitulares.lean) viven en C7: los de la clase (i)
#                       (PUROS, Meta/PurezaTitulares.lean) en C7.i, los demás en C7.ii o C7.iii, salvo los que tienen
#                       fila `titular` (D1, D2, D3 y `consistencia`, ADR-266 §2 y §3); el módulo de un titular es su
#                       espacio de nombres (NAMING-CONVENTIONS §6: TITULAR_MODULO si no es un módulo).
#   Los imports se leen de la CABECERA de cada fichero, como Lean: desde el principio, saltando comentarios (`--` y
#   `/- … -/`, anidados), hasta lo primero que no es un `import`. Lo que viene de fuera de RPP (FOL, Lean) no tiene capa.
#
# 🔑 CALIBRACIÓN (feedback de los controles que no comprueban nada). (1) Dos lecturas independientes de los imports: la
# de la cabecera y la de todas las líneas `import ROBINSON_PlusPlus…` del fichero (la de gen-dependencies.py); si no
# cuentan lo mismo, es rojo (NO_LEIDA: un import que la cabecera no ve, o un comentario que lo parece). (2) Si no se leen
# TITULARES y PUROS (EXTRACCION), rojo. (3) `--autotest`: sobre una COPIA del árbol, por el MISMO camino (`comprobar`),
# la copia limpia da verde con las mismas cifras que el árbol, una excepción con razón hace verde un import que sube, y
# cada mutante da rojo con SU código (no basta una salida ≠ 0): veinticinco, al menos uno por cada manera de fallar de arriba.
#
# 🔧 Sin `lake` (lee texto): desde la raíz de RPP, en Git Bash o en la CI.
#   bash check-capas.bash              # el manifiesto contra el árbol
#   bash check-capas.bash --autotest   # los mutantes

set -uo pipefail
export PATH="/usr/bin:$PATH"
export LC_ALL=C   # awk en modo byte, como mawk en la CI
cd "$(dirname "$0")" || exit 2
MANIFIESTO=doc/control/capas.tsv

# ── la cabecera de cada fichero: «ARISTA m x» por cada import de RPP, «EXTERNO m x» por los de fuera, «RARO m línea» si
#    una línea de import no se sabe leer, y «CUENTA m leídas vistas» (vistas: todas las líneas que lo parecen)
read -r -d '' CABECERA <<'EOF'
function modulo(f) { sub(/^\.\//, "", f); sub(/\.lean$/, "", f); gsub(/\//, ".", f); return f }
function fin() { if (m != "") print "CUENTA\t" m "\t" leidas "\t" vistas }
FNR == 1 { fin(); m = modulo(FILENAME); prof = 0; hecho = 0; leidas = 0; vistas = 0 }
{
  l = $0; sub(/\r$/, "", l)
  if (l ~ /^[ \t]*((public|meta|private)[ \t]+)*import[ \t]+ROBINSON_PlusPlus/) vistas++
  if (hecho) next
  while (1) {
    if (prof > 0) {
      a = index(l, "/-"); c = index(l, "-/")
      if (a == 0 && c == 0) break
      if (a > 0 && (c == 0 || a < c)) { prof++; l = substr(l, a + 2) } else { prof--; l = substr(l, c + 2) }
      continue
    }
    sub(/^[ \t]+/, "", l)
    if (l == "") break
    if (substr(l, 1, 2) == "--") break
    if (substr(l, 1, 2) == "/-") { prof = 1; l = substr(l, 3); continue }
    if (l ~ /^((public|meta|private)[ \t]+)*import[ \t]/) {
      sub(/^((public|meta|private)[ \t]+)*import[ \t]+/, "", l)
      n = split(l, t, /[ \t]+/)
      if (n > 1 && substr(t[2], 1, 2) != "--") { print "RARO\t" m "\t" $0; break }
      if (t[1] ~ /^ROBINSON_PlusPlus/) { print "ARISTA\t" m "\t" t[1]; leidas++ } else print "EXTERNO\t" m "\t" t[1]
      break
    }
    hecho = 1
    break
  }
}
END { fin() }
EOF

# ── las reglas. Entradas: el manifiesto, los módulos, las aristas, TITULARES y PUROS. Salida: «ERR código mensaje» e
#    «INFO …». La regla de ADR-266 §2 está AQUÍ, no en el manifiesto: cambiarla pide un ADR y rompe el autotest.
read -r -d '' REGLAS <<'EOF'
function err(c, s) { print "ERR\t" c "\t" s; nerr++ }
function trim(s) { sub(/^[ \t]+/, "", s); sub(/[ \t]+$/, "", s); return s }
BEGIN {
  FS = "\t"
  ORDEN = "C0 C1 C2 C3 C4 C5 C6 C7.i C7.ii C7.iii C8 barril"
  nc = split(ORDEN, CAPAS, " ")
  P["C0"] = "C0"; P["C1"] = "C0 C1"; P["C2"] = "C0 C1 C2"; P["C3"] = "C0 C1 C2 C3"; P["C4"] = "C0 C1 C2 C3 C4"
  P["C5"] = "C0 C1 C2 C3 C4 C5"; P["C6"] = "C0 C1 C2 C3 C4 C5 C6"
  P["C7.i"] = "C0 C1 C2 C3 C4 C7.i"
  P["C7.ii"] = "C0 C1 C2 C3 C4 C5 C6 C7.i C7.ii"
  P["C7.iii"] = "C0 C1 C2 C3 C4 C5 C6 C7.i C7.ii C7.iii"
  P["C8"] = "C0 C1 C2 C3 C4 C5 C6 C7.i C7.ii C7.iii C8"
  P["barril"] = "C0 C1 C2 C3 C4 C5 C6 C7.i C7.ii C7.iii C8 barril"
  for (i = 1; i <= nc; i++) { n = split(P[CAPAS[i]], a, " "); for (j = 1; j <= n; j++) puede[CAPAS[i], a[j]] = 1 }
  # 1. el manifiesto
  while ((getline l < MAN) > 0) {
    sub(/\r$/, "", l)
    if (l ~ /^#/ || l ~ /^[ \t]*$/) continue
    n = split(l, f, "\t")
    if (f[1] == "capa") {
      if (n != 3 || trim(f[3]) == "") { err("FORMATO", "fila capa sin su descripción: " l); continue }
      if (f[2] in declarada) err("DOS_VECES", "la capa " f[2] " está declarada dos veces")
      declarada[f[2]] = f[3]
    } else if (f[1] == "sube") {
      if (n > 4) { err("FORMATO", "fila sube con más de cuatro campos: " l); continue }
      k = f[2] SUBSEP f[3]
      if (k in sube) err("DOS_VECES", "la excepción " f[2] " → " f[3] " está dos veces")
      sube[k] = 1; nsubeD++
      if (n < 4 || trim(f[4]) == "") err("SIN_RAZON", "la excepción " f[2] " → " f[3] " no tiene razón")
    } else if (f[1] == "titular") {
      if (n > 3) { err("FORMATO", "fila titular con más de tres campos: " l); continue }
      if (f[2] in excT) err("DOS_VECES", "la excepción del titular " f[2] " está dos veces")
      excT[f[2]] = 1
      if (n < 3 || trim(f[3]) == "") err("SIN_RAZON", "la excepción del titular " f[2] " no tiene razón")
    } else if (f[1] ~ /^ROBINSON_PlusPlus/) {
      if (n != 2) { err("FORMATO", "fila de módulo que no es «módulo<TAB>capa»: " l); continue }
      if (f[1] in capa) err("DOS_VECES", f[1] " tiene dos filas (" capa[f[1]] " y " f[2] ")")
      capa[f[1]] = f[2]
    } else err("FORMATO", "fila que no sé leer: " l)
  }
  close(MAN)
  for (i = 1; i <= nc; i++) if (!(CAPAS[i] in declarada)) err("CAPA", "la capa " CAPAS[i] " de la regla no tiene fila capa")
  for (c in declarada) if (!(c in P)) err("CAPA", "la fila capa " c " no es una capa de la regla (ADR-266 §2)")
  for (x in capa) if (!(capa[x] in P)) err("CAPA", x " está en la capa " capa[x] ", que no existe")
  # 2. los módulos
  while ((getline l < MODS) > 0) { sub(/\r$/, "", l); if (l == "") continue; existe[l] = 1; nmods++; if (!(l in capa)) err("FALTA", l " no tiene fila en el manifiesto") }
  close(MODS)
  for (x in capa) if (!(x in existe)) err("NO_EXISTE", "la fila " x " nombra un módulo que no existe")
  # 3. las aristas
  while ((getline l < ARIS) > 0) {
    sub(/\r$/, "", l)
    n = split(l, f, "\t")
    if (f[1] == "CUENTA") { if (f[3] != f[4]) err("NO_LEIDA", f[2] ": " f[4] " líneas «import ROBINSON_PlusPlus…» y la cabecera lee " f[3] " (¿un import tras la cabecera, o un comentario que empieza por «import»?)"); continue }
    if (f[1] == "RARO") { err("CABECERA", f[2] ": una línea de import que no sé leer: " f[3]); continue }
    if (f[1] != "ARISTA") continue
    a1 = f[2]; b1 = f[3]; naris++; if ((a1 in capa) && capa[a1] == "barril") nbar++
    arista[a1, b1] = 1
    if (!(b1 in existe)) { err("IMPORT_DESCONOCIDO", a1 " importa " b1 ", que no es un módulo de la librería"); continue }
    if (!(a1 in capa) || !(b1 in capa)) continue
    ca = capa[a1]; cb = capa[b1]
    if ((ca, cb) in puede) { if ((a1, b1) in sube) err("SOBRA", "la excepción " a1 " → " b1 " no hace falta: " ca " puede importar " cb); continue }
    if ((a1, b1) in sube) { nsube++; continue }
    if (cb == "barril") err("BARRIL", a1 " (" ca ") importa el barril " b1)
    else err("SUBE", a1 " (" ca ") importa " b1 " (" cb "), y " ca " sólo puede importar " P[ca])
  }
  close(ARIS)
  for (k in sube) if (!(k in arista)) { split(k, kk, SUBSEP); err("SOBRA", "la excepción " kk[1] " → " kk[2] " no tiene import") }
  # 4. los titulares
  while ((getline l < PUR) > 0) { sub(/\r$/, "", l); if (l != "") { puro[l] = 1; npur++ } }
  close(PUR)
  while ((getline l < TIT) > 0) {
    sub(/\r$/, "", l)
    if (l == "") continue
    titular[l] = 1; ntit++
    mt = l; sub(/\.[^.]+$/, "", mt)
    if (!(mt in capa)) { err("TITULAR_MODULO", "el titular " l ": su espacio de nombres, " mt ", no es un módulo"); continue }
    ct = capa[mt]
    if (l in excT) { if (ct ~ /^C7/) err("SOBRA", "la excepción del titular " l " no hace falta: está en " ct); else porCapaT[ct]++; continue }
    porCapaT[ct]++
    if (l in puro) { if (ct != "C7.i") err("TITULAR", "el titular " l ", de la clase (i) (PUROS), está en " ct ", no en C7.i") }
    else if (ct != "C7.ii" && ct != "C7.iii") err("TITULAR", "el titular " l ", que no es de la clase (i), está en " ct ", no en C7.ii ni en C7.iii")
  }
  close(TIT)
  for (t in excT) if (!(t in titular)) err("SOBRA", "la excepción del titular " t " no nombra un titular de TITULARES")
  if (ntit < 12 || npur < 1) err("EXTRACCION", "sólo " ntit + 0 " titulares y " npur + 0 " de la clase (i): no se leyeron TITULARES o PUROS")
  for (t in puro) if (!(t in titular)) err("EXTRACCION", t " está en PUROS y no en TITULARES: la lectura de las listas falla")
  # el resumen
  for (x in capa) porCapa[capa[x]]++
  s = ""; st = ""
  for (i = 1; i <= nc; i++) { s = s " " CAPAS[i] ":" porCapa[CAPAS[i]] + 0; if (porCapaT[CAPAS[i]] > 0) st = st " " CAPAS[i] ":" porCapaT[CAPAS[i]] }
  print "INFO\tmódulos\t" nmods + 0 "\t" s
  print "INFO\timports\t" naris + 0 "\t" nsube + 0 "\t" nsubeD + 0 "\t" nbar + 0
  print "INFO\ttitulares\t" ntit + 0 "\t" st
}
EOF

# lista FICHERO DEF: los nombres ``ROBINSON_PlusPlus… de «def DEF : List Name := [ … ]», sin los comentarios `--` (que
# pueden llevar un «]»); se acaba en el primer «]» de código
lista() {
  awk -v D="$2" '
    index($0, "def " D " : List Name := [") == 1 { dentro = 1 }
    dentro {
      l = $0; sub(/\r$/, "", l); i = index(l, "--"); if (i > 0) l = substr(l, 1, i - 1)
      while ((i = index(l, "``ROBINSON_PlusPlus")) > 0) {
        l = substr(l, i + 2); j = 1
        while (j <= length(l) && index(", ]\t", substr(l, j, 1)) == 0) j++
        print substr(l, 1, j - 1); l = substr(l, j)
      }
      if (index(l, "]") > 0) exit
    }' "$1"
}

# comprobar RAIZ MANIFIESTO: las reglas sobre el árbol de RAIZ, por la salida «ERR/INFO»
comprobar() {
  local raiz="$1" man="$2" t
  t=$(mktemp -d)
  ( cd "$raiz" && { find ROBINSON_PlusPlus -name '*.lean'; echo ROBINSON_PlusPlus.lean; } ) \
    | sed -e 's/\.lean$//' -e 's|/|.|g' | LC_ALL=C sort > "$t/modulos.txt"
  ( cd "$raiz" && awk "$CABECERA" $(find ROBINSON_PlusPlus -name '*.lean' | LC_ALL=C sort) ROBINSON_PlusPlus.lean ) > "$t/aristas.txt"
  lista "$raiz/ROBINSON_PlusPlus/Meta/ContratoTitulares.lean" TITULARES > "$t/titulares.txt"
  lista "$raiz/ROBINSON_PlusPlus/Meta/PurezaTitulares.lean" PUROS > "$t/puros.txt"
  awk -v MAN="$man" -v MODS="$t/modulos.txt" -v ARIS="$t/aristas.txt" -v TIT="$t/titulares.txt" -v PUR="$t/puros.txt" \
    "$REGLAS" < /dev/null
  rm -rf "$t"
}

if [ "${1:-}" = "--autotest" ]; then
  echo "════ AUTOTEST DE check-capas.bash: los mutantes, sobre una copia del árbol ════"
  AT=$(mktemp -d)
  trap 'rm -rf "$AT"' EXIT
  mkdir -p "$AT/limpia"
  cp -r ROBINSON_PlusPlus ROBINSON_PlusPlus.lean "$AT/limpia/"
  cp "$MANIFIESTO" "$AT/limpia/capas.tsv"
  F=0
  REAL=$(comprobar . "$MANIFIESTO" | grep '^INFO')
  LIMPIA=$(comprobar "$AT/limpia" "$AT/limpia/capas.tsv")
  if grep -q '^ERR' <<< "$LIMPIA" || [ "$(grep '^INFO' <<< "$LIMPIA")" != "$REAL" ] || [ -z "$REAL" ]; then
    echo "  ✗ la copia limpia no da verde con las cifras del árbol:"; printf '%s\n' "$LIMPIA" | head -5 | sed 's/^/      /'; F=1
  else
    echo "  ✓ la copia limpia: verde, con las cifras del árbol ($(grep -c . <<< "$REAL") líneas de resumen)"
  fi
  T=$'\t'
  ante() { { printf '%s\n' "$2"; cat "$1"; } > "$1.x" && mv "$1.x" "$1"; }   # una línea al principio del fichero
  quita() { grep -v "$2" "$1" > "$1.x"; mv "$1.x" "$1"; }
  # mutante NOMBRE CÓDIGO PROHIBIDO ACCIÓN: la acción sobre una copia limpia; tiene que dar rojo CON el código, y sin
  # el prohibido (o «-»); el código «VERDE» pide lo contrario: ningún ERR, y el import que sube, contado
  mutante() {
    local nombre="$1" esperado="$2" prohibido="$3" accion="$4" sal
    rm -rf "$AT/m"; cp -r "$AT/limpia" "$AT/m"
    ( cd "$AT/m" && eval "$accion" )
    sal=$(comprobar "$AT/m" "$AT/m/capas.tsv")
    if [ "$esperado" = "VERDE" ]; then
      if ! grep -q '^ERR' <<< "$sal" && grep -q "^INFO${T}imports${T}[0-9]*${T}1${T}1${T}[0-9]*\$" <<< "$sal"; then echo "  ✓ $nombre: verde"
      else echo "  ✗ $nombre: tenía que dar verde, con un import que sube admitido:"; printf '%s\n' "$sal" | head -4 | sed 's/^/      /'; F=1; fi
      return
    fi
    if grep -q "^ERR${T}${esperado}${T}" <<< "$sal" && { [ "$prohibido" = "-" ] || ! grep -q "^ERR${T}${prohibido}${T}" <<< "$sal"; }; then
      echo "  ✓ $nombre: rojo, $esperado"
    else
      echo "  ✗ $nombre: tenía que dar $esperado$([ "$prohibido" != "-" ] && echo " y no $prohibido"); dio:"
      printf '%s\n' "$sal" | grep '^ERR' | head -4 | sed 's/^/      /'; F=1
    fi
  }
  L=ROBINSON_PlusPlus/Meta/Lob.lean; N=ROBINSON_PlusPlus/Meta/NatArithPrf.lean
  mutante "una fila borrada" FALTA - "quita capas.tsv '^ROBINSON_PlusPlus\.Meta\.Lob$T'"
  mutante "un módulo nuevo sin fila" FALTA - "printf 'import ROBINSON_PlusPlus.Minimal.Axioms\n' > ROBINSON_PlusPlus/Meta/ModuloNuevo.lean"
  mutante "una fila dos veces" DOS_VECES - "printf 'ROBINSON_PlusPlus.Meta.Lob${T}C7.i\n' >> capas.tsv"
  mutante "una fila de un módulo que no existe" NO_EXISTE - "printf 'ROBINSON_PlusPlus.Meta.NoExiste${T}C4\n' >> capas.tsv"
  mutante "una capa que no existe" CAPA - "quita capas.tsv '^ROBINSON_PlusPlus\.Meta\.Lob$T'; printf 'ROBINSON_PlusPlus.Meta.Lob${T}C9\n' >> capas.tsv"
  mutante "una capa de la regla sin su fila" CAPA - "quita capas.tsv '^capa${T}C6${T}'"
  mutante "C2 importa C5" SUBE - "ante $N 'import ROBINSON_PlusPlus.Meta.Consistencia'"
  mutante "C7.i importa C5 (la regla no es un orden)" SUBE - "ante $L 'import ROBINSON_PlusPlus.Meta.ModeloEstandar'"
  mutante "C7.i importa C6" SUBE - "ante $L 'import ROBINSON_PlusPlus.Meta.PuenteFOL'"
  mutante "un import que sube, tras comentarios" SUBE - "ante $N 'import ROBINSON_PlusPlus.Meta.Consistencia -- al final'; ante $N '-- una línea'; ante $N '   de varias líneas -/'; ante $N '/- un bloque /- anidado -/'"
  mutante "un import tras la cabecera" NO_LEIDA SUBE "printf '\nimport ROBINSON_PlusPlus.Meta.Consistencia\n' >> $N"
  mutante "un import dentro de un comentario" NO_LEIDA SUBE "ante $N '-/'; ante $N 'import ROBINSON_PlusPlus.Meta.Consistencia'; ante $N '/- un comentario:'"
  mutante "una línea de import que no se sabe leer" CABECERA - "ante $N 'import ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Consistencia'"
  mutante "un import de un módulo que no existe" IMPORT_DESCONOCIDO - "ante $N 'import ROBINSON_PlusPlus.Meta.NoExiste'"
  mutante "un módulo importa un barril" BARRIL - "ante $L 'import ROBINSON_PlusPlus.Meta'"
  mutante "una excepción con su razón (control positivo)" VERDE - "ante $N 'import ROBINSON_PlusPlus.Meta.Consistencia'; printf 'sube${T}ROBINSON_PlusPlus.Meta.NatArithPrf${T}ROBINSON_PlusPlus.Meta.Consistencia${T}una razón\n' >> capas.tsv"
  mutante "una excepción sin razón" SIN_RAZON SUBE "ante $N 'import ROBINSON_PlusPlus.Meta.Consistencia'; printf 'sube${T}ROBINSON_PlusPlus.Meta.NatArithPrf${T}ROBINSON_PlusPlus.Meta.Consistencia${T} \n' >> capas.tsv"
  mutante "una excepción sin import" SOBRA - "printf 'sube${T}ROBINSON_PlusPlus.Meta.Lob${T}ROBINSON_PlusPlus.Meta.Consistencia${T}una razón\n' >> capas.tsv"
  mutante "una excepción que no sube" SOBRA - "ante $L 'import ROBINSON_PlusPlus.Minimal.Axioms'; printf 'sube${T}ROBINSON_PlusPlus.Meta.Lob${T}ROBINSON_PlusPlus.Minimal.Axioms${T}una razón\n' >> capas.tsv"
  mutante "un titular nuevo en C5" TITULAR - "sed 's/^def TITULARES : List Name := \[/&\n  \`\`ROBINSON_PlusPlus.Meta.ModeloEstandar.x,/' ROBINSON_PlusPlus/Meta/ContratoTitulares.lean > c.x && mv c.x ROBINSON_PlusPlus/Meta/ContratoTitulares.lean"
  mutante "un titular de la clase (ii) en PUROS" TITULAR - "sed 's/^def PUROS : List Name := \[/&\n  \`\`ROBINSON_PlusPlus.Meta.TitularesII.goedel_I,/' ROBINSON_PlusPlus/Meta/PurezaTitulares.lean > c.x && mv c.x ROBINSON_PlusPlus/Meta/PurezaTitulares.lean"
  mutante "un titular cuyo espacio de nombres no es un módulo" TITULAR_MODULO - "sed 's/^def TITULARES : List Name := \[/&\n  \`\`ROBINSON_PlusPlus.Meta.NoExiste.x,/' ROBINSON_PlusPlus/Meta/ContratoTitulares.lean > c.x && mv c.x ROBINSON_PlusPlus/Meta/ContratoTitulares.lean"
  mutante "sin la excepción de consistencia" TITULAR - "quita capas.tsv '^titular${T}ROBINSON_PlusPlus\.Meta\.Consistencia\.consistencia$T'"
  mutante "una excepción de un titular que está en C7" SOBRA - "printf 'titular${T}ROBINSON_PlusPlus.Meta.Lob.lob${T}una razón\n' >> capas.tsv"
  mutante "TITULARES que no se lee" EXTRACCION - "sed 's/^def TITULARES :/def TITULARES2 :/' ROBINSON_PlusPlus/Meta/ContratoTitulares.lean > c.x && mv c.x ROBINSON_PlusPlus/Meta/ContratoTitulares.lean"
  if [ "$F" = 0 ]; then
    echo "✅ autotest de check-capas.bash: la copia limpia, verde; la excepción con razón, verde; cada mutante, rojo con su código."
    exit 0
  fi
  echo "❌ autotest de check-capas.bash."
  exit 1
fi

echo "════ LAS CAPAS DE RPP: el manifiesto ($MANIFIESTO) y la dirección de los imports (ADR-266, ADR-271) ════"
if [ ! -f "$MANIFIESTO" ]; then echo "  ❌ no existe $MANIFIESTO."; exit 1; fi
SALIDA=$(comprobar . "$MANIFIESTO")
printf '%s\n' "$SALIDA" | awk -F'\t' '
  $1 == "INFO" && $2 == "módulos" { print "  " $3 " módulos (con los dos barriles), por capa:" $4 }
  $1 == "INFO" && $2 == "imports" { print "  " $3 " imports entre módulos de RPP (" $3 - $6 " entre los módulos y " $6 " de los barriles); suben de capa, con su excepción: " $4 " (excepciones declaradas: " $5 ")" }
  $1 == "INFO" && $2 == "titulares" { print "  " $3 " titulares de T07, por la capa de su módulo:" $4 }'
NERR=$(grep -c '^ERR' <<< "$SALIDA")
if [ "$NERR" = 0 ]; then
  echo "✅ las capas: cada módulo con su fila, ningún import que suba sin excepción, los titulares en su capa."
  exit 0
fi
printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "ERR" { print "  ❌ [" $2 "] " $3 }'
echo "❌ las capas: $NERR fallos (el formato y la regla, en la cabecera de $MANIFIESTO)."
exit 1
