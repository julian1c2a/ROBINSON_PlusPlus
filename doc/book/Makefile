# =============================================================================
#  doc/book — Incompletitud, formalizada
#  Ver PLAN-LIBRO.md §4 y §7.  Este Makefile NO toca la compilación Lean.
# =============================================================================
LATEXMK  ?= latexmk
PY       ?= python3
# Motor: LuaLaTeX si su capa de fuentes (luaotfload) está disponible; si no,
# XeLaTeX. Se puede forzar:  make ENGINE=-xelatex
ENGINE   ?= $(shell kpsewhich luaotfload-main.lua >/dev/null 2>&1 && echo -lualatex || echo -xelatex)
FLAGS     = -interaction=nonstopmode -halt-on-error -file-line-error

.PHONY: all extraer pdf verificar simbolos terminos ambito subir axiomas axiomas-fix clean distclean help

## all: extrae, compila y verifica que lo impreso coincide con el repo
all: extraer pdf verificar simbolos terminos

## extraer: vuelca a extraido/ las declaraciones citadas en fragmentos.json
extraer:
	@$(PY) scripts/extraer.py

## pdf: compila libro.pdf (falla si falta algún fragmento)
pdf:
	@$(LATEXMK) $(ENGINE) $(FLAGS) libro.tex

## verificar: comprueba que el código IMPRESO en el PDF es el del repo (§2.1)
verificar:
	@$(PY) scripts/verificar_pdf.py

## simbolos: todo \ident{} del libro nombra algo que existe en el repo (§2.6)
simbolos:
	@$(PY) scripts/simbolos.py --estricto

## terminos: ningún término del vocabulario se usa antes de definirse (§2.7)
terminos:
	@$(PY) scripts/terminos.py

## ambito: comprueba que sólo el libro está preparado para subir
ambito:
	@$(PY) scripts/ambito.py

## subir: compila, verifica, prepara SÓLO el libro y commitea.  make subir MSG='...'
subir: all
	@test -n "$(MSG)" || { echo "falta el mensaje:  make subir MSG='...'"; exit 1; }
	@$(PY) scripts/ambito.py --añadir
	@cd ../.. && git diff --cached --stat
	@cd ../.. && git commit -m "$(MSG)"

## axiomas: mide el #print axioms REAL de cada fragmento (necesita lake y lean)
axiomas:
	@$(PY) scripts/extraer.py --axiomas

## axiomas-fix: mide y ESCRIBE los footprints medidos en fragmentos.json
axiomas-fix:
	@$(PY) scripts/extraer.py --axiomas --fix-footprint

## clean: borra los auxiliares de LaTeX
clean:
	@$(LATEXMK) -C libro.tex >/dev/null 2>&1 || true
	@rm -f *.aux *.log *.out *.toc *.fls *.fdb_latexmk

## distclean: clean + borra todo lo generado en extraido/
distclean: clean
	@rm -f extraido/*.tex extraido/_sonda.lean

## help: esta lista
help:
	@grep -E '^## ' Makefile | sed 's/^## /  /'
