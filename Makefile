# Makefile for Lean 4 projects
# Usage: make <target>
# Requires: bash, lake, git

.PHONY: footprints estratos warnings choice build clean rebuild sorry status lock unlock list init help probar-controles update-toolchain

## Build the project
build:
	lake build

## Clean build artifacts
clean:
	lake clean

## Clean and rebuild
rebuild: clean build

## Check for sorry statements
sorry:
	@bash check-sorry.bash

## Comprueba que la documentacion cuadra con el codigo (AI-GUIDE §27)
docsync:
	@bash check-doc-sync.bash

## Footprints de los titulares (criterio §9 de doc/PLAN-COMPLETITUD-FINITISTA.md).
## Un `info:` en medio de 145 jobs NO es un control: esto sí rompe.
footprints:
	@bash check-footprints.bash

## Censo de ESTRATOS (REFERENCE.md §0bis): cuantos `axiom` HABITAN cada nocion de
## derivabilidad, que es lo que dice si un postulado puede contradecir lo que se demuestra por
## induccion sobre ella (M-11, corregida en ADR-114 §2 y ADR-133: la induccion es valida; hasta
## 2026-10-12 decia «lo unico que decide si `induction` es legitima»).
## `#print axioms` es CIEGO a esto.
estratos:
	@bash check-estratos.bash

warnings:
	@bash check-warnings.bash

## La constructividad, constante a constante (T53, ADR-193): choice, noncomputable y String en RPP, FOL y
## TheoryFramework, contra doc/control/choice.tsv
choice:
	@bash check-choice.bash

## Idem, sin lake build (para iterar rapido)
docsync-quick:
	@bash check-doc-sync.bash --quick

## Show project status: locked files + sorry count
status:
	@echo "=== Lock Status ==="
	@bash git-lock.bash list
	@echo ""
	@echo "=== Sorry Status ==="
	@bash check-sorry.bash || true

## Lock a file: make lock FILE=ProjectName/Module.lean
lock:
	@[ -n "$(FILE)" ] || (echo "Usage: make lock FILE=ProjectName/Module.lean" && exit 1)
	@bash git-lock.bash lock $(FILE)

## Unlock a file: make unlock FILE=ProjectName/Module.lean
unlock:
	@[ -n "$(FILE)" ] || (echo "Usage: make unlock FILE=ProjectName/Module.lean" && exit 1)
	@bash git-lock.bash unlock $(FILE)

## List all locked files
list:
	@bash git-lock.bash list

## Initialize lock system (install git hook)
init:
	@bash git-lock.bash init

# (2026-10-18, T15, ADR-163: `make new` y `make root` se retiraron con new-module.bash y gen-root.bash. Un modulo
#  nuevo se crea a mano y se importa desde su barril; `make docsync` ([L]) dice si un fichero no esta importado.)

## Probar los CONTROLES (T47, ADR-180): strip-lean.awk frente al oraculo (leanlex + oracle2 + oracle3), los
## mutantes de strip-lean.awk frente al humo de check-sorry, y lineWFT frente a su generador. Python 3 y un awk:
## make probar-controles [PYTHON=python3] [AWK=awk]  (en la CI, con mawk: la validacion y lineWFT; los mutantes, a mano)
PYTHON ?= python3
AWK ?= awk
probar-controles:
	@$(PYTHON) scripts/pruebas/validar_strip.py $(AWK)
	@$(PYTHON) scripts/lineWFT_generar.py
	@$(PYTHON) scripts/pruebas/mutantes_strip.py $(AWK)

## Probar el par con otra versión de Lean, sin commit (T42, ADR-176): make update-toolchain [VERSION=v4.35.0]
update-toolchain:
	@bash update-toolchain.bash $(VERSION)

## Show this help
help:
	@echo "Available targets:"
	@grep -E '^## ' Makefile | sed 's/^## /  /'
