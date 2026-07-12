# Development Workflow

**Author**: Julián Calderón Almendros
**Last updated:** 2026-06-05 — Adaptado a flujo IA + opción legacy `git-lock.bash`.

Guía operativa para colaborar en este proyecto. Cubre los **dos modos** activos: sesiones con asistente IA (modo principal) y trabajo humano con `git-lock.bash` (legacy, opcional).

---

## Parte 1 — Setup inicial (una vez por máquina)

### Requisitos

* **Lean 4 v4.29.1** (gestionado por `elan`).
* **`lake`** (incluido con Lean).
* **`git`** y acceso al repo `julian1c2a/ROBINSON_PlusPlus`.
* **FOL** clonado como proyecto sibling en `../FOL` (referenciado en `lakefile.lean`).

### Clonar

```bash
git clone https://github.com/julian1c2a/ROBINSON_PlusPlus.git
cd ROBINSON_PlusPlus
lake build         # verifica que compila (~23 jobs, ~1–3 min en caché fría)
```

### (Opcional) git hook legacy

Solo si vas a trabajar en modo humano con bloqueos por archivo:

```bash
bash git-lock.bash init    # instala pre-commit hook
```

---

## Parte 2 — Modo IA (flujo principal)

Sesiones colaborativas con Claude Code (u otro asistente). Sin locks por archivo; el control de cambios se hace por commits frecuentes + build verde como gate.

### Ciclo de trabajo típico

1. **Orientación**: el asistente lee `REFERENCE.md` (mapa del proyecto), `NEXT-STEPS.md` (qué toca ahora), `CURRENT-STATUS-PROJECT.md` (sorrys + módulos), `MEMORY.md` (checkpoints de sesiones previas).
2. **Edición directa**: el asistente modifica `.lean` con la herramienta `Edit` o `Write`; cada cambio significativo seguido de `lake build` para detectar regresiones inmediatas.
3. **Commit frecuente** tras cada milestone (un módulo cerrado, un axioma eliminado, una doc actualizada). Mensajes en formato `<tipo>(<scope>): <resumen>` siguiendo Conventional Commits informal.
4. **Push** al final de cada milestone (no esperar al final de la sesión).
5. **Doc sync** al cerrar un bloque de trabajo: actualizar `REFERENCE.md`, `CHANGELOG.md`, `CURRENT-STATUS-PROJECT.md`, `NEXT-STEPS.md` según los cambios.
6. **Checkpoint** al cerrar sesión: guardar archivo en `memory/project_session_YYYY-MM-DD.md` con el estado y el siguiente paso, e indexarlo en `MEMORY.md`.

### Gate de calidad

* `lake build` debe pasar (exit 0) **antes de commitear**.
* **0 sorrys reales** es la línea base del proyecto desde 2026-05-27 — cualquier sorry nuevo requiere justificación explícita en el commit.
* Si el linter `unusedSimpArgs` está activo en el módulo editado, eliminar los args señalados o documentar por qué se conservan.

### Comandos formales (definidos en `AI-GUIDE.md`, sección "Comandos Interactivos para la IA")

El usuario puede invocar estos verbos para que el asistente ejecute flujos predefinidos:

| Comando | Qué hace |
|---|---|
| `dame situación` | Reporte read-only: build, sorries, módulos, último cambio. |
| `actualiza doc` | Pasada completa de documentación tras una sesión de desarrollo. |
| `proyecta` | Extrae exports nuevos a `REFERENCE.md`. |
| `guarda y sube` | Build + commit + push. |

### Convención de commits

```text
<tipo>(<scope>): <resumen corto>

<cuerpo opcional explicando el porqué, decisiones, pendientes>

Co-Authored-By: Claude Opus X.Y <noreply@anthropic.com>
```

Tipos usados: `feat`, `fix`, `chore`, `docs`, `refactor`. Scope es típicamente el nombre del módulo (`Block7`, `Block4_C6_C7`) o `docs`.

---

## Parte 3 — Modo humano legacy (`git-lock.bash`)

Flujo histórico con bloqueos explícitos por archivo (ADR-003). **No se usa en sesiones IA**, pero la infraestructura sigue disponible.

### La regla de un solo archivo

> **A lo sumo un `.lean` puede estar desbloqueado en cualquier momento.**

### Ciclo

```bash
bash git-lock.bash list                                # qué hay desbloqueado
bash git-lock.bash unlock ROBINSON_PlusPlus/X.lean     # desbloquea para editar
# … editar X.lean …
bash git-lock.bash lock   ROBINSON_PlusPlus/X.lean     # bloquea al terminar
```

Si cambias de archivo a mitad de sesión: lock el actual antes de unlock el siguiente.

### Pre-commit hook

Bloquea commits que toquen archivos en `locked_files.txt` (o `frozen_files.txt`). Instalado con `bash git-lock.bash init`.

### Freeze permanente

Módulos completos pueden marcarse como permanentemente inmutables (`bash git-lock.bash freeze`). Las extensiones se hacen vía `*Ext.lean` (ver `AI-GUIDE.md §21`).

---

## Parte 4 — Toolchain

```bash
# Actualizar Lean (verifica build + commit automático al éxito)
bash update-toolchain.bash v4.x.x
```

---

## Parte 5 — Mantenimiento

### Regenerar el barrel root

```bash
bash gen-root.bash    # escanea ROBINSON_PlusPlus/ y reescribe ROBINSON_PlusPlus.lean
```

Si añades un módulo manualmente (sin `new-module.bash`), corre esto para sincronizar el import.

### Crear nuevo módulo desde plantilla

```bash
bash new-module.bash ModuleName          # crea ROBINSON_PlusPlus/ModuleName.lean
bash new-module.bash Topic/SubModule     # crea ROBINSON_PlusPlus/Topic/SubModule.lean
```

### Verificar estado

```bash
lake build           # ¿compila? (gate básico)
bash check-sorry.bash    # cuenta sorries reales
bash git-lock.bash list  # qué archivos están en estado lock/frozen
```

---

## Parte 6 — Estructura de archivos clave

| Archivo | Propósito |
|---|---|
| `AI-GUIDE.md` | **Lee primero**: protocolos, naming, comandos formales. |
| `REFERENCE.md` | Mapa técnico del proyecto (módulos, defs, teoremas, axiomas). |
| `NEXT-STEPS.md` | Qué toca hacer ahora. Actualizado por sesión. |
| `CHANGELOG.md` | Historia cronológica de cambios. |
| `CURRENT-STATUS-PROJECT.md` | Snapshot del build + métricas. |
| `DEPENDENCIES.md` | Grafo de dependencias verificado contra imports. |
| `MINIMAL-AXIOMS.md` | Análisis comparativo del sistema axiomático vs Q/PA⁻. |
| `DECISIONS.md` | ADRs (decisiones arquitectónicas). |
| `THOUGHTS.md` | Diario informal (no normativo). |
| `DISCUSIONES.md` | Discusión histórica sobre axiomas eliminados. |
| `PLANNING.md` | Plan estratégico de largo plazo. |
| `TuplasFuncionesYListas.md` | Spec fundacional (inmutable). |
| `NAMING-CONVENTIONS.md` | Convenciones Mathlib-style con 12 reglas. |
| `WORKFLOW.md` | Este archivo. |

---

## Parte 7 — Diferencias respecto a la versión anterior

Esta revisión (2026-06-05) reconoce que el modo de trabajo dominante es la colaboración con IA, no el flujo humano con `git-lock.bash`. Cambios:

* **Modo IA** documentado como flujo principal (Parte 2), no como nota a pie.
* **`git-lock.bash` movido a "Parte 3 — legacy"**: sigue funcional para sesiones humanas pero deja de presentarse como obligatorio.
* **Eliminado** el "Step 1 — Clone the template" / "Step 2 — Run setup": el proyecto ya existe, no hay setup desde plantilla.
* **Añadidos** comandos formales (`dame situación`, `actualiza doc`, etc.) que el usuario invoca por nombre — son la verdadera interfaz cuando trabajas con el asistente.
* **Convención de commits** explicitada con ejemplos Conventional + `Co-Authored-By` para sesiones IA.

Si quieres recuperar la versión template original, sigue en el historial git (`git log --all WORKFLOW.md`).
