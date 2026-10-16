# Next Steps — ROBINSON_PlusPlus

**Last updated:** 2026-10-16 — ADR‑143: T08 hecho (el control de pureza, en el build). Antes, el mismo día — ADR‑142: este fichero, a una página (los bloques viejos, en doc/historia/), con la lista «Pendiente además de Rosser» (T36). Antes, el mismo día — ADR‑141: los sondeos (11 de control en la CI, 53 archivados). Antes, el mismo día — ADR‑140: las decisiones del propietario (capas dentro de RPP, la línea de llegada, ADR‑139 aprobado en sus pasos 1 y 2). Antes, el mismo día — ADR‑138: la consistencia es RELATIVA a Lean; ADR‑139, PROPUESTO: el plan para acotar el proyecto, con el cono de los titulares medido. Antes, 2026-10-14 — ADR‑137: Rosser, decidido (la teoría como parámetro del verificador + T08). Antes, el mismo día — ADR‑136: `master` protegido (T14) y las decisiones del propietario del día. Antes, el mismo día — ADR‑135: T09 hecho (`TEOREMAS-E-HIPOTESIS.md` al día, con la columna «¿qué usa la prueba?» medida, y el control `[T]`). Antes, el mismo día — ADR‑134: T02 hecho (la teoría de los titulares, `T_Prf`, descrita en `AXIOMS.md` §0: contiene a PA; y dónde entra la inducción, medido: `sondeos/InduccionTitulares.lean`), con su revisión adversarial y los comentarios de los `.lean` al día (T31). Antes, 2026-10-12 — ADR‑133: T03 hecho (la tabla MANDATORIES y el control `[M]`). Antes, 2026-10-12 — ADR‑132: la auditoría del suelo, versionada (`doc/AUDITORIA-SUELO-2026-10-12.md`, 81 trabajos: es la lista de trabajo vigente; bloque nuevo, arriba) y T00 hecho. Antes, 2026-10-05 — ADR‑131: el `Classical.choice` de los titulares, medido (punto 6, nuevo); ADR‑130: las dos notas de `Meta/CodeDecode.lean`, medidas (punto 5, hecho); ADR‑129: D7 EJECUTADA (punto 2, hecho); ADR‑128: `autoImplicit` desactivado también en `lake build` (punto 4, hecho); ADR‑127: la auditoría de ADR‑124/125/126 (el punto 1, rectificado) y los 88 sondeos re‑medidos (35 compilan); ADR‑126: la refutación a profundidad 2 y el control de discriminación (`sondeos/RosserBasura.lean`, punto 1); ADR‑125: la guarda de término refutada sobre un numeral (`sondeos/RosserBasura.lean`, punto 1); ADR‑124: el control negativo del modelo, en el build (punto 3, hecho), y la auditoría de ADR‑123 (el punto 1, rectificado); ADR‑123: Rosser, Etapa 0 —la reflexión numeral, confirmada en `sondeos/RosserReflexion.lean`—; ADR‑122: D7 medida (la puerta dice NO: 48 de 226) y Rosser re‑medido; ADR‑121: Gödel I ENTERO (`⊬ ¬G`) y TARSKI, sin hipótesis (bloque nuevo, arriba). Antes, 2026-10-05 — ADR‑120: `ConsistentH` es un TEOREMA del build y Gödel I/II van SIN HIPÓTESIS (bloque nuevo, arriba). Antes, 2026-10-05 — ADR‑119: el MODELO de los 142, `ConsistentH` demostrada en un sondeo (bloque nuevo, arriba); lo siguiente, su promoción al build. Antes, 2026-10-05 — ADR‑118: la clase `AnclaEq` retirada; lo siguiente, el modelo de los 142. Antes, 2026-10-04 — ADR‑117: F1 reparado, el ancla es un TEOREMA y Gödel I/II dependen sólo de `ConsistentH` (bloque nuevo, arriba); lo siguiente, retirar la clase `AnclaEq`. Antes, el mismo día — ADR‑116: los controles endurecidos, el `thaw` de FOL hecho y la etiqueta `pre-adr115` puesta (bloque nuevo, arriba); lo siguiente es F1. Antes, 2026-10-02 — FOL borró `FOL/MetaRules.lean` (ADR‑115 §8): el punto 1 de la lista, hecho; los sondeos, re‑medidos (31 de 85). Antes, el mismo día — ADR‑115: la capa `⊢` retirada de RPP (bloque de abajo, y la lista de lo que queda). Antes, 2026-09-28 — ADR‑113: la salida (5) adoptada y aplicada (bloque de abajo). Antes, 2026-09-26 — `Prf₀` → `Prfᵢ` en todo el fichero (ADR-102: el subíndice nombra un cálculo, y `₀` es el clásico); y se tachan, en el bloque del 2026-09-22, las dos menciones a la 2.ª entrega de `ModelG` (CERRADA, ADR-100 §1.1; definitiva el 2026-09-26); el resto sigue siendo el del 2026-09-22 y **no recoge ADR-098…100**. El bloque fechado más reciente manda. ⚠️ La marca que este fichero tenía decía **2026-07-08** y vivía en la **línea 3763**, donde nadie la ve ni la actualiza; lo destapó `[E]` al rearmarse (ADR-072). Esta va arriba, que es donde se lee.

---

## ▶ PUNTO DE REANUDACIÓN (leer PRIMERO)

> # 🗓️ 2026‑10‑12 — 📋 **ADR‑132: la lista de trabajo vigente es `doc/AUDITORIA-SUELO-2026-10-12.md`**
>
> 81 trabajos priorizados con su evidencia y cómo cerrarlos. **P0**: T01 (Rosser: un enunciado con contenido antes
> de pagarlo; decide el propietario), T02 (la teoría `T_Prf` descrita con precisión; ✅ ADR‑134: contiene a PA, `AXIOMS.md` §0), T03 (MANDATORIES: M‑11, M‑10 y
> M‑6; ✅ ADR‑133), T04 (el núcleo de `[B]`). **P1**: T00 (✅ ADR‑132), T04b, T06, T07, T08, T09 (✅ ADR‑135), T15. Orden recomendado:
> T03 (✅) → T02 (✅) → T09 (✅) → T01 (decisión) → T08 → T04 → T06 → … Medido el 2026‑10‑12: `d3_prf_of_sigma1` y
> `d3_prf_of_reflect_bounded` son VACUOS (`sondeos/D3Sigma1Vacuo.lean`; T05, P2). Y D1 usa la inducción, D2 la de
> listas, y ningún titular construye un paso DNE salvo `goedel_I_neg`, al decodificar el modelo
> (`sondeos/InduccionTitulares.lean`; ADR‑134).
>
> 🗓️ **2026‑10‑14 — decisiones del propietario** (ADR‑136): T26 y T28 se REESCRIBEN; T49 (el libro), vivo y en espera;
> T14: `master` PROTEGIDO —sólo entra un commit con la CI ya verde, por una rama `ci/…` (AI‑GUIDE, `guarda_y_sube`)—, y
> un módulo de RPP se congela sólo con su fase cerrada (hoy, ninguno). T01 (Rosser), DECIDIDO por la tarde (ADR‑137):
> **la teoría como parámetro del verificador** (opción a‑ii), con **T08** como criterio de aceptación; el informe, en
> `doc/registro/2026-10-14-t01-rosser/informe.md`. Lo siguiente: **T08** → la medición de alcance y el ADR de diseño de
> T62 (ii) → el sondeo de viabilidad de Rosser; y T04, T06 y las reescrituras de T26 y T28.
>
> 🗓️ **2026‑10‑16** — ADR‑138: la consistencia que da `consistencia` es RELATIVA a Lean (PRA ⊢ Con(Lean) → Con(T_Prf))
> y no puede ser absoluta; dicho en los banners, en `TEOREMAS-E-HIPOTESIS.md` §4, en `AXIOMS.md` §0.2 y en
> `PLAN-LIBRO.md` cap. 6. ADR‑139, 🟡 PROPUESTO (decide el propietario): acotar el proyecto en tres pasos —archivar los
> sondeos (T06 → T10), congelar la historia (T33, T36, T54, T55) y contratos de capa (T66, T74)—, con el cono de los
> titulares MEDIDO por declaración (`sondeos/ConoTitulares.lean`: D3 es el 92 % del cono; lo que sobra no está en el
> build, sino en los sondeos y en la prosa). Mientras no se decida, el orden de ADR‑137 sigue en pie.
> ✏️ Decidido el mismo día (ADR‑140): capas DENTRO de RPP (un repositorio aparte sólo al cerrar una capa; Gentzen, en
> el suyo); la línea de llegada de RPP es `T_UNIVERSO` + Rosser + Löb, y Gentzen y el libro quedan fuera; las variantes
> Q++/PA/HA se miden en el diseño de T62. ADR‑139 aprobado en sus pasos 1 (sondeos) y 2 (historia), que se ejecutan
> ahora; después, el orden de ADR‑137 (T08 → T62).
> ✏️ ADR‑141 (paso 1, hecho): los sondeos, medidos con `lake lean` (39 de 93 compilan) y clasificados: 11 de control,
> que la CI compila en cada push; 28 de registro; 1 a reparar; y 53 archivados con la etiqueta `archivo/sondeos-2026-10`.
> ✏️ ADR‑142 (paso 2, hecho): la historia, a `doc/historia/` por traslado puro: ADR‑001…130 (en DECISIONS queda su
> índice), los bloques viejos de este fichero y los banners apilados; la fuente única del estado es el banner de
> `TEOREMAS-E-HIPOTESIS.md`; CHANGELOG, congelado.
>
> 🗓️ *Los bloques anteriores (del 2026‑10‑05 hacia atrás) y las secciones de junio y julio están, tal cual, en
> [doc/historia/NEXT-STEPS-hasta-2026-10-14.md](doc/historia/NEXT-STEPS-hasta-2026-10-14.md) (ADR‑142).*

---

## ⬜ Pendiente además de Rosser (T36)

**Regla:** un punto sale de esta lista sólo CERRADO con su ADR, o DESCARTADO con una nota fechada. La lista entera,
con su evidencia y cómo cerrar cada punto, es `doc/AUDITORIA-SUELO-2026-10-12.md`.

* **El orden de ADR‑137:** ~~T08~~ ✅ (ADR‑143: el control de pureza, en el build) → el ADR de diseño de T62 (la teoría como parámetro;
  cotiza también las reglas, ADR‑140) → el sondeo de viabilidad de Rosser.
* **Löb** (T70): dentro de la línea de llegada de RPP (ADR‑140).
* **Los P0 y P1 abiertos de la auditoría:** T04 (el núcleo de `[B]`), T04b (`[A]` y `[A2]` ciegos), T07 (el contrato de
  los enunciados y de los valores de las definiciones) y T15 (todo `.lean` del árbol en el build).
* **ADR‑139, paso 3:** las capas dentro de RPP (ADR‑140), con los 21 ficheros importados que no aportan nada al cono
  (T05, T66, T74).
* **Lo que se había caído de las listas** (T36): la ronda 3 y la revisión adversarial de D7 (T17), la deuda de ADR‑115
  §5 (`DEPENDENCIES.md`) y promover cuatro de `Probe/` y barrer el resto (T48).
* **Las reescrituras** de `CURRENT-STATUS-PROJECT.md` y `GODEL-STATUS.md` (T26, T28).
