# Gentzen: el alcance, medido (T69)

**Last updated:** 2026-11-05 — [ADR‑259](../DECISIONS.md): §3, la prueba de `listInd`, en el build. Antes, 2026-11-04 — [ADR‑254](../DECISIONS.md): §6, la lección de L5‑02 para el repositorio nuevo (los
nombres de los símbolos, por índice). Antes, 2026-11-02 — creado con T69 ([ADR‑244](../DECISIONS.md)): los primeros
pasos medibles de la auditoría (el censo de la forma de los axiomas y la admisibilidad de `listInd`), y lo que harían
falta después.
**Autor:** Julián Calderón Almendros

> **Qué es esto.** Gentzen —la consistencia de la teoría por inducción transfinita hasta ε₀— está FUERA de RPP desde
> ADR‑140: nacerá en su propio repositorio, cuando empiece. T69 de `doc/AUDITORIA-SUELO-2026-10-12.md` pedía dejar antes
> medido lo que se puede medir desde aquí. Este documento lo junta. Las etiquetas: **MEDIDO** (compilado o contado,
> con su registro), **INFERIDO** (razonado, sin compilar), **ESTIMACIÓN** (sin medir).

---

## 0 · La teoría que habría que tratar

`T_Prf` ([AXIOMS.md](../AXIOMS.md) §0.1): lo que deriva `Prf` (`Meta/Hilbert.lean`) desde los 120 axiomas de
`axioms`, con los esquemas lógicos de `Prfᵢ`, DNE (`p3`) y el confinamiento (`qconf`), y dos esquemas no lógicos para
TODA fórmula: la inducción (`ind`) y la inducción de listas (`listInd`). Contiene a PA (por lectura). Un análisis
ordinal tiene que tratar todas sus reglas, no las que usan los titulares: un censo de uso no sirve (lo dijo el
verificador de CRI‑03).

## 1 · La forma de los axiomas — MEDIDO

`sondeos/CensoFormaAxiomas.lean` (REGISTRO) recorre cada axioma sin reducir ningún numeral y da su clase sintáctica en
la jerarquía aritmética, con los átomos (`lt`, `In`, `allIn`, `lineWF`, `chainOk`…) y las ecuaciones como Δ₀. La salida
entera, en `doc/registro/2026-11-02-t69/censo.txt`.

| clase | cuántos | cuáles |
|---|---|---|
| Δ₀ (sin cuantificadores) | 5 | `ax25_pred_zero`, `ax_prodp_nil`, `ax_tc_zero`, `ax_lenc_nil` y el ancla (una ecuación) |
| Π₁ | 107 | 31 de la teoría y 76 de codificación |
| Π₂ | 8 | `ax13_lt_def` y los siete `ax_lineWF_*` con guarda de testigo (`q1`, `q2`, `q3`, `leibniz`, `ind`, `qconf`, `listInd`) |

* `ax13_lt_def` es `∀n m (n < m ⇔ ∃k (n + σk = m))`: el `∃` no está acotado. Con la cota `k < m` (o `k ≤ m`) sería Π₁.
* Los siete `ax_lineWF_*` definen `lineWF` con un bicondicional cuyo lado derecho lleva `hasWitF`: dos `∃` de un cuerpo
  cuyos `∀` están acotados (`∀i (i < lenc w ⇒ …)`), es decir, Σ₁. Si los acotados contaran como cuantificadores,
  serían Π₃.
* Ningún otro axioma lleva un `∃`.

**Lo que significa (INFERIDO), y su límite.** Un axioma Π₁ cuyos átomos son primitivos recursivos es, en un cálculo
con la regla ω, una familia de instancias cerradas Δ₀ verdaderas: no cuesta nada en la eliminación de cortes. Pero la
clase es la del ENUNCIADO, con cada átomo como Δ₀: `lineWF` lo definen los siete axiomas Π₂ (un bicondicional con
una guarda Σ₁), y los axiomas que lo usan como átomo (los `ax_lineWF_*` sin guarda, `ax_chainOk_*`…) subirían de clase
al desplegarlo; `lt` lo define `ax13_lt_def`. Tratarlos como símbolos definidos —conservativamente— o desplegarlos es
la primera decisión de un análisis ordinal, y no está medida aquí. Lo medido: ningún axioma, tal como está escrito,
pide más que Π₂.

## 2 · Los esquemas

* `ind` (para toda fórmula): es la inducción de PA; con ella va ε₀.
* `listInd` (para toda fórmula): ADMISIBLE desde `ind` (§3): se reduce a la inducción de PA.
* `qconf` (`∀x(P ⇒ C) ⇒ (P ⇒ ∀x C)`, con x no libre en P) y `p3` (DNE): lógicos (el confinamiento y la lógica
  clásica). No piden ordinales.

## 3 · ¿Es `listInd` admisible desde `ind`? — MEDIDO

**Sí.** (✏️ 2026‑11‑05, [ADR‑259](../DECISIONS.md): la prueba está ya en el BUILD, `Meta/ListIndAdmisible.lean`, con sus
footprints vigilados; el sondeo guarda la medida.) `sondeos/ListIndAdmisible.lean` (REGISTRO; ≈ 6 s, 727 líneas, la prueba 437) demuestra

    theorem listInd_admisible (A : Formula) : Prf (listInductionFormula A)

para TODA fórmula `A` —con parámetros—, sin el constructor `listInd`, y lo mide: con la orden de medida de
`sondeos/InduccionTitulares.lean`, en el cierre de la prueba (2213 constantes) sólo nombran el constructor los cuatro
recorridos del teorema de la deducción y sus traducciones, que copian los pasos que reciben; cortado el cierre en
ellos, ninguna constante nombra `listInd` (ni `p3`), y los dos controles positivos —`Prf.listInd A` a secas, y el
`prf_nil_or_cons` del build, que sale de la regla derivada `prf_list_induction`— salen rojos en la misma ejecución.
`#print axioms`: `[propext, Quot.sound]`. La salida, en `doc/registro/2026-11-02-t69/listind.txt`.

* **La ruta:** inducción FUERTE sobre el código de la lista, para toda fórmula (la del build pedía una sin parámetros);
  todo código es `nil` o un `cons` (por `ind` sobre una ECUACIÓN, sin `listInd`: la del build salía de él); y la cola
  es menor que la lista (la monotonía de Cantor).
* **Lo que dice:** como TEORÍA, `listInd` no añade nada a `ind`: todo teorema de `Prf` lo es de `Prf` sin `listInd`,
  sustituyendo cada hoja `listInd` por esta derivación (INFERIDO: es una inducción sobre `Prf` que no se compila). Para
  Gentzen, es una regla menos que tratar: `listInd` se reduce a `ind`.
* **Lo que NO dice:** que `listInd` sobre en el código (sigue en `Prf`, en el verificador y en el ancla: quitarlo
  cambiaría la teoría codificada y `G`), ni cuánto sube la jerarquía de las instancias de `ind` que usa. Y, de paso: la
  derivación no construye ningún paso `p3` (es intuicionista en la lógica), aunque usa axiomas que no lo son (la
  tricotomía, `ax19_lt_trichotomy`).
* Usarla en el build pide reordenar los imports (`prf_list_induction` vive por debajo de los módulos que usa la
  prueba): ESTIMACIÓN del agente que la escribió, uno o dos días, con su ADR. No se ha hecho.

## 4 · Lo que haría falta después — ESTIMACIÓN

* **Notaciones de ordinales hasta ε₀** en Lean, con su buen orden: no las tiene ningún repositorio del propietario
  (MEDIDO por la auditoría, T69).
* **La reducción**: o la eliminación de cortes para `T_Prf` con la regla ω (Schütte), o la reducción de derivaciones de
  Gentzen; las dos piden formalizar las derivaciones como objetos (aquí, `Prf` es un `inductive` de Lean, en `Prop`).
* **La metateoría débil**: el resultado de Gentzen es PRA + TI(ε₀) ⊢ Con(PA). En Lean, la consistencia de `T_Prf` ya
  está demostrada por el modelo (`consistencia`, ADR‑120), relativa a Lean (ADR‑138); lo que Gentzen añadiría es la
  FUERZA de la metateoría que basta, y eso exige vigilar qué usa la prueba (la clase (i) de T08 es el precedente).
* **Reducir `T_Prf` a PA**: los axiomas de codificación (los 85) son definiciones de funciones primitivas recursivas
  sobre códigos; PA las define, y la reducción es conservatividad (INFERIDO, sin medir).

## 5 · Dónde vive

En su propio repositorio, cuando empiece (ADR‑140). De RPP necesita: la teoría (`Minimal/Axioms.lean`, `Meta/Hilbert.lean`),
el censo de §1 y el resultado de §3. El horizonte, en [NEXT-STEPS.md](../NEXT-STEPS.md) («Pendiente además de Rosser»,
T36).

## 6 · Una lección de RPP para el repositorio nuevo (ADR‑254)

**Los nombres de los símbolos, por índice, no carácter a carácter** (L5‑02 de la auditoría de la base). En RPP, el
código de un símbolo es la lista de sus caracteres, y cada carácter, el numeral UNARIO de su punto de código (σ son 963
sucesores anidados): en dos axiomas del verificador, el 98–99 % de los nodos del código son esos nombres
(`sondeos/RecodCoste.lean`: `ax_tc_zero`, 49 015 nodos, 48 528 de nombres; con un índice, unos 708). Es la razón
escrita de que el código de los axiomas sea opaco y de que haga falta subir `maxRecDepth` para levantarlos. En RPP no
se cambia —cambiaría todos los códigos, `G`, el ancla y el modelo, y nada evalúa el ancla (ADR‑117)—; un repositorio
que empieza puede codificar cada símbolo por su índice en una tabla, o con un código etiquetado, desde el principio.
