# Escalando el proyecto: ROBINSON_PlusPlus ↔ DeepArithmetic (sobre FOL⁼)

**Última actualización:** 2026-07-08
**Autor:** Julián Calderón Almendros

> Estudio del enlace entre `ROBINSON_PlusPlus` y `Lean4_vs_PureLogic` (proyecto **DeepArith**),
> y de cómo el trabajo actual (cierre de Gödel II vía la Σ₁-completitud provable) fabrica el
> activo común que ambos comparten a través del kernel **FOL⁼**.

---

## 0 · Tesis

`ROBINSON_PlusPlus` y `DeepArith` son **los dos extremos del mismo eje**, montados sobre el
**mismo kernel `FOL`**. El toolkit inductivo/aritmético/metamatemático que ROBINSON está
construyendo para cerrar Gödel II es **exactamente** el que DeepArith necesita para su capa
aritmética (Fase 2–3) y su capa de computabilidad (`Automata`/`TuringMachine`). Como comparten
kernel, ese toolkit **se cosecha una vez y sirve a los dos**. «Escalar el proyecto» = subir esas
piezas a FOL⁼ y hospedar DeepArith sobre ellas.

---

## 1 · El artefacto de enlace: el kernel `FOL` compartido

Ambos `lakefile.lean` declaran la MISMA dependencia:

```lean
require FOL from "../FOL"
```

FOL⁼ es el cimiento común:

- Motor de deducción natural `Derives Γ P` (índices De Bruijn, manejo higiénico de variables).
- `substFormula` / `liftFormula` + su **toolkit De Bruijn** (`FOL/Theorems/Eq.lean`:
  `substTerm_liftTerm`, `substTerm_liftLift`, `liftTerm_comm_zero`, `subst_subst_lift_gen`,
  lema de Barendregt, …).
- Meta-reglas ω en `FOL/MetaRules.lean` (`imp_intro`, `gen`, `raa`, `or_elim`, `ex_elim`, `dne`).

**Consecuencia:** todo endurecimiento de FOL hecho desde ROBINSON (p. ej. el fix de solidez
`subst_lift_cancel_formula` de axioma-falso → teorema, o el toolkit De Bruijn) **beneficia
directamente a DeepArith**, y viceversa.

---

## 2 · Los dos extremos del eje

| | ROBINSON_PlusPlus | DeepArith (`Lean4_vs_PureLogic`) |
|---|---|---|
| Filosofía | **Minimalista** + metamatemática | **Maximalista** (universo $V$) |
| Base | Robinson Q (34 axiomas, **sin inducción**) | ZFC-like + **ε-Inducción** (Fundación/Recursión) |
| Datos | `cons`/`nil` (listas), pares Cantor | primitivas disjuntas `n_zero`/`n_succ`/`l_cons`/`tup` (Von Neumann) |
| Objetivo probado | Cantor, listas, TFA sin inducción | aritmética, listas, árboles, **autómatas, Turing** |
| Joya | **Gödel I/II REAL** (arithmetización, verificador `Prf`, Σ₁-completitud) | teoría de la **computabilidad a nivel objeto** |
| Estado | 0 sorrys, Gödel I real + D1/D2 reales | en desarrollo (con `sorry`s en `ArithmeticAddProofs`) |

ROBINSON explora **qué se puede sin inducción** y luego construye la **metamatemática** (Gödel);
DeepArith explora **hasta dónde se llega con inducción fuerte** (ε-Inducción) en un universo rico.

---

## 3 · Dónde ROBINSON ayuda a cerrar DeepArith

### 3.1 El toolkit aritmético `Prf` = lo que DeepArith Fase 2–3 necesita

Lo que ROBINSON está fabricando AHORA para Gödel II (plan 12-A, `GODEL-D3-TRACKED-DESIGN.md`):

- **`prf_nat_induction`** (eliminador de inducción natural), **`prf_add_zero_left`** (`0+n=n`),
  **`prf_add_succ_left`** (`σm+n=σ(m+n)`), toolkit de `<` (`prf_zero_lt_succ`, …).
- **capa numérica de listas** `lenc`/`nthc` + caracterización acotada de `In`.
- **Σ₁-completitud provable** (β-función / Δ₀ del verificador).

Es **exactamente** la maquinaria de razonamiento inductivo sobre operaciones recursivas que
DeepArith requiere para:

- **Fase 2**: `succ(x)+y=succ(x+y)`, conmutatividad de `+` (¡su `ArithmeticAddProofs` aún tiene
  `sorry`s en el caso base/paso de `0+n=n`!). ROBINSON ya resolvió ese patrón exacto
  (`prf_add_zero_left`) a 0-sorry.
- **Fase 3**: `to_binary`/`to_base10`, división euclídea (`n_div`/`n_mod`) con **terminación**
  probada por inducción.

> Nota: la aritmética de ROBINSON está a nivel del cálculo finitario `Prf` y DeepArith usa
> `Derives` directamente; el puente es que `Prf → Derives` (`prf_to_derives`) y ambos comparten
> `substFormula`/`liftFormula`. La **metodología** (predicado inductivo + eliminador + normalización
> De Bruijn `norm11`/`norm21`/`norm32`) es transferible tal cual.

### 3.2 La metamatemática de ROBINSON = base de la capa `Automata`/`Turing` de DeepArith

DeepArith apunta a `LogicAbstraction/Automata`, `TuringMachine`, `TuringProofs`: **máquinas a
nivel objeto con corrección probada**. ROBINSON ya tiene la plantilla:

- **verificador arithmetizado** `checkProof`/`runFn`/`chainOk` = una máquina verificadora Δ₀/Σ₁
  con **solidez y completitud probadas** (`prf_iff_derivation`, `dem_tracks`).
- **representabilidad** (`repr_pos'`, `substfc`/`tcFn`) = funciones computables representadas y su
  corrección.
- La **Σ₁-completitud provable** (D3, en curso) es el corazón de toda teoría de la computabilidad
  formalizada (es lo que separa «definir una máquina» de «probar internamente qué computa»).

### 3.3 El patrón «Connection» (adecuación object ↔ Lean nativo)

DeepArith separa `Foundation/*/PureAxioms` (object) de `Semantics/*/Connection` (puente a
`Nat`/`List` nativos) y `Computability`. ROBINSON tiene los análogos: `numeral_bridge`,
`Full.numeral`/`Godel.numeral`, `prf_to_derives`, `dem_tracks`. Misma metodología: **construir a
nivel objeto + probar fiel por meta-recursión + transferencia**. Los lemas de transferencia de
ROBINSON son plantilla directa para las `Connection` de DeepArith.

---

## 4 · «Ampliar FOL⁼ hasta DeepArith»: qué subir al kernel

El endgame es promover a `FOL/` (kernel común) las piezas reutilizables que ROBINSON está madurando:

1. **El cálculo de Hilbert finitario `Prf`** + teorema de deducción (`prf_deduction`) + eliminación
   del ∃ (`prf_ex_elim_imp`) + regla de inducción (`Prf.ind`) + eliminadores
   (`prf_nat_induction`, `prf_list_induction`). Un cálculo r.e. (finitario) paralelo al ω-sistema,
   necesario para toda metamatemática (Gödel, computabilidad) y reutilizable por DeepArith.
2. **El toolkit De Bruijn completo** (ya parcialmente en `FOL/Theorems/Eq.lean`): normalizaciones
   `norm11`/`norm21`/`norm32`/`norm_s`, Barendregt, conmutaciones lift/subst.
3. **El toolkit aritmético object** (`<`, `+`, inducción natural, capa numérica de listas).
4. **La metodología de representabilidad** (arithmetización de funciones/predicados + fidelidad).

Con eso, la ε-Inducción + universo $V$ de DeepArith pueden **hospedar una teoría de computabilidad
—y hasta de incompletitud— sobre base más rica**, heredando «gratis» la capacidad inductiva y
metamatemática.

---

## 5 · Roadmap de convergencia (orientativo)

1. **[ROBINSON, en curso]** Cerrar Gödel II real (12-A: capa numérica Δ₀ + Σ₁-completitud provable).
   Esto termina de fabricar el toolkit aritmético/metamatemático a 0-sorry.
2. **[FOL⁼]** Refactorizar las piezas genéricas (§4) hacia `FOL/` como capa reutilizable
   (`FOL/Hilbert`, `FOL/DeBruijn`, `FOL/Arithmetic`).
3. **[DeepArith]** Reescribir `ArithmeticAddProofs`/`Fase 2` usando el toolkit importado (cerrar sus
   `sorry`s), y construir `Fase 3` (representaciones posicionales, división) sobre él.
4. **[DeepArith]** Levantar `Automata`/`Turing` con la plantilla del verificador arithmetizado de
   ROBINSON, y — a largo plazo — una incompletitud sobre el universo $V$.

---

## 6 · En una frase

**ROBINSON fabrica, para Gödel II, el mismo toolkit inductivo/aritmético/metamatemático que
DeepArith necesita para su aritmética y su capa Turing; comparten el kernel FOL⁼, así que el
activo se cosecha una vez. El trabajo de hoy (`prf_nat_induction`, `prf_add_succ_left`, toolkit
`<`) es la primera piedra de ese activo común.**

---

**Autor**: Julián Calderón Almendros · Licencia MIT
