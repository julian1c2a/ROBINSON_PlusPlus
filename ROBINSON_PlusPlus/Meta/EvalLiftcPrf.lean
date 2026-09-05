import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NatOrderPrf
import ROBINSON_PlusPlus.Meta.NumListPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf

/-!
# `Meta/EvalLiftcPrf.lean` — promovido de `sondeos/DescensoLiftc.lean` (rama B2)

Promocion de `sondeos/DescensoLiftc.lean` (2011 lineas, 198 declaraciones) quedandose
**SOLO con lo que falta**. Todo lo demas se CONSUME de produccion.

## Nombre propuesto: `EvalLiftcPrf`

`LiftcCodePrf` ya es «la teoria a nivel de CODIGO de `liftc`/`liftsc`» (vocabulario, axiomas
dotados, las cuatro clausulas del reflector). Lo que aporta ESTE modulo es la EVALUACION:
el descenso bien fundado que cierra `pcc_eval_liftc`. El prefijo `Eval…Prf` es el de
`EvalRunFnPrf`, `EvalNthcPrf`, `EvalPredPrf`, `EvalCarcNthcPrf` — la familia de los
`pcc_eval_*`. `EvalLiftcPrf` lo dice, y ademas ordena el grafo: `EvalLiftcPrf` importa a
`LiftcCodePrf`, nunca al reves.

## ⚠️ POLITICA DE CITAS DE ESTE DOCSTRING (2026‑09‑04)

**A produccion se cita por NOMBRE, nunca por numero de linea.** No es estilo: es lo medido.
Dos auditorias mecanicas seguidas encontraron que **practicamente todas** las citas
`fichero.lean:NNN` de esta cabecera eran falsas a las pocas horas de escribirlas — y las peores
aterrizaban sobre OTRO teorema real del vecindario, que es el modo mas peligroso de fallar:
quien la sigue encuentra codigo plausible y no sospecha. `PrfH_congr_targetLift` se cito como
`:797`, se midio en `:816` y hoy esta en `:821`: tres valores en un dia.

Los numeros que quedan apuntan a **`sondeos/`**, que esta fuera del build y no se toca; aun asi,
van como referencia a la version del sondeo, no como direccion estable.

## Lo que NO se promueve (ya vive en produccion)

De las 198 declaraciones del sondeo se promueven **31**, de las que **23 aterrizan en ESTE
modulo** y 8 se reparten (6 suben aguas arriba, 2 bajan a `LiftcCodePrf`). El reparto, medido
sobre `env.constants` — no sobre el fuente:

* **159** ya estaban en produccion **por nombre** (la tabla de abajo dice donde);
* **8** no se promueven: los **2** duplicados conocidos (`iz_inv`, `eqc_eq_eqCodeFn`, tabla
  siguiente) y los **6** controles de §9 retirados en la auditoria de promocion
  (`tEjA`, `tEjB`, `CRIT_real_A`, `CRIT_real_B`, `CRIT_real_lista` eran instancias de un
  enunciado ya universal en `t`; `CRIT_antecedente_discrimina` era
  `SinWTs.crit_junk_var0_witness1` renombrado);
* **23** se declaran AQUI y **8** en otros modulos (las dos tablas de mas abajo) = **31**;
  mas **6** puentes de consumo (§0) y **5** controles negativos (`example`), que no anaden
  constantes al frente. Este modulo declara **29** nombres: 23 + los 6 puentes.

| bloque del sondeo         | lineas      | ya vive en                                    |
|---------------------------|-------------|-----------------------------------------------|
| §1–§4 vocabulario `liftcT`| 56–168      | `Meta/LiftcCodePrf.lean`                      |
| `targetLift`/`targetLiftsc`| 79, 535    | `Meta/LiftcCodePrf.lean`  ⚠ CRITICO           |
| §4–§6 axiomas dotados     | 180–520     | `Meta/LiftcCodePrf.lean`                      |
| §7 `refl_caso_*`          | 542–672     | `Meta/LiftcCodePrf.lean`                      |
| §9–§10 `refl_*_imp`       | 676–856     | `Meta/LiftcCodePrf.lean` (los CUATRO)         |
| §10 `argsIn`/`isTermCodeE1`| 862–879    | `Minimal/Axioms.lean`, alias `SinWTs` (ADR-020)|
| §C `isTC1` y su fontaneria| 883–1041    | `isTC1` en `Minimal/Axioms.lean`; el resto en `CodeWitnessPrf` |
| §E controles `crit_*`     | 1401–1568   | `Meta/CodeWitnessPrf.lean` (`SinWTs`)         |
| `hasWit`, `CRIT_hasWit_real`| 1386,1964 | `hasWit` en `Minimal/Axioms.lean` (ADR-020); `CRIT_hasWit_real` en `CodeWitnessPrf` (`ENS`) |
| cola del §E + testigo `tcodes1` | 1571–1897 | `Meta/CodeWitnessPrf.lean` (`SinWTs`) ⚠️ el §F del sondeo empieza en la 1899, no aqui |

## ⚠️ LOS DOS DUPLICADOS CONOCIDOS — se BORRAN y se redirigen sus usos

| duplicado del sondeo         | linea | es, byte a byte                                        |
|------------------------------|-------|--------------------------------------------------------|
| `iz_inv`                     | 538   | `EvalRunFnPrf.prf_substtc_termCode_nil` (`nil := zero`) |
| `eqc_eq_eqCodeFn`            | 74    | `Sigma1AtomPrf.eqCodeFn_eq_eqc` con la orientacion dada vuelta |

Ninguno de los dos se usa ya en el residuo promovido: los unicos consumidores de `iz_inv` eran
`refl_caso_*` / `refl_*_imp`, que YA estan en produccion (y alli usan
`prf_substtc_termCode_nil`, ver `Meta/LiftcCodePrf.lean`).

## ⚠️ EL PUNTO CRITICO: `targetLift` ya esta en produccion

`sondeos/DescensoLiftc.lean:79,535` REDEFINE `targetLift`/`targetLiftsc`. Este modulo NO los
redefine: consume los de `Meta/LiftcCodePrf.lean`. Los puentes `:= rfl` de §0 lo
demuestran, y por tanto el descenso CONECTA con el vocabulario ya promovido.

## Lo que este modulo entrega rio abajo

* `pcc_eval_liftc` — el `hLift` sin descargar de `sondeos/Paso2CasoForall.lean:505`.
* `DESCENSO_hasWit` — la forma CONSUMIBLE (testigo bajo un `∃`, contra `ENS.hasWit`).
* **CUATRO lemas GENERICOS** (§2) que no mencionan `targetLift` y que el frente `substfc`
  vuelve a necesitar palabra por palabra: `nilOrCons`, `nilOrCons_at`, `prf_nil_or_cons_all`,
  `prf_nil_or_cons`. Ver la nota del bloque `export`.

⚠️ **SEIS piezas mas se subieron a modulos de aguas ARRIBA, no aqui** — eran genericas y
desde el modulo del descenso quedaban invisibles para los sondeos que las tienen copiadas:

⚠️ **Convencion de la ultima columna**, que la version anterior de esta tabla mezclaba y por
eso tenia TRES de seis cifras mal: se cuentan **ficheros de `sondeos/` que DECLARAN el nombre**
(regex `^(theorem|def|lemma) <nombre>`), **incluido `DescensoLiftc`**, que es el que se promueve.
Entre parentesis, las **declaraciones**, que no coinciden porque algun sondeo lo declara dos veces.

| pieza                              | ahora vive en                         | declarada en |
|------------------------------------|---------------------------------------|--------------|
| `psi_lift_form` (generico en `Φ`)  | `Meta/StrongInductionPrf.lean`        | 5 sondeos (5) |
| `PSI_inst` (generico en `Φ`)       | `Meta/StrongInductionPrf.lean`        | **8 sondeos (10)** |
| `prf_argsIn_head`                  | `Meta/CodeWitnessPrf.lean` (`SinWTs`) | 5 sondeos (5) |
| `prf_argsIn_tail`                  | `Meta/CodeWitnessPrf.lean` (`SinWTs`) | 6 sondeos (8) |
| `prf_isTermCodeE1_of_boundedIn`    | `Meta/CodeWitnessPrf.lean` (`SinWTs`) | 6 sondeos (8) |
| `prf_isTermCodeE1_of_In`           | `Meta/CodeWitnessPrf.lean` (`SinWTs`) | 6 sondeos (8) |

⚠️ **Y DOS BAJARON a `Meta/LiftcCodePrf.lean`**: `substF_targetLift` y `substF_targetLiftsc`.
No podian quedarse aqui como generales con el particular arriba —seria un CICLO, porque este
modulo lo importa—, asi que bajaron ellos y alli `substF_targetLift_hole` quedo reescrito
como su corolario. Es la restriccion que manda en esta rama.

## ⚠️ LA LISTA DE `import` CONCRETA DEL MODULO REAL (20; ninguno es el barrel)

El borrador de `Probe/` llevaba `import ROBINSON_PlusPlus.Meta` porque ahi SI vale. **Este**
modulo lleva estos 20, **cada uno justificado por el simbolo que lo pide**:

| import (`ROBINSON_PlusPlus.Meta.…`) | simbolo que lo exige                                    |
|-------------------------------------|---------------------------------------------------------|
| `ArithPrf`        | `prf_eq_symm`, `prf_eq_trans`, `prf_refl`                            |
| `BoundedInPrf`    | `PrfH_lt_subst2` (§6). ⚠️ `boundedIn` y `prf_boundedIn_of_In` se los llevaron los lemas de §4 al bajar, pero el import SE QUEDA |
| `CantorMonoPrf`   | `prf_cantor_mono_left` / `_right` — el descenso de Cantor (§6)        |
| `ChainPrf`        | `prf_list_induction` (§2), `PrfH_leibniz_subst`, `PrfH_and_*`, `PrfH_or_elim`, `PrfH_spec` |
| `CodeWitnessPrf`  | `SinWTs` (`tcodes1`, `crit_*`, y por alias `isTC1`/`wfAll1`/`argsIn`/`isTermCodeE1`) y `ENS` (`liftF_isTC1`, `substF_isTC1`, `substF_wfAll1`, `CRIT_hasWit_real`, y por alias `hasWit`). ⚠️ Los predicados de guarda se DECLARAN en `Minimal/Axioms.lean` desde ADR-020 |
| `DerivCondPrf`    | `liftTerm_termCode`, `liftTerm_strCode`, `substTerm_strCode` (§1)     |
| `EvalRunFnPrf`    | `prf_substtc_termCode_nil` — SOLO para el puente anti‑`iz_inv` de §0  |
| `Hilbert`         | `Prf`, `PrfH`, `Prf₀.p1`/`j1`/`j2`, `Prf.gen`, `Prf.qconf`            |
| `HilbertDeduction`| `prf_deduction`, `deduction_aux`, `prf_to_prfH`, `prfH_nil_to_prf`, `prf_ex_elim_imp` |
| `LiftcCodePrf`    | ⚠️ **EL IMPORT CENTRAL**: `targetLift`, `targetLiftsc`, `liftcT`, `liftscT`, `refl_shapeUn_imp`, `refl_shapeBin_imp`, `refl_lista_nil`, `refl_lista_cons_imp`, `substTerm_termCode`, `prf_substtc_termCode_zero` |
| `NatArithPrf`     | `prf_zero_lt_succ`, `prf_succ_lt_succ_of_lt` (§3, §6)                 |
| `NatOrderPrf`     | `prf_lt_trans` — la cadena `b < … < X` de §6                          |
| `NumListPrf`      | `prf_lenc_cons`, `prf_nthc_zero`, `prf_nthc_succ` (§3, §6)            |
| `Provability`     | `termCode`                                                            |
| `ReprPrf`         | `prf_mp`, `prf_spec`, `prf_and_intro`, `prf_and_elim_left`, `prf_carc_cons` |
| `Sigma1AtomPrf`   | `eqCodeFn`, `eqCodeFn_eq_eqc` — SOLO para el puente anti‑`eqc_eq_eqCodeFn` de §0 |
| `Sigma1CorePrf`   | `objList` (§9)                                                        |
| `Sigma1Prf`       | `provFromCode`                                                        |
| `StrongInductionPrf` | `PSI`, `prf_strong_induction` — el motor del descenso (§5, §7)     |
| `TrackedCorePrf`  | `liftFormula_provFromCode_open`, `substFormula_provFromCode_open` (§1) |

⚠️ **MEDIDO, y es la trampa registrada de la auditoria de footprint**: un leave‑one‑out sobre
los 20 `import` da **19 «redundantes»** — todos son alcanzables TRANSITIVAMENTE desde
`LiftcCodePrf` (que importa `CodeWitnessPrf`, que importa casi todo). Con solo
`import ROBINSON_PlusPlus.Meta.LiftcCodePrf` el fichero compila igual. Eso es un FALSO
NEGATIVO del crawler, no una prueba de que sobren: la lista de arriba es la de dependencias
DIRECTAS, y es la que protege ante un refactor aguas arriba. Es la misma convencion que sigue
`Meta/LiftcCodePrf.lean` (25 `import`, la mayoria transitivamente implicados).

Si el orquestador decide BORRAR los dos puentes anti‑duplicado de §0 (son controles, no
resultados), caen con ellos `EvalRunFnPrf` y `Sigma1AtomPrf`: quedan 18.
-/

/-! ⚠️ `open` YA PODADO: el sondeo abria **35** namespaces; este modulo necesita **22** — los 20
    de abajo, mas `CodeWitnessPrf.SinWTs` entero y `CodeWitnessPrf.ENS` selectivo.
    Cada linea esta cubierta por su `import` homonimo de la cabecera.

    ⚠️ `open ROBINSON_PlusPlus.Minimal.Axioms` en CABECERA: aqui **no muerde**. La trampa
    (`<=`/`<` resolviendo al orden OBJETO) solo se dispara donde se ELABORA un `<` de `Nat`;
    el unico sitio con aritmetica `Nat` es `CRIT_targetLiftsc_real`, y alli el `k < ts.length`
    llega YA ELABORADO en la signatura de `SinWTs.prf_argsIn_of_closed`. -/
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.EvalRunFnPrf

/-! ⚠️ `SinWTs` entero: es de donde sale TODO el vocabulario del testigo (`isTC1`, `wfAll1`,
    `argsIn`, `isTermCodeE1`, `consOk`, `tcodes1`, los `crit_*`). Su `prf_congr_liftc` es
    AMBIGUO con `NumCodeClosedPrf.prf_congr_liftc`, pero este modulo NO usa ese nombre
    (la ambiguedad de `open` en Lean 4 es perezosa: solo rompe en el punto de uso).

    ⚠️ De `ENS`, en cambio, `open` **SELECTIVO**: `ENS` reprueba `liftF_argsIn`,
    `substF_argsIn`, `liftF_isTermCodeE1`, `substF_isTermCodeE1` y `liftF_wfAll1`, que ya
    estan en `SinWTs`; abrirlo entero los volveria ambiguos, y este modulo los usa todos. -/
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS
  (hasWit liftF_isTC1 substF_isTC1 substF_wfAll1 liftF_hasWit substF_hasWit CRIT_hasWit_real)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace ROBINSON_PlusPlus.Meta.EvalLiftcPrf

/-! ## §0 · PUENTES DE CONSUMO — `net-0`; **cinco por `rfl` y uno por `.symm`**

    Estos cuatro `rfl` son la MEDIDA de que este modulo consume el vocabulario de produccion
    y no fabrica constantes nuevas. Si alguno dejara de ser `rfl`, el descenso estaria
    hablando de otro objetivo y NO conectaria con `Meta/LiftcCodePrf.lean`. -/

/-- `LiftcCodePrf.targetLift` es, byte a byte, el `targetLift` de `sondeos/DescensoLiftc.lean:79`. -/
theorem targetLift_es_el_del_sondeo (s : Term) :
    targetLift s = provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))) :=
  rfl

/-- `LiftcCodePrf.targetLiftsc` es el `targetLiftsc` de `sondeos/DescensoLiftc.lean:535`. -/
theorem targetLiftsc_es_el_del_sondeo (b : Term) :
    targetLiftsc b
      = provFromCode (eqc (liftscT (termCode zero) (tcFn b)) (tcFn (liftsc zero b))) :=
  rfl

/-- `ENS.hasWit` es el `hasWit` de `sondeos/DescensoLiftc.lean:1386`. -/
theorem hasWit_es_el_del_sondeo (c : Term) :
    hasWit c = Formula.ex (isTC1 (.var 0) (liftTerm 0 c)) := rfl

/-- `SinWTs.isTC1` es el `isTC1` de `sondeos/DescensoLiftc.lean:899`. -/
theorem isTC1_es_el_del_sondeo (w c : Term) : isTC1 w c = land (wfAll1 w) (In c w) := rfl

/-- **El duplicado `iz_inv` (`sondeos/DescensoLiftc.lean:538`) NO se promueve**: es
    `EvalRunFnPrf.prf_substtc_termCode_nil`, porque `nil := zero` (`Minimal/Axioms.lean:126`)
    y por tanto `termCode nil` y `termCode zero` son EL MISMO termino.

    ⚠️ El puente se enuncia como igualdad de PROPOSICIONES, no como `rfl` entre las dos
    pruebas: `Prf` es un `Prop`, asi que un `rfl` entre pruebas lo daria la irrelevancia
    y no mediria nada. Asi enunciado, el `rfl` dice EXACTAMENTE lo que hay que decir: los
    dos ENUNCIADOS son el mismo. -/
theorem iz_inv_es_prf_substtc_termCode_nil (W : Term) :
    Prf (substtc zero W (termCode zero) =eq termCode zero)
      = Prf (substtc zero W (termCode nil) =eq termCode nil) := rfl

/-- Y los dos habitantes existen ya en produccion, uno por cada cara del mismo enunciado. -/
example (W : Term) : Prf (substtc zero W (termCode nil) =eq termCode nil) :=
  ROBINSON_PlusPlus.Meta.CodeCtorKit.prf_substtc_termCode_zero 0 W
example (W : Term) : Prf (substtc zero W (termCode zero) =eq termCode zero) :=
  ROBINSON_PlusPlus.Meta.EvalRunFnPrf.prf_substtc_termCode_nil W

/-- **El duplicado `eqc_eq_eqCodeFn` (`:74`) tampoco**: es `Sigma1AtomPrf.eqCodeFn_eq_eqc`
    con la orientacion invertida. -/
theorem eqc_eq_eqCodeFn_es_symm (a b : Term) : eqc a b = eqCodeFn a b :=
  (eqCodeFn_eq_eqc a b).symm

/-! ## §1 · `liftFormula`/`substFormula` atraviesan los dos objetivos

    El cuerpo Σ₁ de `provFromCode` es cerrado; el unico hueco es el codigo. -/

theorem liftF_targetLift (k : Nat) (s : Term) :
    liftFormula k (targetLift s) = targetLift (liftTerm k s) := by
  simp only [targetLift, liftFormula_provFromCode_open, eqc, liftcT, funcc, tcFn, liftc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_termCode, liftTerm_strCode]

theorem liftF_targetLiftsc (k : Nat) (s : Term) :
    liftFormula k (targetLiftsc s) = targetLiftsc (liftTerm k s) := by
  simp only [targetLiftsc, liftFormula_provFromCode_open, eqc, liftscT, funcc, tcFn, liftsc,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_termCode, liftTerm_strCode]

-- ⚠️ `substF_targetLift` y `substF_targetLiftsc` NO se declaran aqui: **BAJARON** a
--    `Meta/LiftcCodePrf.lean`, junto a `substF_targetLift_hole`, que es su caso
--    `v := 0`, `s := #0` y que alli quedo reescrito como corolario suyo.
--    Razon: este modulo IMPORTA a `LiftcCodePrf`, asi que el corolario no podia ir al reves
--    sin ciclo — y el `_hole` tiene tres consumidores dentro de aquel fichero.
--    Los usos de abajo —en `PrfH_congr_targetLiftsc`, `PHI_at` y `PHI_use`— resuelven por
--    el `open ...LiftcCodePrf` de la cabecera. (Por NOMBRE, no por linea: los numeros que
--    habia aqui eran falsos, copiados de un parche previo al fichero actual.)

/-- Leibniz sobre el argumento de `targetLiftsc`. (La companera `PrfH_congr_targetLift` ya
    esta en produccion, en `Meta/LiftcCodePrf.lean`.) -/
theorem PrfH_congr_targetLiftsc {Γ : List Formula} {s s' : Term} (h : PrfH Γ (s =eq s'))
    (ha : PrfH Γ (targetLiftsc s)) : PrfH Γ (targetLiftsc s') := by
  have hS : ∀ u : Term, substFormula 0 u (targetLiftsc (.var 0)) = targetLiftsc u := by
    intro u
    rw [substF_targetLiftsc]
    simp only [substTerm, if_true]
  exact (hS s') ▸ PrfH_leibniz_subst (A := targetLiftsc (.var 0)) h ((hS s) ▸ ha)

/-! ## §2 · LA ESTRUCTURA: `⊢ Y ≐ nil ∨ Y ≐ cons (carc Y) (cdrc Y)` para `Y` ARBITRARIO

    Es lo que `argsIn` (POSICIONAL) no da, y lo unico que la induccion fuerte no puede
    fabricar (ordena valores, no descompone). Sale de `prf_list_induction` con un paso que
    **no usa la hipotesis de induccion**: `prf_consOk_cons` a secas. -/

def nilOrCons : Formula := lor (Formula.eq (.var 0) nil) (consOk (.var 0))

theorem nilOrCons_at (Y : Term) :
    substFormula 0 Y nilOrCons = lor (Formula.eq Y nil) (consOk Y) := by
  simp only [nilOrCons, consOk, lor, carc, cdrc, cons, nil, zero, substFormula, substTerm,
    substTerms, if_true]

theorem prf_nil_or_cons_all : Prf (Formula.forall nilOrCons) := by
  refine prf_list_induction nilOrCons ?base ?step
  · rw [nilOrCons_at]
    exact prf_orL (prf_refl nil)
  · refine Prf.gen _ (Prf.gen _ ?_)
    have hR : substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 nilOrCons))
        = lor (Formula.eq (cons (.var 1) (.var 0)) nil) (consOk (cons (.var 1) (.var 0))) := by
      simp only [nilOrCons, consOk, lor, carc, cdrc, cons, nil, zero, liftFormula, substFormula,
        liftTerm, liftTerms, substTerm, substTerms, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT,
        reduceIte, if_true]
    rw [hR]
    exact prf_mp (Prf.incl (Prf₀.p1 _ _)) (prf_orR (prf_consOk_cons _ _))

/-- **`⊢ Y ≐ nil ∨ consOk Y`** con `Y` **abstracto** (puede ser `#0`). -/
theorem prf_nil_or_cons (Y : Term) : Prf (lor (Formula.eq Y nil) (consOk Y)) := by
  have h := prf_spec prf_nil_or_cons_all Y
  rwa [nilOrCons_at] at h

/-! ## §3 · `argsIn` se parte en CABEZA y COLA

    ⚠️ **`prf_argsIn_head` y `prf_argsIn_tail` NO viven aqui.** Son genericos —no mencionan
    `targetLift`— y al promover se bajaron a `Meta/CodeWitnessPrf.lean` (`SinWTs`, :680 y
    :692), junto a `PrfH_inst_argsIn`, que es de quien salen.

    Razon: `prf_argsIn_tail` esta copiado a mano en SEIS sondeos del frente y
    `prf_argsIn_head` en CINCO — `EvalSubsttc` copia solo la cola — (`DescensoLiftc`,
    `EvalSubstfcPrf`, `SubstfcEx`, …). Dejandolos en el modulo del DESCENSO quedaban
    invisibles para todos ellos, que es justo el problema que esta promocion venia a
    resolver. Se consumen desde aqui via `open …CodeWitnessPrf.SinWTs`. -/
/-! ## §4 · Del testigo al NODO

    ⚠️ **`prf_isTermCodeE1_of_boundedIn` y `prf_isTermCodeE1_of_In` NO viven aqui.** Son
    genericos —no mencionan `targetLift`— y se BAJARON a `Meta/CodeWitnessPrf.lean`
    (`SinWTs`), junto a `prf_argsIn_head`/`_tail` y a `PrfH_inst_wfAll1`, que es de quien
    salen. Alli son el analogo por sort de `ENS.prf_isFormCodeE2_of_boundedIn`/`_of_In`,
    con el esqueleto de prueba identico linea a linea.

    Se consumen desde aqui via `open …CodeWitnessPrf.SinWTs` — y el `impT` deja de necesitar
    cualificacion, porque dentro de `SinWTs` el nombre a secas ya es el correcto. -/

/-! ## §5 · EL PREDICADO DE LA INDUCCION FUERTE — las DOS mitades a la vez

    🔑 **LA LECCION DE DISENO**: NO son dos inducciones mutuas, sino UNA induccion fuerte con
    conclusion **CONJUNTIVA** sobre los dos sorts, y con `w` cuantificado **DENTRO** de `Φ`.

        Φ(X) := ∀w. ( isTC1 w X                ⇒ targetLift   X )
                   ∧ ( (wfAll1 w ∧ argsIn w X) ⇒ targetLiftsc X )

    `w` va **cuantificado dentro** porque lo exige el gate `hΦ : liftFormula 1 Φ = Φ` de
    `prf_strong_induction`: con `w` libre haria falta `liftTerm 1 w = w`, que no se descarga.
    `#1` es el codigo sobre el que se induce. -/

def PHIbody : Formula :=
  land (Formula.impl (isTC1 (.var 0) (.var 1)) (targetLift (.var 1)))
       (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
         (targetLiftsc (.var 1)))

def PHI : Formula := Formula.forall PHIbody

theorem hPHI : liftFormula 1 PHI = PHI := by
  simp only [PHI, PHIbody, land, liftFormula, liftF_isTC1, liftF_wfAll1, liftF_argsIn,
    liftF_targetLift, liftF_targetLiftsc, liftTerm, Nat.reduceAdd, Nat.reduceLT, reduceIte]

theorem PHI_at (t : Term) :
    substFormula 0 t PHI = Formula.forall (
      land (Formula.impl (isTC1 (.var 0) (liftTerm 0 t)) (targetLift (liftTerm 0 t)))
           (Formula.impl (land (wfAll1 (.var 0)) (argsIn (.var 0) (liftTerm 0 t)))
             (targetLiftsc (liftTerm 0 t)))) := by
  simp only [PHI, PHIbody, land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetLift, substF_targetLiftsc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

/-- Instanciacion de las dos mitades a un testigo `w` concreto. -/
theorem PHI_use {Γ : List Formula} (t w : Term) (h : PrfH Γ (substFormula 0 t PHI)) :
    PrfH Γ (land (Formula.impl (isTC1 w t) (targetLift t))
                 (Formula.impl (land (wfAll1 w) (argsIn w t)) (targetLiftsc t))) := by
  rw [PHI_at] at h
  have hs := PrfH_spec h w
  simpa only [land, substFormula, substF_isTC1, substF_wfAll1, substF_argsIn,
    substF_targetLift, substF_targetLiftsc, substTerm, FOL.substTerm_liftTerm, if_true] using hs

/-! ⚠️ **`psi_lift_form` y `PSI_inst` NO viven aqui.** El sondeo los tenia instanciados a
    `Φ := PHI`, pero son maquinaria GENERICA de la induccion fuerte: `psi_lift_form` sale en
    dos lineas de `psi_lift_eq_subst` + `psi_at`, y `PSI_inst` es la version `PrfH` de
    `prf_psi_elim`. Al promover se subieron **genericos en `Φ`** a
    `Meta/StrongInductionPrf.lean:195,203`, junto a sus padres.

    No es cosmetica: `PSI_inst` esta copiado a mano en **OCHO** sondeos, con **DIEZ**
    declaraciones (`EvalSubstfcPrf` ×2, `HasWitFReal` ×2, `EvalSubsttc`, `EnsamblajeMedida`,
    `EnsamblajeTriple`, `Paso2Guardado`, `SubstfcEx`, `DescensoLiftc`), y `psi_lift_form` en
    **cinco**. Dejandolos aqui, instanciados a `PHI`, seguirian invisibles para todos ellos.

    Uso local: `PSI_inst PHI hPHI hpsi z`. -/

/-! ## §6 · EL PASO DE LA INDUCCION FUERTE

    El descenso de Cantor vale para las dos mitades: `carc` y `cdrc` de un `cons` son ambos
    ESTRICTAMENTE menores (`prf_cantor_mono_left/right`). -/

theorem PHI_step : Prf (Formula.forall (Formula.impl (PSI PHI) PHI)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHI] PHIbody ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH_and_intro ?half1 ?half2
  case half1 =>
    -- `X = #1`, `w = #0`; hipotesis: `isTC1 w X`
    refine deduction_aux ?_ (isTC1 (.var 0) (.var 1)) [liftFormula 0 (PSI PHI)] rfl
    have hh : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (isTC1 (.var 0) (.var 1)) := PrfH.hyp _ _ (List.Mem.head _)
    have hpsi : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (liftFormula 0 (PSI PHI)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    have hwf : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (wfAll1 (.var 0)) := PrfH_and_elim_left hh
    have hin : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (In (.var 1) (.var 0)) := PrfH_and_elim_right hh
    have hitc : PrfH [isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
        (isTermCodeE1 (.var 0) (.var 1)) :=
      PrfH.mp _ _ _ (PrfH.mp _ _ _
        (prf_to_prfH (prf_isTermCodeE1_of_In (.var 0) (.var 1)) _) hin) hwf
    refine PrfH_or_elim hitc ?varc ?func
    case varc =>
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeUn_imp (.var 1)) _)
        (PrfH.hyp _ _ (List.Mem.head _))
    case func =>
      have hb : PrfH [land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)]
          (land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hwf' : PrfH [land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)] (wfAll1 (.var 0)) :=
        PrfH_and_elim_left (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))
      have hpsi' : PrfH [land (shapeBin (.var 1) 1) (argsIn (.var 0) (nthc (.var 1) (numeralM 2))),
          isTC1 (.var 0) (.var 1), liftFormula 0 (PSI PHI)] (liftFormula 0 (PSI PHI)) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hshape := PrfH_and_elim_left hb
      have hargs := PrfH_and_elim_right hb
      -- `b < X`: `b < cons b nil < cons p (cons b nil) < cons 1̄ (…) = X` (Cantor)
      have h1 : Prf (lt (nthc (.var 1) (numeralM 2)) (cons (nthc (.var 1) (numeralM 2)) nil)) :=
        prf_cantor_mono_left _ _
      have h2 : Prf (lt (cons (nthc (.var 1) (numeralM 2)) nil)
          (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil))) :=
        prf_cantor_mono_right _ _
      have h3 : Prf (lt (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil))
          (cons (numeralM 1)
            (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil)))) :=
        prf_cantor_mono_right _ _
      have h12 : Prf (lt (nthc (.var 1) (numeralM 2))
          (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h1) h2
      have h123 : Prf (lt (nthc (.var 1) (numeralM 2))
          (cons (numeralM 1)
            (cons (nthc (.var 1) (numeralM 1)) (cons (nthc (.var 1) (numeralM 2)) nil)))) :=
        prf_mp (prf_mp (prf_lt_trans _ _ _) h12) h3
      have hltb := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hshape) (prf_to_prfH h123 _)
      have hphi := PrfH.mp _ _ _ (PSI_inst PHI hPHI hpsi' (nthc (.var 1) (numeralM 2))) hltb
      have huse := PHI_use (nthc (.var 1) (numeralM 2)) (.var 0) hphi
      have htls := PrfH.mp _ _ _ (PrfH_and_elim_right huse) (PrfH_and_intro hwf' hargs)
      exact PrfH.mp _ _ _ (prf_to_prfH (refl_shapeBin_imp (.var 1)) _)
        (PrfH_and_intro hshape htls)
  case half2 =>
    refine deduction_aux ?_ (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)))
      [liftFormula 0 (PSI PHI)] rfl
    have hh : PrfH [land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
        (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1))) := PrfH.hyp _ _ (List.Mem.head _)
    refine PrfH_or_elim (prf_to_prfH (prf_nil_or_cons (.var 1)) _) ?nilc ?consc
    case nilc =>
      have heq : PrfH [Formula.eq (.var 1) nil,
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (Formula.eq (.var 1) nil) := PrfH.hyp _ _ (List.Mem.head _)
      exact PrfH_congr_targetLiftsc (PrfH_eq_symm heq) (prf_to_prfH refl_lista_nil _)
    case consc =>
      have hcons : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (Formula.eq (.var 1) (cons (carc (.var 1)) (cdrc (.var 1)))) :=
        PrfH.hyp _ _ (List.Mem.head _)
      have hh' : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1))) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
      have hpsi : PrfH [consOk (.var 1),
          land (wfAll1 (.var 0)) (argsIn (.var 0) (.var 1)), liftFormula 0 (PSI PHI)]
          (liftFormula 0 (PSI PHI)) :=
        PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      have hwf := PrfH_and_elim_left hh'
      have hargs := PrfH_and_elim_right hh'
      -- (a) la CABEZA esta en el testigo y es MENOR ⟹ `targetLift (carc X)` por la HI
      have hlenX := PrfH_eq_trans (PrfH_congr_lenc hcons)
        (prf_to_prfH (prf_lenc_cons (carc (.var 1)) (cdrc (.var 1))) _)
      have hzlt := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
        (PrfH_eq_symm hlenX) (prf_to_prfH (prf_zero_lt_succ (lenc (cdrc (.var 1)))) _)
      have hin0 := PrfH.mp _ _ _
        (PrfH_inst_argsIn (.var 0) (.var 1) zero hargs) hzlt
      have hnth0 := PrfH_eq_trans (PrfH_congr_nthc_lst zero hcons)
        (prf_to_prfH (prf_nthc_zero (carc (.var 1)) (cdrc (.var 1))) _)
      have hinhd := PrfH_congr_In_left hnth0 hin0
      have hlthd := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_left (carc (.var 1)) (cdrc (.var 1))) _)
      have huse_hd := PHI_use (carc (.var 1)) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst PHI hPHI hpsi (carc (.var 1))) hlthd)
      have hTL_hd := PrfH.mp _ _ _ (PrfH_and_elim_left huse_hd) (PrfH_and_intro hwf hinhd)
      -- (b) la COLA hereda `argsIn` y es MENOR ⟹ `targetLiftsc (cdrc X)` por la HI
      have hargs_cons := PrfH_congr_argsIn hcons hargs
      have hargs_tl := PrfH.mp _ _ _
        (prf_to_prfH (prf_argsIn_tail (.var 0) (carc (.var 1)) (cdrc (.var 1))) _) hargs_cons
      have hlttl := ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hcons)
        (prf_to_prfH (prf_cantor_mono_right (carc (.var 1)) (cdrc (.var 1))) _)
      have huse_tl := PHI_use (cdrc (.var 1)) (.var 0)
        (PrfH.mp _ _ _ (PSI_inst PHI hPHI hpsi (cdrc (.var 1))) hlttl)
      have hTLs_tl := PrfH.mp _ _ _ (PrfH_and_elim_right huse_tl) (PrfH_and_intro hwf hargs_tl)
      -- (c) el paso `cons` del reflector, y vuelta a `X` por Leibniz
      have hres := PrfH.mp _ _ _
        (prf_to_prfH (refl_lista_cons_imp (carc (.var 1)) (cdrc (.var 1))) _)
        (PrfH_and_intro hTL_hd hTLs_tl)
      exact PrfH_congr_targetLiftsc (PrfH_eq_symm hcons) hres

/-! ## §7 · EL DESCENSO -/

theorem PHI_all (t : Term) : Prf (substFormula 0 t PHI) :=
  prf_strong_induction PHI hPHI PHI_step t

/-- **EL DESCENSO, en forma de IMPLICACION OBJETO**, con `w` y `s` **ABSTRACTOS**. -/
theorem DESCENSO_imp (w s : Term) : Prf (Formula.impl (isTC1 w s) (targetLift s)) :=
  prfH_nil_to_prf (PrfH_and_elim_left (PHI_use s w (prf_to_prfH (PHI_all s) []))) rfl

/-- Su gemela sobre LISTAS de argumentos. -/
theorem DESCENSO_lista_imp (w s : Term) :
    Prf (Formula.impl (land (wfAll1 w) (argsIn w s)) (targetLiftsc s)) :=
  prfH_nil_to_prf (PrfH_and_elim_right (PHI_use s w (prf_to_prfH (PHI_all s) []))) rfl

/-- **DESCENSO** (la forma pedida). -/
theorem DESCENSO (w s : Term) (h : Prf (isTC1 w s)) : Prf (targetLift s) :=
  prf_mp (DESCENSO_imp w s) h

theorem DESCENSO_lista (w s : Term) (hwf : Prf (wfAll1 w)) (hargs : Prf (argsIn w s)) :
    Prf (targetLiftsc s) :=
  prf_mp (DESCENSO_lista_imp w s) (prf_and_intro hwf hargs)

/-- **`pcc_eval_liftc`** — el `hLift` de `sondeos/Paso2CasoForall.lean:505`, LITERAL.
    Es EL MISMO teorema que `DESCENSO`, con el objetivo desplegado. -/
theorem pcc_eval_liftc (w s : Term) (h : Prf (isTC1 w s)) :
    Prf (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s)))) :=
  DESCENSO w s h

/-! ## §8 · La forma que de verdad llega rio abajo: el testigo viene de un `∃`.

    `hasWit` es el de produccion: se declara en `Minimal/Axioms.lean` (ADR-020) y
    `CodeWitnessPrf.ENS` lo re-exporta. Aqui NO se redefine. -/

theorem DESCENSO_hasWit (s : Term) : Prf (Formula.impl (hasWit s) (targetLift s)) := by
  refine prf_ex_elim_imp ?_
  rw [liftF_targetLift]
  exact PrfH.mp _ _ _ (prf_to_prfH (DESCENSO_imp (.var 0) (liftTerm 0 s)) _) (prfH_hyp_self _)

/-! ############################################################################
    ## §9 · CONTROLES ADVERSARIALES SOBRE EL DESCENSO

    Los `crit_*` de base (`crit_junk_var0_witness1`, `prf_isTC1_tcodes`, `tcodes1`, …) ya
    estan en produccion (`Meta/CodeWitnessPrf.lean`, `SinWTs`). Aqui solo se APLICAN al
    DESCENSO.

    ⚠️⚠️ **QUE MIDEN Y QUE NO — leer antes de citarlos.**

    Estos controles **NO** prueban que el enunciado sea alcanzable: eso ya lo tenia
    produccion **sin ningun descenso**, componiendo `LiftcCodePrf.refl_termCode` /
    `refl_termsCode` (:752, :757) con los puentes `Representability.termCodeM_eq` /
    `termsCodeM_eq` (:158, :161). Medido y compilado en la auditoria de promocion.

    Lo que SI miden, y es lo que se quiere: que **el DESCENSO DISPARA** — que el
    antecedente `isTC1 W ⌜t⌝` es demostrable con testigo explicito y computable, de modo
    que `DESCENSO` no es un `⊥ ⇒ …` disfrazado. La ruta importa: `refl_termCode` va por
    recursion META sobre la estructura del termino y **no ejercita la induccion objeto**;
    estos van por `DESCENSO (objList (tcodes1 t)) …`, que es justamente lo que hay que medir.

    Por eso se conservan TRES y se retiraron SEIS (`CRIT_real_A`, `CRIT_real_B`,
    `CRIT_real_lista` eran instancias de un enunciado ya universal en `t`; sus datos `tEjA`
    y `tEjB`, con ellas; y `CRIT_antecedente_discrimina` era `SinWTs.crit_junk_var0_witness1`
    renombrado — usese el de produccion directamente).
    ############################################################################ -/

/-- **EL DESCENSO DISPARA (1)** — sort TERMINO. Para **todo** termino REAL `t`, abierto
    incluido, el antecedente `isTC1 W ⌜t⌝` es demostrable con testigo explicito, luego el
    DESCENSO entrega el `hLift` de `paso2_caso_forall` (`sondeos/Paso2CasoForall.lean:505`;
    el consumidor en produccion es `pcc_eval_liftc`).

    ⚠️ El ENUNCIADO no es informacion nueva (ver la cabecera de §9): lo nuevo es la RUTA. -/
theorem CRIT_targetLift_real (t : Term) : Prf (targetLift (termCodeM t)) :=
  DESCENSO (objList (tcodes1 t)) (termCodeM t) (prf_isTC1_tcodes t)

/-- **EL DESCENSO DISPARA (2)** — sort LISTA: sobre la lista de argumentos REAL de un
    `funcc` (el testigo es el mismo del termino entero, `tcodes1`).

    ⚠️ El simbolo de funcion es INTERNO y fijo (`add_sym`, de `Minimal/Axioms.lean`): no
    aparece en la conclusion, asi que exponerlo como parametro `(f : String)` — como hacia
    el sondeo — solo aparentaba generalidad. Cero simbolos de funcion objeto nuevos. -/
theorem CRIT_targetLiftsc_real (ts : List Term) :
    Prf (targetLiftsc (termsCodeM ts)) := by
  have h := prf_isTC1_tcodes (Term.func add_sym ts)
  refine DESCENSO_lista (objList (tcodes1 (Term.func add_sym ts))) _ (prf_and_elim_left h) ?_
  refine prf_argsIn_of_closed _ (termsCodeM ts) ts.length
    (liftTerm_objList 0 _ (fun x hx => (closed_mem_tcodes1 _ x hx).1 0))
    (liftTerm_termsCodeM 0 ts)
    (fun v s => substTerm_objList v s _ (fun x hx => (closed_mem_tcodes1 _ x hx).2 v s))
    (fun v s => substTerm_termsCodeM v s ts)
    (prf_lenc_termsCodeM ts) ?_
  intro k hk
  obtain ⟨u, hu⟩ : ∃ u, ts[k]? = some u := ⟨ts[k], getElem?_pos ts k hk⟩
  refine prf_congr_In_left (prf_eq_symm (prf_nthc_termsCodeM ts k u hu)) ?_
  refine prf_In_objList _ (termCodeM u) ?_
  simp only [tcodes1]
  exact List.Mem.tail _ (mem_tcodes1s_of_mem ts u (mem_of_getElem? ts k u hu))

-- ⚠️ RETIRADO `CRIT_antecedente_discrimina`: era `SinWTs.crit_junk_var0_witness1`
--    (en `Meta/CodeWitnessPrf.lean`) renombrado — el sondeo lo definia literalmente como
--    `crit_junk_var0_witness1 hjunk`. El lado contrario de la no-vacuidad (que `isTC1` es
--    REFUTABLE con el codigo de una FORMULA y testigo ARBITRARIO, luego el DESCENSO no es
--    un `⊥ ⇒ …` disfrazado) lo da ESE lema de produccion, directamente.

/-- **EL DESCENSO DISPARA (3)** — la SEGUNDA RUTA, con testigo EXISTENCIAL: todo termino
    real tiene testigo (`ENS.CRIT_hasWit_real`, ya en produccion) y el descenso lo consume.

    ⚠️ Su TIPO es identico al de `CRIT_targetLift_real`: no es un segundo teorema, son dos
    RUTAS al mismo enunciado — una con el testigo explicito `objList (tcodes1 t)`, la otra
    bajo el `∃` de `hasWit`. Se conservan las dos a proposito, porque la que ejercita
    `DESCENSO_hasWit` es esta, y `DESCENSO_hasWit` es la forma consumible rio abajo. -/
theorem CRIT_hasWit_descenso (t : Term) : Prf (targetLift (termCodeM t)) :=
  prf_mp (DESCENSO_hasWit (termCodeM t)) (CRIT_hasWit_real t)

/-! ### CONTROLES NEGATIVOS: los enunciados no son reflexividades disfrazadas -/

example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftcT (termCode zero) (tcFn s) = tcFn (liftc zero s))
  trivial

example (s : Term) : True := by
  fail_if_success
    exact (rfl : liftscT (termCode zero) (tcFn s) = tcFn (liftsc zero s))
  trivial

/-- El predicado de la induccion NO es trivial: `PHI` no es `⊤` ni se reduce a la conclusion. -/
example : True := by
  fail_if_success exact (rfl : PHIbody = targetLift (.var 1))
  trivial

end ROBINSON_PlusPlus.Meta.EvalLiftcPrf

/-! ## AI-GUIDE §17 · bloque `export` del modulo

    ⚠️⚠️ **EL `export` ES DELIBERADAMENTE PARCIAL, Y ESTO ES UN HALLAZGO, NO UN OLVIDO.**

    `sondeos/EvalSubstfcPrf.lean` (el frente `substfc`, ya PROBADO, la promocion siguiente)
    monta **otros DOS descensos** con los MISMOS nombres genericos y predicados DISTINTOS:

    | nombre     | aqui (`liftc`)      | `EvalSubstfcPrf.lean:5618` (`substtc`) | `:6302` (`substfc`) |
    |------------|---------------------|----------------------------------------|---------------------|
    | `PHI`      | 1 binder            | 3 binders (`CONJ`)                     | 5 binders (`BODY`)  |
    | `PHI_step` | sin hipotesis       | `(hP : PredHyp)`                       | `(hbot …)(hatom …)` |
    | `DESCENSO_imp` | `(w s)`         | `(hP)(w v s t)`                        | `(hbot …)(…)`       |

    Sacar `PHI`, `PHI_step`, `PHI_all`, `PHI_at`, `PHI_use`, `PHIbody`, `hPHI`, `PSI_inst`,
    `psi_lift_form` y la familia `DESCENSO_*` a la RAIZ dejaria esos tres modulos con nombres
    de raiz AMBIGUOS. Se quedan CUALIFICADOS: `EvalLiftcPrf.PHI_step`, `EvalLiftcPrf.DESCENSO`.

    Lo que SI sale a la raiz es (a) el resultado consumible `pcc_eval_liftc`, (b) los cuatro
    transportes De Bruijn de los objetivos, y (c) **los ocho lemas GENERICOS de §2–§4**, que
    NO mencionan `targetLift` y que los otros dos descensos vuelven a necesitar palabra por
    palabra (`EvalSubstfcPrf.lean:5333‑5424`, `:2469‑2567`). Al salir de aqui, la promocion
    siguiente los CONSUME en vez de redefinirlos por tercera vez. -/

export ROBINSON_PlusPlus.Meta.EvalLiftcPrf (
  liftF_targetLift liftF_targetLiftsc
  -- ⚠️ `substF_targetLift` / `substF_targetLiftsc` los exporta ahora `LiftcCodePrf`, a la
  --    MISMA raiz: bajaron alli. Exportar aqui un nombre que el modulo ya no declara es
  --    error de elaboracion, no un aviso.
  PrfH_congr_targetLiftsc
  nilOrCons nilOrCons_at prf_nil_or_cons_all prf_nil_or_cons
  -- ⚠️ `prf_argsIn_head` / `prf_argsIn_tail` ya NO se exportan desde aqui: viven en
  --    `Meta/CodeWitnessPrf.lean` (`SinWTs`), que es donde esta `PrfH_inst_argsIn`.
  -- ⚠️ `prf_isTermCodeE1_of_boundedIn` / `_of_In` ya no se exportan desde aqui: viven en
  --    `Meta/CodeWitnessPrf.lean` (`SinWTs`), junto a `PrfH_inst_wfAll1`, que es de quien
  --    salen. Exportar un nombre que el modulo ya no declara es ERROR DURO de elaboracion.
  pcc_eval_liftc
)

/-! ## CONTROL DE FOOTPRINT

    ⚠️ **NET-0 aqui significa «ningun axioma NUEVO», no «solo los tres de Lean».** Los
    resultados sustantivos de este modulo salen con **CUATRO**:

        [propext, Classical.choice, Quot.sound, Representability2Prf.prf_axiomsCodeT_eq]

    El cuarto es uno de los `axiom` de Lean ya sancionados del proyecto
    (`Meta/Representability2Prf.lean:104`) y **ya estaba en la linea base**: `LiftcCodePrf`
    lo arrastra en `refl_termCode` y en `refl_shapeUn_imp`, ambos anteriores a este modulo.
    Medido, no supuesto.

    Los que SI salen con los tres —o con menos— son los PUENTES de consumo de §0, que son
    puramente definicionales. No citar «net-0 puro» para los teoremas principales. -/

#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista_imp
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_step
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.PHI_all
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLift_real
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLiftsc_real
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_hasWit_descenso

-- CONTROL: los puentes de consumo son NET-0 y `rfl`.
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLift_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.targetLiftsc_es_el_del_sondeo
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.iz_inv_es_prf_substtc_termCode_nil

/-! ## ENUNCIADOS LITERALES -/

#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc
