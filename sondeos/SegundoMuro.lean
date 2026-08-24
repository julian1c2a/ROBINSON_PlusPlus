/-
✅ SONDEO POSITIVO (2026-08-24) — **EL SEGUNDO MURO NO ES UN MURO**.

Contexto: la ruta `isFormCode` para tumbar el **muro de `substfc`** (los 7 tags de `lineWF`:
`q1 q2 q3 leibniz ind qconf listInd`) arrastra una objeción que 8 de 8 revisores afirmaron y
**ninguno compiló**: al meter un conjunto extra dentro del `⇔` de los 7 esquemas,
`pcc_lineWF_tracked` **tiene que reflejarlo también**. Eso es el «segundo muro».

Este sondeo lo parte en dos mitades y **mide las dos**.

## MITAD 1 — ¿lo absorbe el CHASIS?  ✅ SÍ, y está compilado aquí

`hcond_absorbe_extra` (abajo) es net-0. Dado el reflector del conjunto extra `P` y el de la
condición de siempre `C`, sale el de `P ∧ C`, **que es exactamente la `hcond` que pide
`pcc_lineWF_tracked_of_schema`** (`Meta/LineWFSchemaPrf.lean:291`).

⇒ **Enmendar los 7 esquemas NO obliga a rehacer el chasis.** El coste marginal es *sólo* el
reflector del predicado nuevo. Las dos piezas que lo hacen salir:

* `Prf₀.c2` / `Prf₀.c3` — proyecciones de la conjunción **fuera** de `Prov`;
* `prf_substfc_and` (`Meta/ArithPrf.lean`) — `substfc` **distribuye** sobre `andc`, luego
  `condD (P ∧ C) t` **es** `andc (condD P t) (condD C t)`, y `PrfH_and_intro_code` cierra
  **dentro** de `Prov`. Es la lección 1 de la repatriación otra vez: *el transporte cambia de
  NIVEL, no de nombre*.

## MITAD 2 — ¿es alcanzable el REFLECTOR del predicado nuevo?  ✅ los 4 ingredientes están en producción

La obligación es: del hecho OBJETO `isFormCode c` producir `Prov(⌜isFormCode ċ⌝)`, con `c`
**abstracto**. La receta y su precedente:

| ingrediente | dónde | estado |
|---|---|---|
| inducción **fuerte** en forma OBJETO | `Meta/StrongInductionPrf.lean:185` `prf_strong_induction` | ✅ **existe y está exportada** |
| orden bien fundado sobre códigos | `Meta/CantorMonoPrf.lean` `prf_cantor_mono_left/right` | ✅ `lt h (cons h t)`, `lt t (cons h t)` |
| reflector del átomo `<` | `Meta/Delta0ReflectPrf.lean:233` `pcc_lt_tracked` | ✅ |
| **precedente de la forma completa** | `Meta/EvalListPrf.lean:345` `pcc_eval_lenc (L : Term)` | ✅ argumento **abstracto**, conclusión en `Prov`, vía `prf_spec` de un `∀` probado por `prf_list_induction` |

⚠️ **`pcc_In_lfc_tracked` (`InAxiomsCodePrf.lean:249`) NO es el precedente**, aunque lo parezca:
recurre sobre `L : List Formula`, una lista **META** de Lean (`| [] => … | f :: fs => …`). Lo
abstracto ahí es `y`/`yc`, no la lista. El precedente bueno es `pcc_eval_lenc`.

⇒ El reflector es **trabajo real y precedentado** (misma receta que `pcc_eval_lenc`, con
`prf_strong_induction` en lugar de `prf_list_induction`), **no** una técnica nueva como `hC_dot`.

## HALLAZGO LATERAL 1 — el ÍNDICE de `MEMORY.md` sigue diciendo que falta la inducción fuerte

Dice: «**(ii)** inducción fuerte en forma OBJETO (`Full/StrongInduction.lean` es GUION, no
importable — está sobre `Derives`)». **Ya no es cierto**: `Meta/StrongInductionPrf.lean:185` la
tiene sobre `Prf`, **exportada**, construida con `prf_nat_induction` + `prf_le_of_lt_succ` +
`prf_not_lt_zero`. El paso (ii) de la ruta 1a está **HECHO**.

(El nodo `project_substfc_wall.md` ya lo había corregido el 2026‑08‑23; lo que arrastraba la
mentira era el **índice**. Es la trampa registrada en `feedback_doc_audit_traps.md`, otra vez:
*los docs de estado se actualizan por su banner y no por su cuerpo* — aquí al revés.)

## HALLAZGO LATERAL 2 — la corrección R-6 CONFIRMADA, y con ella la especificación exacta

R-6 decía que la enmienda «obvia» (`isTermCode (nthc #0 3)` en los 7) es **incorrecta en 4 de 7**.
Verificado leyendo `Minimal/Axioms.lean`, y además la enmienda **correcta** sale mecánicamente
mirando qué POSICIÓN ocupa cada casilla:

| tag | lenc | casillas | `isFormCode` en | `isTermCode` en | por qué |
|---|---|---|---|---|---|
| `q1` (9)      | 4 | 1,2,3   | s2 | s3 | `substfc 0 (nthc X 3) (nthc X 2)`: s3 es el **sustituyendo** |
| `q2` (10)     | 4 | 1,2,3   | s2 | s3 | ídem |
| `q3` (11)     | 4 | 1,2,3   | s2, **s3** | — | `liftfc 0 (nthc X 3)` y `implc (exc …) (nthc X 3)`: s3 es **fórmula** |
| `leibniz` (13)| 5 | 1,2,3,4 | s2 | s3, s4 | `eqc (nthc X 3) (nthc X 4)` ⇒ términos; s2 es el cuerpo |
| `ind` (18)    | **3** | 1,2 | s2 | — | **NO HAY casilla 3**; los sustituyendos son CONCRETOS (`termCodeM zero`, `termCodeM (succ #0)`) |
| `qconf` (19)  | 4 | 1,2,3   | s2, **s3** | — | `liftfc 0 (nthc X 2)`, ambas son **fórmula** |
| `listInd` (20)| **3** | 1,2 | s2 | — | **NO HAY casilla 3**; sustituyendos concretos (`termCodeM nil`, `termCodeM (cons #1 #0)`) |

Las dos formas de romperlo que R-6 señalaba, confirmadas:
1. `ind`/`listInd` tienen `lenc = 3` ⇒ pedir algo de `nthc X 3` es pedir de una casilla que **no
   existe**;
2. en `q3`/`qconf` la casilla 3 lleva un código de **FÓRMULA** ⇒ `isTermCode (nthc X 3)` sería
   **refutable** y el esquema cerraría **ex falso** (B.3c 21/21 por la puerta de atrás).

⇒ **La enmienda correcta pide DOS predicados, no uno**: `isFormCode` en 7/7 (9 instancias) y
`isTermCode` en 3/7 (4 instancias), y son **mutuamente recursivos** (un código de fórmula contiene
códigos de término). Eso **duplica** el trabajo de reflector respecto a lo que suponían los
diseños de julio.

## ⚠️ Nada de esto existe todavía

`isFormCode` / `isTermCode` **no aparecen en ninguna parte del árbol** (comprobado). La ruta pide
definirlos, axiomatizarlos (con su principio de inversión) y reflejarlos. Este sondeo mide el
COSTE, no lo paga.

## Cómo re-ejecutar

    lake env lean sondeos/SegundoMuro.lean
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf ROBINSON_PlusPlus.Meta.CantorMonoPrf

namespace SegundoMuro

/-! ## MITAD 1 — el chasis absorbe el conjunto extra -/

/-- **LA PREGUNTA DE LA MITAD 1**: dado el reflector del conjunto extra `P` y el reflector de la
    condición de siempre `C`, ¿sale el reflector de `P ∧ C` — que es la `hcond` que pide
    `pcc_lineWF_tracked_of_schema`?

    **SÍ**, y net-0. Se mide GENÉRICO en `P` porque `isFormCode` aún no existe. -/
theorem hcond_absorbe_extra (P C : Formula) (t : Term) (n : Nat)
    (hP : Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t P ⇒ provFromCode (condD P t)))))
    (hC : Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t C ⇒ provFromCode (condD C t))))) :
    Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
      (substFormula 0 t (Formula.and P C) ⇒ provFromCode (condD (Formula.and P C) t)))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (substFormula 0 t (Formula.and P C))
    [lenc t =eq numeralM n, lineWF t] rfl)
    (lenc t =eq numeralM n) [lineWF t] rfl)
  let Γ : List Formula :=
    [substFormula 0 t (Formula.and P C), lenc t =eq numeralM n, lineWF t]
  have hlw : PrfH Γ (lineWF t) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hln : PrfH Γ (lenc t =eq numeralM n) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hand : PrfH Γ (Formula.and (substFormula 0 t P) (substFormula 0 t C)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hPt : PrfH Γ (substFormula 0 t P) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hand
  have hCt : PrfH Γ (substFormula 0 t C) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hand
  have hPd : PrfH Γ (provFromCode (condD P t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hP _) hlw) hln) hPt
  have hCd : PrfH Γ (provFromCode (condD C t)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH hC _) hlw) hln) hCt
  -- ∧-intro INTERNO + transporte a la forma `condD (P ∧ C) t`
  have hcomp : Prf (andc (condD P t) (condD C t) =eq condD (Formula.and P C) t) :=
    prf_eq_symm (prf_substfc_and zero (tcFn t) (formCode P) (formCode C))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hcomp) _)
    (PrfH_and_intro_code _ _ hPd hCd)

/-! ## MITAD 2 — los ingredientes del reflector, comprobados por máquina

Cada `example` es una comprobación de que la pieza EXISTE, es importable y tiene el tipo que
el reflector necesitaría. No prueban el reflector; acotan su coste. -/

/-- La **inducción fuerte en forma OBJETO** existe (contra lo que decía `MEMORY.md`). -/
example (Φ : Formula) (hΦ : liftFormula 1 Φ = Φ)
    (step : Prf (Formula.forall (Formula.impl (PSI Φ) Φ))) :
    ∀ t : Term, Prf (substFormula 0 t Φ) :=
  prf_strong_induction Φ hΦ step

/-- El **orden bien fundado** sobre códigos: todo sub-código es ESTRICTAMENTE menor. Es lo que
    justifica la recursión de `isFormCode` y alimenta la `PSI` de la inducción fuerte. -/
example (h t : Term) : Prf (lt h (cons h t)) := prf_cantor_mono_left h t
example (h t : Term) : Prf (lt t (cons h t)) := prf_cantor_mono_right h t

/-- El **reflector del átomo `<`**, que hace falta para meter la hipótesis de inducción fuerte
    DENTRO de `Prov`. -/
example (s t : Term) : Prf ((lt s t) ⇒ provFromCode (ltCodeFn (tcFn s) (tcFn t))) :=
  pcc_lt_tracked s t

/-- **EL PRECEDENTE**: `pcc_eval_lenc` tiene exactamente la forma que necesita el reflector —
    argumento OBJETO **abstracto**, conclusión dentro de `Prov`, probada especializando un `∀`
    demostrado por inducción a nivel objeto. `pcc_In_lfc_tracked` **no** sirve de precedente:
    su recursión es sobre una lista META de Lean. -/
example (L : Term) : Prf (provFromCode (evalLencCode L)) := pcc_eval_lenc L

end SegundoMuro

#print axioms SegundoMuro.hcond_absorbe_extra
