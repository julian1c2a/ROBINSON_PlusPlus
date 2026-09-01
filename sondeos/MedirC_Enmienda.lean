/-
################################################################################
MEDICION (no construccion) — LA ENMIENDA DEL ESQUEMA `ax_lineWF_q1` Y SU COSTE.
Angulo (C).  ⚠️ NO se toca `Minimal/Axioms.lean`: la enmienda se escribe como `def` de `Probe/`.
Todo lo que se afirma abajo esta COMPILADO en este fichero (exit 0, `lake env lean`).
################################################################################

RESUMEN DE LO MEDIDO (cada punto tiene su teorema o su `run_cmd` en el cuerpo):

 1. La enmienda TIPA y es escribible con vocabulario objeto de PRODUCCION
    (`ENS.hasWit` / `ENS.hasWitF` de `Meta/CodeWitnessPrf.lean`).      → §2
    Ademas cumple la obligacion administrativa del chasis (`substFormula 0 #0 C = C`),
    que NO era obvia por los dos `∃` de `hasWitF`.                      → §2
 2. EL CHASIS LA ABSORBE: `hcond_absorbe_extra` aplica tal cual.        → §3, §4
 3. SOLIDEZ: NO se rompe. Anadir conjuntos hace el lado derecho del `⇔` mas FUERTE ⇒
    la direccion de ACEPTACION (`⇐`, la del incidente `ax_lineWF_gen`) acepta MENOS
    lineas, y la de EXTRACCION (`⇒`) entrega MAS. Una sola implicacion lo decide. → §5
 4. COMPLETITUD (D1) sobre lineas REALES: se paga (`HW.prf_hasWitF_real` + el gemelo
    `prf_hasWit_real`, probado aqui).                                    → §6
 5. LO QUE COMPRA: dentro de `hcond` queda disponible LITERALMENTE el antecedente de
    `pcc_eval_substfc_wit`.                                             → §7
 6. LO QUE DEBE: el reflector Σ₁ del conjunto extra (`DEUDA_hGuard`).    → §7
 7. ⛔ EL COSTE QUE NADIE HABIA MEDIDO — LA CIRCULARIDAD: la guarda DISCRIMINA
    (`CRIT_hasWitF_rejects_varc` compilado), luego NO se puede descargar para codigo
    ABSTRACTO; y `prf_lineOk_q1 (c Ac w)` / `prf_lineOk_q2 (c Ac w)` la usan con `Ac`,`w`
    ABSTRACTOS. Esos dos alimentan `pcc_forallElim_code_open` / `pcc_exIntro_code_open`,
    que alimentan `pcc_thm_inst`, que alimenta `schema_backbone`, que ES el chasis de los
    21 tags. **Enmendar q1 rompe el chasis que consume la enmienda.**     → §8, §9
 8. ¿CAMBIA `G`? **NO.** `godelCN` no depende de `axioms` ni de `ax_lineWF_q1` (medido
    sobre el `Environment`, no por grep). Lo que cambia es la TEORIA (`⊢`), no la
    SENTENCIA. Y el NUMERO de axiomas tampoco cambia: 141 antes y despues.  → §10

Como re-ejecutar:   lake env lean Probe\MC_enmienda.lean
-/
import ROBINSON_PlusPlus.Meta
import Lean

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ArithPrf ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LineWFSchemaPrf
open ROBINSON_PlusPlus.Meta.LineWFAssemblePrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.D3InDotPrf ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.Delta0ReflectPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.MpCodePrf ROBINSON_PlusPlus.Meta.ForallElimCodePrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace MCenmienda

/-! ## §1 · El esquema ACTUAL de `q1`, en forma de chasis -/

/-- La condicion estructural ACTUAL de `q1`. -/
def condQ1 : Formula :=
  carc (.var 0) =eq implc (forallc (nthc (.var 0) (numeralM 2)))
    (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2)))

/-- El axioma de produccion, releido con las piezas del chasis. **`rfl`**. -/
theorem ax_lineWF_q1_eq_chasis :
    ax_lineWF_q1
      = Formula.forall (Formula.impl (tagF 9) (lwfVar ⇔ Formula.and (lencF 4) condQ1)) := rfl

/-! ## §2 · LA ENMIENDA, escrita con vocabulario objeto de PRODUCCION

`q1` es `⟨concl, 9, ⌜A⌝, ⌜t⌝⟩` con `concl ⇔ (∀A) ⇒ A[t]`: la casilla **2** lleva un codigo de
FORMULA y la casilla **3** el codigo del TERMINO sustituyente. El conjunto de bien-formacion es
exactamente la GUARDA de `pcc_eval_substfc_wit`, con `s := nthc #0 3` y `f := nthc #0 2`. -/

/-- **El conjunto extra**: la guarda de `pcc_eval_substfc_wit` sobre las casillas de `q1`.
    `ENS.hasWit` / `ENS.hasWitF` son constantes de PRODUCCION (`Meta/CodeWitnessPrf.lean`). -/
def guardQ1 : Formula :=
  Formula.and (ENS.hasWit (nthc (.var 0) (numeralM 3)))
              (ENS.hasWitF (nthc (.var 0) (numeralM 2)))

/-- La condicion ENMENDADA (conjunto extra PRIMERO, que es lo que pide `hcond_absorbe_extra`). -/
def condQ1E : Formula := Formula.and guardQ1 condQ1

/-- **EL AXIOMA ENMENDADO** — el enunciado exacto de la propuesta.
    ⚠️ Es un `def` de `Probe/`, NO se toca `Minimal/Axioms.lean`. -/
def ax_lineWF_q1_ENM : Formula :=
  Formula.forall (Formula.impl (tagF 9) (lwfVar ⇔ Formula.and (lencF 4) condQ1E))

/-- TIPA, y es una `Formula` cerrada del lenguaje objeto (mismo tipo que el axioma real). -/
example : Formula := ax_lineWF_q1_ENM

/-- La enmienda **no es** el axioma actual: son formulas DISTINTAS. -/
example : True := by
  fail_if_success exact (rfl : ax_lineWF_q1_ENM = ax_lineWF_q1)
  trivial

/-! ### La obligacion administrativa del chasis, para la condicion ENMENDADA

`pcc_lineWF_tracked_of_schema` pide `hC : substFormula 0 #0 C = C`. Para `condQ1` sale por `rfl`;
la pregunta REAL es si sigue saliendo con los dos `∃` de `hasWitF` delante (De Bruijn). -/

theorem substFormula_condQ1 : substFormula 0 (.var 0) condQ1 = condQ1 := rfl

/-- Fontaneria que FALTABA en produccion (`Meta/CodeWitnessPrf.lean` solo tiene `liftF_hasWitF`):
    `substFormula` conmuta con `hasWitF`. Net-0. -/
theorem substF_hasWitF (v : Nat) (s c : Term) :
    substFormula v s (ENS.hasWitF c) = ENS.hasWitF (substTerm v s c) := by
  have h1 : (1 = v + 1 + 1) = False := eq_false (by omega)
  have h2 : (1 > v + 1 + 1) = False := eq_false (by omega)
  have h3 : (0 = v + 1 + 1) = False := eq_false (by omega)
  have h4 : (0 > v + 1 + 1) = False := eq_false (by omega)
  simp only [ENS.hasWitF, substFormula, ENS.substF_isFC1, substTerm, h1, h2, h3, h4, if_false,
    FOL.substTerm_lift_comm_zero]

theorem substFormula_guardQ1 : substFormula 0 (.var 0) guardQ1 = guardQ1 := by
  simp only [guardQ1, substFormula, ENS.substF_hasWit, substF_hasWitF, nthc, substTerm,
    substTerms, substTerm_numeralM, FOL.substTerm_liftTerm, if_true]

theorem substFormula_condQ1E : substFormula 0 (.var 0) condQ1E = condQ1E := by
  simp only [condQ1E, substFormula, substFormula_guardQ1, substFormula_condQ1]

/-! ### La guarda instanciada en una linea `t` ES la guarda de `pcc_eval_substfc_wit`

`sondeos/EvalSubstfcPrf.lean:8328`:
`pcc_eval_substfc_wit (v s f) : Prf (land (hasWit s) (hasWitF f) ⇒ targetSubstfc v s f)`.
Con `s := nthc t 3` y `f := nthc t 2`, su antecedente es LITERALMENTE `substFormula 0 t guardQ1`. -/
theorem substFormula_guardQ1_at (t : Term) :
    substFormula 0 t guardQ1
      = Formula.and (ENS.hasWit (nthc t (numeralM 3))) (ENS.hasWitF (nthc t (numeralM 2))) := by
  simp only [guardQ1, substFormula, ENS.substF_hasWit, substF_hasWitF, nthc, substTerm,
    substTerms, substTerm_numeralM, FOL.substTerm_liftTerm, if_true]

/-- Y `substFormula 0 t condQ1E` se parte en la guarda + la condicion de siempre. -/
theorem substFormula_condQ1E_at (t : Term) :
    substFormula 0 t condQ1E
      = Formula.and
          (Formula.and (ENS.hasWit (nthc t (numeralM 3))) (ENS.hasWitF (nthc t (numeralM 2))))
          (carc t =eq implc (forallc (nthc t (numeralM 2)))
            (substfc zero (nthc t (numeralM 3)) (nthc t (numeralM 2)))) := by
  simp only [condQ1E, condQ1, substFormula, substFormula_guardQ1_at, carc, nthc, implc, forallc,
    substfc, zero, cons, nil, succ, substTerm, substTerms, substTerm_numeralM,
    FOL.substTerm_liftTerm, if_true]

/-! ## §3 · ¿LO ABSORBE EL CHASIS?  — `hcond_absorbe_extra` reprobado y APLICADO a `q1`

`sondeos/SegundoMuro.lean` esta FUERA del build (no hay `.olean`), asi que no se puede importar:
se reprueba aqui literalmente (25 lineas, net-0) y se INSTANCIA en `q1`. -/

/-- Copia literal de `SegundoMuro.hcond_absorbe_extra` (sondeo fuera del build). -/
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
  have hcomp : Prf (andc (condD P t) (condD C t) =eq condD (Formula.and P C) t) :=
    prf_eq_symm (prf_substfc_and zero (tcFn t) (formCode P) (formCode C))
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hcomp) _)
    (PrfH_and_intro_code _ _ hPd hCd)

/-- **RESPUESTA A LA PREGUNTA 2: SI.** El chasis absorbe la enmienda de `q1` sin rehacerse:
    de los DOS reflectores (el del conjunto extra y el de la condicion de siempre) sale la
    `hcond` EXACTA que pide `pcc_lineWF_tracked_of_schema` para `condQ1E`. -/
theorem hcond_q1E_de_las_dos_mitades (t : Term)
    (hGuard : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t guardQ1 ⇒ provFromCode (condD guardQ1 t)))))
    (hCarc : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t))))) :
    Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1E ⇒ provFromCode (condD condQ1E t)))) :=
  hcond_absorbe_extra guardQ1 condQ1 t 4 hGuard hCarc

/-! ## §4 · EL ENCAJE COMPLETO: `q1` cerrado POR la enmienda, modulo las dos mitades

Esto es lo que compra la via (C). `hCarc` es el reflector que HOY es imposible sin guarda
(`ENS.CRIT_isFC1_rejects_varc` refuta `isFC1` para argumento abstracto); con la enmienda tiene
`substFormula 0 t condQ1` **y** `substFormula 0 t guardQ1` en el contexto, que es exactamente el
antecedente de `pcc_eval_substfc_wit`. -/

theorem q1_cerrado_por_la_enmienda (t : Term)
    (hax : Prf ax_lineWF_q1_ENM)
    (hGuard : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t guardQ1 ⇒ provFromCode (condD guardQ1 t)))))
    (hCarc : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t condQ1 ⇒ provFromCode (condD condQ1 t))))) :
    Prf (lineWF t ⇒ ((nthc t (succ zero) =eq numeralM 9) ⇒
      provFromCode (lineWFCodeFn (tcFn t)))) :=
  pcc_lineWF_tracked_of_schema t substFormula_condQ1E hax
    (hcond_q1E_de_las_dos_mitades t hGuard hCarc) (by omega)

/-- Y eso enchufa DIRECTAMENTE en el ensamblador de produccion (hipotesis `hq1` de
    `pcc_lineWF_tracked_modulo_7`): el tipo es el mismo modulo `lineTag t = nthc t (succ zero)`. -/
theorem encaja_en_el_ensamblador (t : Term) :
    (lineTag t =eq numeralM 9) = (nthc t (succ zero) =eq numeralM 9) := rfl

/-! ## §5 · ¿SE ROMPE LA SOLIDEZ?  — NO, y es un teorema de una linea

El incidente `ax_lineWF_gen` fue INSOLIDO por AFLOJAR la direccion de aceptacion (`⇐`).
Anadir un conjunto va en la direccion CONTRARIA: el lado derecho del `⇔` se hace mas FUERTE,
luego el `⇐` acepta **menos** lineas y el `⇒` entrega **mas**. Las dos cosas salen de una sola
implicacion objeto. -/

/-- **La sola implicacion que lo decide**: el lado derecho ENMENDADO implica el ACTUAL. -/
theorem enm_implica_actual (Ln P C : Formula) :
    Prf (Formula.and Ln (Formula.and P C) ⇒ Formula.and Ln C) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (Formula.and Ln (Formula.and P C))
  have hL : PrfH [Formula.and Ln (Formula.and P C)] Ln :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hh
  have hPC : PrfH [Formula.and Ln (Formula.and P C)] (Formula.and P C) :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hh
  have hC : PrfH [Formula.and Ln (Formula.and P C)] C :=
    PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c3 _ _)) hPC
  exact PrfH_and_intro hL hC

/-- **(a) ACEPTACION — no se acepta NI UNA linea mas.** Si con la enmienda una linea pasa el `⇐`,
    con el esquema ACTUAL tambien pasaba. Es la direccion peligrosa (la del incidente `gen`),
    y va hacia el lado seguro. -/
theorem enm_no_acepta_mas (X Ln P C : Formula)
    (hactual : Prf (Formula.and Ln C ⇒ X)) :
    Prf (Formula.and Ln (Formula.and P C) ⇒ X) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH hactual _)
    (PrfH.mp _ _ _ (prf_to_prfH (enm_implica_actual Ln P C) _)
      (prfH_hyp_self (Formula.and Ln (Formula.and P C))))

/-- **(b) EXTRACCION — no se pierde NADA aguas abajo.** Todo lo que el esquema ACTUAL entregaba
    por el `⇒`, la enmienda lo sigue entregando (y ademas la guarda). -/
theorem enm_no_pierde_nada (X Ln P C : Formula)
    (henm : Prf (X ⇒ Formula.and Ln (Formula.and P C))) :
    Prf (X ⇒ Formula.and Ln C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (enm_implica_actual Ln P C) _)
    (PrfH.mp _ _ _ (prf_to_prfH henm _) (prfH_hyp_self X))

/-- Instanciado en `q1`: el lado derecho enmendado implica el actual. -/
theorem enm_q1_implica_actual :
    Prf (Formula.and (lencF 4) condQ1E ⇒ Formula.and (lencF 4) condQ1) :=
  enm_implica_actual (lencF 4) guardQ1 condQ1

/-! ## §6 · EL PRECIO DE LA ENMIENDA ES LA COMPLETITUD (D1), Y SE PAGA

Restringir `lineWF` no puede romper la SOLIDEZ (§5), pero SI podria romper la COMPLETITUD: D1
tiene que seguir probando `lineWF L` para las lineas `q1` REALES, y ahora eso pide ademas el
conjunto extra. Aqui se compila que **se paga**, con piezas de PRODUCCION. -/

open ROBINSON_PlusPlus.Meta.NumListPrf in
/-- El accesor de la casilla 3 (falta en produccion; `prf_nthc_c1`/`c2` si estan). -/
theorem prf_nthc_c3 (a b c d e : Term) :
    Prf (nthc (cons a (cons b (cons c (cons d e)))) (numeralM 3) =eq d) :=
  prf_eq_trans (prf_nthc_succ a (cons b (cons c (cons d e))) (numeralM 2))
    (SinWTs.prf_nthc_c2 b c d e)

/-- **`hasWit` para un codigo de termino REAL** — el gemelo de `HW.prf_hasWitF_real`, que
    faltaba. `∃`-intro con la lista testigo canonica `objList (tcodes1 t)`. Net-0. -/
theorem prf_hasWit_real (t : Term) : Prf (ENS.hasWit (termCodeM t)) := by
  have hw := SinWTs.prf_isTC1_tcodes t
  have hs : substFormula 0 (objList (SinWTs.tcodes1 t))
      (SinWTs.isTC1 (.var 0) (liftTerm 0 (termCodeM t)))
      = SinWTs.isTC1 (objList (SinWTs.tcodes1 t)) (termCodeM t) := by
    simp only [ENS.substF_isTC1, substTerm, FOL.substTerm_liftTerm, if_true]
  have hq := Prf.incl (Prf₀.q2 (SinWTs.isTC1 (.var 0) (liftTerm 0 (termCodeM t)))
    (objList (SinWTs.tcodes1 t)))
  rw [hs] at hq
  exact prf_mp hq hw

/-- Congruencia de `hasWit` (Leibniz objeto). -/
theorem prf_congr_hasWit {a b : Term} (h : Prf (a =eq b)) (hw : Prf (ENS.hasWit a)) :
    Prf (ENS.hasWit b) := by
  have e : ∀ s : Term, substFormula 0 s (ENS.hasWit (.var 0)) = ENS.hasWit s := by
    intro s; simp only [ENS.substF_hasWit, substTerm, if_true]
  have hl := Prf.incl (Prf₀.leibniz (ENS.hasWit (.var 0)) a b)
  rw [e a, e b] at hl
  exact prf_mp (prf_mp hl h) hw

/-- Congruencia de `hasWitF` (Leibniz objeto). -/
theorem prf_congr_hasWitF {a b : Term} (h : Prf (a =eq b)) (hw : Prf (ENS.hasWitF a)) :
    Prf (ENS.hasWitF b) := by
  have e : ∀ s : Term, substFormula 0 s (ENS.hasWitF (.var 0)) = ENS.hasWitF s := by
    intro s; simp only [substF_hasWitF, substTerm, if_true]
  have hl := Prf.incl (Prf₀.leibniz (ENS.hasWitF (.var 0)) a b)
  rw [e a, e b] at hl
  exact prf_mp (prf_mp hl h) hw

/-- La linea `q1` REAL: `⟨concl, 9, ⌜A⌝, ⌜t⌝⟩`. -/
def lineaQ1 (concl : Term) (A : Formula) (t : Term) : Term :=
  cons concl (cons (numeralM 9) (cons (formCodeM A) (cons (termCodeM t) nil)))

/-- **RESPUESTA A «¿se rompe D1?»: NO.** Para la linea `q1` REAL, el conjunto extra ENMENDADO
    es DEMOSTRABLE, con `HW.prf_hasWitF_real` (produccion) y `prf_hasWit_real` (arriba).
    Es literalmente `substFormula 0 (lineaQ1 …) guardQ1`. -/
theorem guardQ1_se_paga (concl : Term) (A : Formula) (t : Term) :
    Prf (substFormula 0 (lineaQ1 concl A t) guardQ1) := by
  rw [substFormula_guardQ1_at]
  refine prf_and_intro ?_ ?_
  · exact prf_congr_hasWit
      (prf_eq_symm (prf_nthc_c3 concl (numeralM 9) (formCodeM A) (termCodeM t) nil))
      (prf_hasWit_real t)
  · exact prf_congr_hasWitF
      (prf_eq_symm (SinWTs.prf_nthc_c2 concl (numeralM 9) (formCodeM A)
        (cons (termCodeM t) nil)))
      (HW.prf_hasWitF_real A)

/-! ## §7 · LO QUE LA ENMIENDA **COMPRA** Y LO QUE **DEBE**

**COMPRA**: dentro de `hcond` del esquema enmendado, el antecedente contiene LITERALMENTE la
guarda de `pcc_eval_substfc_wit` (`sondeos/EvalSubstfcPrf.lean:8328`), o sea el reflector `hCarc`
—hoy IMPOSIBLE sin guarda— pasa a ser una MP.

**DEBE**: el reflector del conjunto extra, `hGuard`, que es reflexion Σ₁ de un `∃∃`. -/

/-- **LA COMPRA, compilada.** Cualquier consumidor `huso` de la guarda (en particular
    `pcc_eval_substfc_wit` con `s := nthc t 3`, `f := nthc t 2`) se aplica DENTRO de `hcond`
    del esquema enmendado. Esto es lo unico que la via (C) tiene que dar, y lo da. -/
theorem guarda_disponible_en_hcond (t : Term) (X : Formula)
    (huso : Prf (Formula.and (ENS.hasWit (nthc t (numeralM 3)))
                             (ENS.hasWitF (nthc t (numeralM 2))) ⇒ X)) :
    Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒ (substFormula 0 t condQ1E ⇒ X))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (substFormula 0 t condQ1E) [lenc t =eq numeralM 4, lineWF t] rfl)
    (lenc t =eq numeralM 4) [lineWF t] rfl)
  have hh : PrfH [substFormula 0 t condQ1E, lenc t =eq numeralM 4, lineWF t]
      (substFormula 0 t condQ1E) := PrfH.hyp _ _ (List.Mem.head _)
  rw [substFormula_condQ1E_at] at hh
  exact PrfH.mp _ _ _ (prf_to_prfH huso _)
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.c2 _ _)) hh)

/-- **LA DEUDA, enunciada exactamente.** Es lo unico que la via (C) deja abierto en `q1`
    (ademas de la enmienda misma). No se prueba aqui: se MIDE. -/
abbrev DEUDA_hGuard (t : Term) : Prop :=
  Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
    (substFormula 0 t guardQ1 ⇒ provFromCode (condD guardQ1 t))))

/-- Y la deuda se PARTE en dos por el mismo mecanismo que absorbe el conjunto extra
    (`substfc` distribuye sobre `andc`): reflector de `hasWit` + reflector de `hasWitF`. -/
theorem DEUDA_se_parte (t : Term)
    (h1 : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t (ENS.hasWit (nthc (.var 0) (numeralM 3))) ⇒
        provFromCode (condD (ENS.hasWit (nthc (.var 0) (numeralM 3))) t)))))
    (h2 : Prf (lineWF t ⇒ ((lenc t =eq numeralM 4) ⇒
      (substFormula 0 t (ENS.hasWitF (nthc (.var 0) (numeralM 2))) ⇒
        provFromCode (condD (ENS.hasWitF (nthc (.var 0) (numeralM 2))) t))))) :
    DEUDA_hGuard t :=
  hcond_absorbe_extra _ _ t 4 h1 h2

/-! ## §8 · ⚠️ EL HALLAZGO CARO: LA GUARDA **DISCRIMINA**, Y ESO ROMPE LAS LINEAS ABIERTAS

La guarda no es vacua: refuta los codigos que no son de FORMULA. Eso es lo que la hace util
(no cierra `ex falso`), **y a la vez** lo que hace cara la enmienda: `Meta/ForallElimCodePrf.lean:68`
`prf_lineOk_q1 (c Ac w : Term)` y `Meta/Sigma1CorePrf.lean:268` `prf_lineOk_q2 (c Ac w : Term)`
usan la direccion `⇐` del esquema con `Ac`, `w` **ABSTRACTOS**. Con la enmienda, esa direccion pide
la guarda sobre `Ac`, y para `Ac` abstracto la guarda es REFUTABLE. Se compila aqui.

(Reprueba de `sondeos/EvalSubstfcPrf.lean` §14, que esta fuera del build, con piezas de PRODUCCION.) -/

theorem prf_shapeNul_str (X : Term) (k : Nat) :
    Prf (Formula.impl (ENS.shapeNul X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 1))))) :=
  SinWTs.prf_shape_strengthens X _ k 1 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c1 _) (SinWTs.prf_consOk_cons _ _)

theorem prf_shapeUn_str' (X : Term) (k : Nat) :
    Prf (Formula.impl (SinWTs.shapeUn X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 2))))) :=
  SinWTs.prf_shape_strengthens X _ k 2 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c2 _ _) (SinWTs.prf_consOk_cons _ _)

theorem prf_shapeBin_str' (X : Term) (k : Nat) :
    Prf (Formula.impl (SinWTs.shapeBin X k)
      (land (SinWTs.consOk X) (land (Formula.eq (carc X) (numeralM k))
                                    (Formula.eq (lenc X) (numeralM 3))))) :=
  SinWTs.prf_shape_strengthens X _ k 3 (prf_carc_cons _ _)
    (SinWTs.prf_lenc_c3 _ _ _) (SinWTs.prf_consOk_cons _ _)

theorem lor_map {A A' B B' : Formula} (hA : Prf (A ⇒ A')) (hB : Prf (B ⇒ B')) :
    Prf (lor A B ⇒ lor A' B') :=
  SinWTs.prf_or_elim_imp (SinWTs.impT hA (SinWTs.prf_lorL _ _))
    (SinWTs.impT hB (SinWTs.prf_lorR _ _))

/-- La forma ECUACIONAL fortalece la POSICIONAL — 8 disyuntos a 8 disyuntos. -/
theorem prf_isFormCodeE2_str (wF wT X : Term) :
    Prf (Formula.impl (ENS.isFormCodeE2 wF wT X) (SinWTs.isFormCodeB2 wF wT X)) := by
  simp only [ENS.isFormCodeE2, SinWTs.lorAll, ENS.clBot, ENS.clAtom, ENS.clEq, ENS.clBin,
    ENS.clUn, SinWTs.isFormCodeB2]
  exact lor_map (prf_shapeNul_str X 2)
   (lor_map (SinWTs.prf_str_and X 3 3 _ _ (prf_shapeBin_str' X 3))
    (lor_map (SinWTs.prf_str_and X 4 3 _ _ (prf_shapeBin_str' X 4))
     (lor_map (SinWTs.prf_str_and X 5 3 _ _ (prf_shapeBin_str' X 5))
      (lor_map (SinWTs.prf_str_and X 6 2 _ _ (prf_shapeUn_str' X 6))
       (lor_map (SinWTs.prf_str_and X 7 3 _ _ (prf_shapeBin_str' X 7))
        (lor_map (SinWTs.prf_str_and X 8 3 _ _ (prf_shapeBin_str' X 8))
                 (SinWTs.prf_str_and X 9 2 _ _ (prf_shapeUn_str' X 9))))))))

/-- **CONTROL**: un codigo de VARIABLE no pasa el reconocedor de FORMULA. -/
theorem CRIT_E2_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (ENS.isFormCodeE2 wF wT (varc n)) Formula.bottom) :=
  SinWTs.impT (prf_isFormCodeE2_str wF wT (varc n))
    (SinWTs.crit_isFormCodeB2_rejects_varc wF wT n)

/-- **CONTROL**: la GUARDA COMPLETA hereda la discriminacion. -/
theorem CRIT_isFC1_rejects_varc (wF wT n : Term) :
    Prf (Formula.impl (ENS.isFC1 wF wT (varc n)) Formula.bottom) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (ENS.isFC1 wF wT (varc n))
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hh)
  have hin := PrfH_and_elim_right hh
  have hcode := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (ENS.prf_isFormCodeE2_of_In wF wT (varc n)) _) hin) hwF
  exact PrfH.mp _ _ _ (prf_to_prfH (CRIT_E2_rejects_varc wF wT n) _) hcode

/-- **★ EL CONTROL QUE MIDE EL COSTE ★** — la guarda CUANTIFICADA tambien refuta un codigo de
    variable: `Prf (hasWitF (varc n) ⇒ ⊥)`. Luego la guarda **NO** se puede descargar para un
    codigo ABSTRACTO, y todo consumidor que hoy pasa un codigo abstracto por la direccion `⇐`
    de `q1`/`q2` deja de compilar con la enmienda. -/
theorem CRIT_hasWitF_rejects_varc (n : Term) :
    Prf (Formula.impl (ENS.hasWitF (varc n)) Formula.bottom) := by
  refine prf_ex_elim_imp ?_
  refine PrfH.mp _ _ _ (prf_to_prfH (prf_ex_elim_imp ?_) _) (prfH_hyp_self _)
  exact PrfH.mp _ _ _ (prf_to_prfH (CRIT_isFC1_rejects_varc _ _ _) _) (prfH_hyp_self _)

/-! ## §9 · ⛔ LA CIRCULARIDAD — LA ENMIENDA DE `q1` ROMPE EL CHASIS QUE LA CONSUME

Cadena, toda de PRODUCCION y toda verificable con los `#check` de abajo:

  `LineWFSchemaPrf.schema_backbone` (l.266)  usa  `MpCodePrf.pcc_thm_inst` (l.171)
  `pcc_thm_inst φ h w  :=  prf_mp (pcc_forallElim_code_open (formCode φ) w) (repr_pos'_prf h)`
  `ForallElimCodePrf.pcc_forallElim_code_open` (l.80)  usa  `prf_lineOk_q1 (c Ac w)` (l.68)
  `prf_lineOk_q1`  usa  `prf_iff_mpr (prf_lineWF_q1 _ Ac w)`  ⟸  **`ax_lineWF_q1`**

y `schema_backbone` es la columna vertebral de `pcc_lineWF_tracked_of_schema`, o sea de **los 21
tags**, incluidos los **14 ya cerrados**. -/

/-- El chasis instancia el esquema con testigo-codigo `tcFn t`, `t` **ABSTRACTO**
    (`LineWFSchemaPrf.lean:266`: `pcc_thm_inst _ hbwd (tcFn t)`). -/
example (φ : Formula) (h : Prf (Formula.forall φ)) (t : Term) :
    Prf (provFromCode (substfc zero (tcFn t) (formCode φ))) := pcc_thm_inst φ h (tcFn t)

/-- Y por debajo hay una linea `q1` con casilla 2 = `Ac` y casilla 3 = `w`, **ambas
    abstractas**, aceptada HOY **incondicionalmente**. Con la enmienda haria falta
    `Prf (ENS.hasWitF Ac)` (refutable si `Ac := varc n`, §8) y `Prf (ENS.hasWit w)`
    con `w := tcFn t` para `t` abstracto — que NO existe: `ax_tc_cons` esta RETIRADO por
    inconsistente y `ax_tc_zero`/`ax_tc_succ` solo fijan `tcFn` sobre NUMERALES. -/
example (c Ac w : Term) :
    Prf (lineOk c (cons (implc (forallc Ac) (substfc zero w Ac))
      (cons (numeralM 9) (cons Ac (cons w nil))))) := prf_lineOk_q1 c Ac w

/-- **La imposibilidad, compilada**: no puede haber un `hasWitF` uniforme para codigo abstracto. -/
theorem no_hay_guarda_uniforme (n : Term) (h : ∀ Ac : Term, Prf (ENS.hasWitF Ac)) :
    Prf Formula.bottom :=
  prf_mp (CRIT_hasWitF_rejects_varc n) (h (varc n))

end MCenmienda

/-! ############################################################################
    ## §10 · EL COSTE EN `G`, MEDIDO SOBRE EL ENTORNO (no por grep)

    `feedback_auditoria_footprint.md`: los grep dan FALSOS NEGATIVOS. Aqui se calcula el
    cierre transitivo de dependencias DIRECTAMENTE sobre el `Environment` de Lean, y los
    `run_cmd` **LANZAN ERROR** si la afirmacion es falsa ⇒ el exit code es la evidencia.
    ############################################################################ -/

namespace MCmedicion
open Lean

/-- Cierre transitivo de constantes usadas (tipo + valor). -/
partial def deps (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
    if acc.contains n then deps env rest acc
    else
      let acc := acc.insert n
      match env.find? n with
      | none => deps env rest acc
      | some ci =>
        let l1 := ci.type.getUsedConstants.toList
        let l2 := match ci.value? with | some v => v.getUsedConstants.toList | none => []
        deps env (l1 ++ l2 ++ rest) acc

/-- Constantes usadas DIRECTAMENTE (tipo + valor). -/
def usedDirect (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | none => []
  | some ci =>
    let l1 := ci.type.getUsedConstants.toList
    let l2 := match ci.value? with | some v => v.getUsedConstants.toList | none => []
    (l1 ++ l2).eraseDups

abbrev AXIOMS : Name := `ROBINSON_PlusPlus.Minimal.Axioms.axioms
abbrev CODINGAX : Name := `ROBINSON_PlusPlus.Minimal.Axioms.codingAxioms
abbrev Q1 : Name := `ROBINSON_PlusPlus.Minimal.Axioms.ax_lineWF_q1
abbrev GODEL : Name := `ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN
abbrev PROVC : Name := `ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC'
abbrev PRF : Name := `ROBINSON_PlusPlus.Meta.Hilbert.Prf₀.thy
abbrev D1Q1 : Name := `ROBINSON_PlusPlus.Meta.ReprPrf.prf_lineWF_q1
abbrev ENSAM : Name := `ROBINSON_PlusPlus.Meta.LineWFAssemblePrf.pcc_lineWF_tracked_modulo_7

/-- Los nombres de las constantes de un `NameSet`, ordenados. -/
def dump (s : Array Name) : List Name := s.toList

/-! **CLAVE 1**: `godelCN` (LA SENTENCIA G) **NO depende** de `axioms` ni de `ax_lineWF_q1`.
    Si dependiera, este comando LANZA ERROR y el fichero no compila. -/
open Elab Command in
run_cmd do
  let env ← getEnv
  let d := deps env [GODEL] {}
  if d.contains AXIOMS then throwError "FALSO: godelCN DEPENDE de `axioms`"
  if d.contains Q1 then throwError "FALSO: godelCN DEPENDE de `ax_lineWF_q1`"
  let dp := deps env [PROVC] {}
  if dp.contains AXIOMS then throwError "FALSO: provFormulaC' DEPENDE de `axioms`"
  logInfo m!"[G] godelCN: {d.toList.length} constantes transitivas; \
    contiene `axioms` = {d.contains AXIOMS}; contiene `ax_lineWF_q1` = {d.contains Q1}. \
    provFormulaC': {dp.toList.length} constantes; contiene `axioms` = {dp.contains AXIOMS}."

/-! **CONTROL DE QUE LA MEDICION NO ES VACUA**: lo que SI depende de `ax_lineWF_q1` es la
    TEORIA (`Prf₀.thy`, o sea `⊢`) y los teoremas D1/D3 de produccion. O sea: **cambia la
    TEORIA, no la SENTENCIA**. -/
open Elab Command in
run_cmd do
  let env ← getEnv
  let d := deps env [PRF] {}
  if !d.contains AXIOMS then throwError "FALSO: Prf₀.thy NO depende de `axioms` (medicion vacua)"
  if !d.contains Q1 then throwError "FALSO: Prf₀.thy NO depende de `ax_lineWF_q1` (vacua)"
  let dd := deps env [D1Q1] {}
  let de := deps env [ENSAM] {}
  logInfo m!"[CONTROL] Prf₀.thy: axioms={d.contains AXIOMS}, ax_lineWF_q1={d.contains Q1}. \
    ReprPrf.prf_lineWF_q1: existe={(env.find? D1Q1).isSome}, \
    valor={((env.find? D1Q1).bind (·.value?)).isSome}, \
    ax_lineWF_q1={dd.contains Q1}, axioms={dd.contains AXIOMS} ({dd.toList.length} const.). \
    pcc_lineWF_tracked_modulo_7: ax_lineWF_q1={de.contains Q1}, \
    axioms={de.contains AXIOMS} ({de.toList.length} const.)."

/-! **CLAVE 2**: quien menciona `ax_lineWF_q1` en su **ENUNCIADO** (tipo), en TODO el arbol.
    Barrido EXHAUSTIVO del entorno.
    ⚠️ LIMITE MEDIDO Y DECLARADO: los `.olean` de este proyecto **no traen el cuerpo de los
    `theorem`** (comprobado: `ReprPrf.prf_lineWF_q1` existe pero `value? = none`; 103227 de
    208766 constantes tienen valor, todas `def`/`instance`). Luego este barrido cubre TIPOS
    (todo) y VALORES (solo de `def`s). Para las PRUEBAS, la lista sale por grep y esta en
    §9 y en el informe. -/
open Elab Command in
run_cmd do
  let env ← getEnv
  let hits : Array Name := env.constants.fold (init := #[]) fun acc n ci =>
    if (`ROBINSON_PlusPlus).isPrefixOf n || (`FOL).isPrefixOf n then
      let l1 := ci.type.getUsedConstants
      let l2 := match ci.value? with | some v => v.getUsedConstants | none => #[]
      if l1.contains Q1 || l2.contains Q1 then acc.push n else acc
    else acc
  logInfo m!"[DEP-DIRECTA de ax_lineWF_q1] {hits.size}: {hits.qsort Name.lt |>.toList}"

/-! **CLAVE 2b**: idem para `ReprPrf.prf_lineWF_q1` (0 hits *por el limite de arriba*, no porque
    nadie lo use: el grep da 8 modulos y ~25 llamadas; ver §9). -/
open Elab Command in
run_cmd do
  let env ← getEnv
  let hits : Array Name := env.constants.fold (init := #[]) fun acc n ci =>
    if (`ROBINSON_PlusPlus).isPrefixOf n || (`FOL).isPrefixOf n then
      let l1 := ci.type.getUsedConstants
      let l2 := match ci.value? with | some v => v.getUsedConstants | none => #[]
      if l1.contains D1Q1 || l2.contains D1Q1 then acc.push n else acc
    else acc
  logInfo m!"[DEP-DIRECTA de ReprPrf.prf_lineWF_q1] {hits.size}: {hits.qsort Name.lt |>.toList}"

/-! **CLAVE 3**: cuantos `ax_lineWF_*` hay en total (la enmienda toca 7 de ellos). -/
open Elab Command in
run_cmd do
  let env ← getEnv
  let lwf : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if (`ROBINSON_PlusPlus.Minimal.Axioms).isPrefixOf n
        && (n.getString!).startsWith "ax_lineWF_" then acc.push n else acc
  logInfo m!"[ax_lineWF_*] {lwf.size}: {lwf.qsort Name.lt |>.toList}"

end MCmedicion

namespace MCcifras
open ROBINSON_PlusPlus.Minimal.Axioms

/-! Cifras: longitud de las listas de axiomas OBJETO. -/
#eval axioms.length          -- 141
#eval codingAxioms.length    -- 107
#eval coreAxioms.length      --  34

/-- **La enmienda NO cambia el NUMERO de axiomas**: sustituye el CONTENIDO de 7 elementos de
    la lista. La longitud —y por tanto el numero de pasos de `prf_In_listFormCodeM` /
    `prf_not_In_listFormCodeM`— es la misma. -/
example : axioms.length = 141 := by decide

/-- Y `axioms = coreAxioms ++ codingAxioms` sigue siendo `rfl` tras la enmienda: los 7
    esquemas viven en `codingAxioms`, no en `coreAxioms` (la teoria MATEMATICA no se toca). -/
example : axioms = coreAxioms ++ codingAxioms := axioms_eq

end MCcifras

/-! ############################################################################
    ## §11 · FOOTPRINT — `#print axioms` de TODO lo que sostiene el informe.
       La base sancionada del proyecto es {propext, Classical.choice, Quot.sound}.
    ############################################################################ -/

#print axioms MCenmienda.ax_lineWF_q1_eq_chasis
#print axioms MCenmienda.substF_hasWitF
#print axioms MCenmienda.substFormula_condQ1E
#print axioms MCenmienda.substFormula_condQ1E_at
#print axioms MCenmienda.hcond_absorbe_extra
#print axioms MCenmienda.hcond_q1E_de_las_dos_mitades
#print axioms MCenmienda.q1_cerrado_por_la_enmienda
#print axioms MCenmienda.enm_implica_actual
#print axioms MCenmienda.enm_no_acepta_mas
#print axioms MCenmienda.enm_no_pierde_nada
#print axioms MCenmienda.prf_hasWit_real
#print axioms MCenmienda.prf_congr_hasWit
#print axioms MCenmienda.prf_congr_hasWitF
#print axioms MCenmienda.guardQ1_se_paga
#print axioms MCenmienda.guarda_disponible_en_hcond
#print axioms MCenmienda.DEUDA_se_parte
#print axioms MCenmienda.prf_isFormCodeE2_str
#print axioms MCenmienda.CRIT_E2_rejects_varc
#print axioms MCenmienda.CRIT_isFC1_rejects_varc
#print axioms MCenmienda.CRIT_hasWitF_rejects_varc
#print axioms MCenmienda.no_hay_guarda_uniforme

/-! **CONTROL de footprint**: `q1_cerrado_por_la_enmienda` arrastra `prf_axiomsCodeT_eq` porque lo
    arrastra el CHASIS de produccion, no por nada que se anada aqui. Se compara con un tag YA
    CERRADO en produccion por el mismo chasis. -/
#print axioms ROBINSON_PlusPlus.Meta.LineWFEfqPrf.pcc_lineWF_tracked_efq_imp
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.HW.prf_hasWitF_real

/-! ### Firmas que sostienen la CADENA DE CIRCULARIDAD de §9 -/
#check @ROBINSON_PlusPlus.Meta.LineWFSchemaPrf.schema_backbone
#check @ROBINSON_PlusPlus.Meta.MpCodePrf.pcc_thm_inst
#check @ROBINSON_PlusPlus.Meta.ForallElimCodePrf.pcc_forallElim_code_open
#check @ROBINSON_PlusPlus.Meta.ForallElimCodePrf.prf_lineOk_q1
#check @ROBINSON_PlusPlus.Meta.Sigma1CorePrf.prf_lineOk_q2
#check @ROBINSON_PlusPlus.Meta.Delta0ReflectPrf.pcc_exIntro_code_open
#check @ROBINSON_PlusPlus.Meta.ReprPrf.prf_lineWF_q1
#check @ROBINSON_PlusPlus.Meta.LineWFAssemblePrf.pcc_lineWF_tracked_modulo_7
