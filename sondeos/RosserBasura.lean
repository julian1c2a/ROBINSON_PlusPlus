import ROBINSON_PlusPlus

/-!
# Rosser, Etapa 0: la mitad BASURA — refutar en `Prf` la guarda de TÉRMINO sobre un numeral (ADR‑125/126)

**Fecha**: 2026‑10‑05. Es la segunda pieza de la Etapa 0 del plan de Rosser (ADR‑122 §2; la primera, la reflexión,
en `sondeos/RosserReflexion.lean`): donde la guarda es FALSA, la reflexión no da nada y hay que REFUTARLA en `Prf`.

**Qué dice** (la guarda ENTERA, con su `∃` eliminado, y por primera vez sobre un NUMERAL):

    Prf (¬ hasWit 0̄)                                         -- el 0 (= nil) no es código de término
    Prf (¬ hasWit c)   para c cerrado con Prf (carc c = k̄), k ∉ {0, 1}
    Prf (¬ hasWit (consN k r)‾)   para todo k ∉ {0, 1} y todo r     -- un numeral, sin hipótesis
    Prf (¬ hasWit [1, s, [0]]‾)    para todo s                     -- la basura, en el ÚNICO argumento (ADR‑126)

`[1, s, [0]]` es la lista de TRES elementos `consN 1 (consN s (consN (consN 0 0) 0))`: etiqueta `1`, casilla de
símbolo `s` (que la guarda no mira) y una lista de UN argumento, el `0`. «Profundidad» cuenta aquí PROYECCIONES hasta
el dato que falla (0: el numeral es `0`; 1: su etiqueta; 2: un argumento); en el ÁRBOL del término, la basura de
`[1, s, [0]]` está a profundidad 1.

Y un control (`control_codigo_no_refutable`): sobre el numeral del código CANÓNICO de cualquier término, `¬ hasWit`
NO es demostrable en `Prf` por ningún método —la solidez en `MNV V₀` lo impide, porque allí esa guarda es verdadera—.
No mide el método sino la guarda: `¬ hasWit` no es demostrable en todas partes, así que lo refutado depende de la
basura. Sólo códigos canónicos; la forma general (`hasWitN c → ¬ Prf ¬hasWit c̄`) sale igual y no está escrita.

**Precedentes** (✏️ auditoría `wf_e04d70c1-e0c`): la guarda ENTERA ya se había refutado en `Prf` sobre términos
CERRADOS —no numerales— con la misma prueba que §2: `CRIT_hasWit_rejects` (`sondeos/MedirC_Deriva.lean`) y
`CRIT_hasWit_rejects_tag` (`sondeos/HasWitFCritica.lean`), y la de fórmula, `CRIT_hasWitF_rejects_tag` y
`CRIT_hasWitF_rejects_varc` (`sondeos/MedirC_Carga.lean`); ninguno compila hoy. Lo nuevo aquí es el NUMERAL, el `0`
y el caso del argumento.

**Cómo**: lo que había en `Meta/CodeWitnessPrf.lean` —el refutador de PROFUNDIDAD 1 con testigo abierto
(`prf_crit_In_rejects_open1`) y la forma de pertenencia de `wfAll1` (`prf_isTermCodeE1_of_In`)— más el `∃`‑elim
(`prf_ex_elim_imp`), el puente `∈ → índice` (`prf_boundedIn_of_In`), y, para el numeral, `carc ⟨k, r⟩‾ = k̄` por
`prf_cons_eval`. Lo nuevo: `0 ≠ cons a b` en `Prf` (por los axiomas de lista L1/L2) y la congruencia de `carc` en
`Prf` (la de `PrfH` ya estaba: `PrfH_eq_congr_carc`). A
profundidad 2 (§4): la forma `B1` (`prf_isTermCodeE1_str`); su rama de variable cae por la etiqueta
(`crit_cOk2_absurd`); la de función da `argsIn`, instanciado en `0` (`PrfH_inst_argsIn`), con `nthc`/`lenc`
evaluados sobre el numeral (`prf_nthc_c2`, `prf_lenc_c1`, `prf_nthc_zero`), y el `0` cae por §1.

⚠️ Lo que NO dice: la versión hereditaria GENERAL (por inducción sobre el numeral: aquí hay UN caso, con un
argumento); la etiqueta buena con forma mala (`[0]‾`, `[1, s]‾`: longitud distinta de 2 o 3), que ningún titular
cubre; nada de `hasWitF`; ni una línea `q1` basura.

## Medido (2026‑10‑05, RPP con ADR‑124)

Compila en 4 s (1,07 GB), 0 errores y 0 avisos; 217 líneas, 14 teoremas (`wc -l`). `#print axioms` de los
cuatro titulares: `[propext, Classical.choice, Quot.sound]`. La §4 compiló a la tercera; la §5, a la primera.

## Cómo re‑ejecutarlo

    lake env lean sondeos/RosserBasura.lean      # desde la raíz de RPP
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs

namespace RosserBasura

/-! ## §1 · Profundidad 0: el `0` (= `nil`) no es código de término -/

/-- `0 ≠ cons a b` en `Prf`, por los axiomas de lista: `a ∈ cons a b`, y nada está en `nil = 0`. -/
theorem prf_zero_ne_cons (a b : Term) : Prf (Formula.impl (Formula.eq zero (cons a b)) Formula.bottom) := by
  refine prf_deduction ?_
  have hin : PrfH [Formula.eq zero (cons a b)] (In a zero) :=
    PrfH_eq_subst_in (PrfH_eq_symm (prfH_hyp_self _)) (PrfH_in_cons_head a b)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil a) _) hin

theorem prf_isTermCodeE1_zero_absurd (w : Term) :
    Prf (Formula.impl (isTermCodeE1 w zero) Formula.bottom) :=
  prf_or_elim_imp (prf_zero_ne_cons _ _) (impT (Prf.incl (Prfᵢ.c2 _ _)) (prf_zero_ne_cons _ _))

/-- 🏁 **`¬ hasWit 0̄`**: la guarda ENTERA, con su `∃` eliminado, para CUALQUIER testigo. -/
theorem prf_neg_hasWit_zero : Prf (neg (hasWit (numeralM 0))) := by
  refine prf_ex_elim_imp ?_
  show PrfH [isTC1 (.var 0) zero] Formula.bottom
  have hh := prfH_hyp_self (isTC1 (.var 0) zero)
  have hc := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_In (.var 0) zero) _)
    (PrfH_and_elim_right hh)) (PrfH_and_elim_left hh)
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_zero_absurd (.var 0)) _) hc

/-! ## §2 · Profundidad 1: una etiqueta que no es de término (∉ {0, 1}) -/

/-- La guarda entera, sobre un `c` cerrado de etiqueta `k ∉ {0, 1}`: el `∃`‑elim sobre `prf_crit_In_rejects_open1`. -/
theorem prf_neg_hasWit_tag (c : Term) (k : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hcl : ∀ n : Nat, liftTerm n c = c) (hck : Prf (carc c =eq numeralM k)) : Prf (neg (hasWit c)) := by
  refine prf_ex_elim_imp ?_
  rw [hcl 0]
  show PrfH [isTC1 (.var 0) c] Formula.bottom
  have hh := prfH_hyp_self (isTC1 (.var 0) c)
  have hb := PrfH.mp _ _ _ (prf_to_prfH (prf_boundedIn_of_In c (.var 0)) _) (PrfH_and_elim_right hh)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (prf_crit_In_rejects_open1 (.var 0) c k hk0 hk1 hcl hck) _) hb) (PrfH_and_elim_left hh)

/-! ## §3 · Sobre un NUMERAL: `⟨k, r⟩‾`, sin hipótesis -/

theorem prf_congr_carc {x y : Term} (h : Prf (x =eq y)) : Prf (carc x =eq carc y) := by
  let f : Formula := Formula.eq (carc (liftTerm 0 x)) (carc (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (carc x) (carc s) := by
    intro s; simp only [f, substFormula, carc, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS y) ▸ prf_leibniz_subst (A := f) h ((hS x) ▸ prf_refl (carc x))

/-- La etiqueta de un numeral `⟨k, r⟩‾`, en `Prf`: `prf_cons_eval` lo parte en `cons k̄ r̄`. -/
theorem prf_carc_numeral (k r : Nat) : Prf (carc (numeralM (consN k r)) =eq numeralM k) := by
  have h1 := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.prf_cons_eval k r
  rw [← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq, ← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq,
    ← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq] at h1
  exact prf_eq_trans (prf_congr_carc (prf_eq_symm h1)) (prf_carc_cons _ _)

/-- 🏁 **Un numeral basura, refutado**: para TODO `k ∉ {0, 1}` y todo `r`, `Prf (¬ hasWit ⟨k, r⟩‾)`. -/
theorem prf_neg_hasWit_num (k r : Nat) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    Prf (neg (hasWit (numeralM (consN k r)))) :=
  prf_neg_hasWit_tag _ k hk0 hk1 (fun n => ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM n _)
    (prf_carc_numeral k r)

/-! ## §4 · Profundidad 2 (en proyecciones), un caso HEREDITARIO: la basura en la lista de argumentos

`[1, s, [0]]` tiene la etiqueta de un término (`1`) y una lista de UN argumento, el `0`, que no es código de nada.
Refutarlo pide bajar: de `X ∈ w` y `wfAll1 w`, la forma `B1` (`prf_isTermCodeE1_str`); su rama de variable cae por la
etiqueta; la de función da `argsIn w (nthc X 2̄)`, que en el índice `0` pone el `0` en `w`, y §1 lo refuta. -/

-- `prf_congr_lenc` y `prf_lt_subst2` son los del árbol (`SinWTs.prf_congr_lenc` en `Meta/CodeWitnessPrf.lean`,
-- `prf_lt_subst2` en `Meta/BoundedInPrf.lean`), abiertos arriba: la primera redacción los re‑derivaba.

/-- `cons ā b̄ = (consN a b)‾`, con `numeralM`. -/
theorem prf_cons_evalM (a b : Nat) : Prf (cons (numeralM a) (numeralM b) =eq numeralM (consN a b)) := by
  have h1 := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.prf_cons_eval a b
  rw [← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq, ← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq,
    ← ROBINSON_PlusPlus.Meta.CheckArith.numeralM_eq] at h1
  exact h1

/-- El numeral de `[1, s, [0]]`, partido: `cons 1̄ (cons s̄ (cons A (0̄)))`, con `A = (consN 0 0)‾ = [0]‾`. -/
theorem prf_parte (s : Nat) :
    Prf (numeralM (consN 1 (consN s (consN (consN 0 0) 0))) =eq
      cons (numeralM 1) (cons (numeralM s) (cons (numeralM (consN 0 0)) (numeralM 0)))) :=
  prf_eq_trans (prf_eq_symm (prf_cons_evalM 1 _))
    (prf_congr_cons_tail (prf_eq_trans (prf_eq_symm (prf_cons_evalM s _))
      (prf_congr_cons_tail (prf_eq_symm (prf_cons_evalM (consN 0 0) 0)))))

/-- La lista de argumentos de `[1, s, [0]]`, evaluada: `nthc X̄ 2̄ = cons 0̄ nil`. -/
theorem prf_args (s : Nat) :
    Prf (nthc (numeralM (consN 1 (consN s (consN (consN 0 0) 0)))) (numeralM 2) =eq cons (numeralM 0) nil) :=
  prf_eq_trans (prf_congr_nthc_lst _ (prf_parte s))
    (prf_eq_trans (prf_nthc_c2 _ _ _ _) (prf_eq_symm (prf_cons_evalM 0 0)))

theorem prf_lt_args (s : Nat) :
    Prf (lt (numeralM 0) (lenc (nthc (numeralM (consN 1 (consN s (consN (consN 0 0) 0)))) (numeralM 2)))) :=
  prf_lt_subst2 (prf_eq_symm (prf_eq_trans (prf_congr_lenc (prf_args s)) (prf_lenc_c1 _)))
    (ROBINSON_PlusPlus.Meta.NatArithPrf.prf_zero_lt_succ zero)

theorem prf_nth0_args (s : Nat) :
    Prf (nthc (nthc (numeralM (consN 1 (consN s (consN (consN 0 0) 0)))) (numeralM 2)) (numeralM 0)
      =eq numeralM 0) :=
  prf_eq_trans (prf_congr_nthc_lst _ (prf_args s)) (ROBINSON_PlusPlus.Meta.NumListPrf.prf_nthc_zero _ _)

/-- 🏁 **La basura en el argumento**: `Prf (¬ hasWit [1, s, [0]]‾)` para TODO `s`. -/
theorem prf_neg_hasWit_prof2 (s : Nat) : Prf (neg (hasWit (numeralM (consN 1 (consN s (consN (consN 0 0) 0)))))) := by
  refine prf_ex_elim_imp ?_
  rw [ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM]
  show PrfH [isTC1 (.var 0) (numeralM (consN 1 (consN s (consN (consN 0 0) 0))))] Formula.bottom
  have hh := prfH_hyp_self (isTC1 (.var 0) (numeralM (consN 1 (consN s (consN (consN 0 0) 0)))))
  have hE1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_In (.var 0) _) _)
    (PrfH_and_elim_right hh)) (PrfH_and_elim_left hh)
  have hB1 := PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_str (.var 0) _) _) hE1
  refine PrfH_or_elim hB1 ?_ ?_
  · exact PrfH.mp _ _ _ (prf_to_prfH (crit_cOk2_absurd _ 1 0 (by decide) (prf_carc_numeral 1 _) _) _)
      (PrfH.hyp _ _ (List.Mem.head _))
  · have h2 : PrfH (cOk (numeralM (consN 1 (consN s (consN (consN 0 0) 0))))
        (funcOkT1 (.var 0) (numeralM (consN 1 (consN s (consN (consN 0 0) 0))))) ::
        [isTC1 (.var 0) (numeralM (consN 1 (consN s (consN (consN 0 0) 0))))])
        (cOk (numeralM (consN 1 (consN s (consN (consN 0 0) 0))))
          (funcOkT1 (.var 0) (numeralM (consN 1 (consN s (consN (consN 0 0) 0)))))) :=
      PrfH.hyp _ _ (List.Mem.head _)
    have hf := PrfH_and_elim_right h2
    have hargs := PrfH_and_elim_right hf
    have hin := PrfH.mp _ _ _ (PrfH_inst_argsIn _ _ (numeralM 0) hargs) (prf_to_prfH (prf_lt_args s) _)
    have hin0 := PrfH_congr_In_left (prf_to_prfH (prf_nth0_args s) _) hin
    have hwf : PrfH (cOk (numeralM (consN 1 (consN s (consN (consN 0 0) 0))))
        (funcOkT1 (.var 0) (numeralM (consN 1 (consN s (consN (consN 0 0) 0))))) ::
        [isTC1 (.var 0) (numeralM (consN 1 (consN s (consN (consN 0 0) 0))))]) (wfAll1 (.var 0)) :=
      PrfH_and_elim_left (PrfH.hyp _ (isTC1 (.var 0) (numeralM (consN 1 (consN s (consN (consN 0 0) 0)))))
        (List.Mem.tail _ (List.Mem.head _)))
    have hz := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_of_In (.var 0) zero) _) hin0) hwf
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_isTermCodeE1_zero_absurd (.var 0)) _) hz

/-! ## §5 · Control: sobre un código CANÓNICO, `¬ hasWit` no es demostrable

No mide el método sino la guarda: por la solidez (`prf_sound`) y la guarda que ya se demostraba
(`prf_hasWit_termCodeM`), `¬ hasWit` no es demostrable en `Prf` sobre el numeral del código de NINGÚN término; lo
refutado en §1–§4 depende, pues, de la basura. Sólo códigos canónicos. -/

theorem control_codigo_no_refutable (t : Term) : ¬ Prf (neg (hasWit (numeralM (codeNatTerm t)))) := by
  intro h
  have hs := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN h (fun _ => 0)
  have hw := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (ROBINSON_PlusPlus.Meta.SubstTreeReflect.prf_hasWit_termCodeM t) (fun _ => 0)
  apply hs
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWit, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_numeralM]
  rw [ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_hasWit, ROBINSON_PlusPlus.Meta.ModeloEstandar.ev_termCodeM] at hw
  exact hw

end RosserBasura

#print axioms RosserBasura.prf_neg_hasWit_zero
#print axioms RosserBasura.prf_neg_hasWit_num
#print axioms RosserBasura.prf_neg_hasWit_prof2
#print axioms RosserBasura.control_codigo_no_refutable
