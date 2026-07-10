/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalLtPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.ForallElimCodePrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.ExIntroCodePrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace ROBINSON_PlusPlus.Meta.EvalBoundedPrf

/-!
## META — NIVEL D real (§30): cuantificadores ACOTADOS a nivel de código

Los cuantificadores acotados del verificador Δ₀ son **azúcar** sobre `∧`, `⇒`, `<`, `∃`, `∀`:

```text
∃i<b. φ(i)  ≡  ∃i. (i < b) ∧ φ(i)
∀i<b. φ(i)  ≡  ∀i. (i < b) ⇒ φ(i)
```

Su reflexión al nivel de código se compone por tanto de piezas ya construidas:

* la lógica proposicional interna `∧` — **líneas‑axioma C1/C2/C3 libres de muro** (`prf_lineWF_c1`
  etc. son estructurales, igual que EQREFL/LEIBNIZ §15.4): `pcc_and_intro_code`,
  `pcc_and_elim_left_code`, `pcc_and_elim_right_code`;
* la reflexión de `<` (§29, `pcc_lt_intro` / `ltCodeFn`);
* el `∃`‑intro (§17, `pcc_exIntro_code'`) y el `∀`‑elim (§22, `pcc_forallElim_code_open`).

**Payoff:** `pcc_bdEx_intro` (introducción del `∃` acotado) y `pcc_bdAll_elim` (eliminación del `∀`
acotado), las dos reglas que la reflexión de `boundedIn`/`boundedCarcLt`/`boundedAllIn` usa. La
INTRODUCCIÓN del `∀` acotado (para `hbC`) requiere inducción acotada interna (fase estructural).
-/

/-! ### `∧` a nivel de código — líneas‑axioma C1/C2/C3, libres de muro -/

/-- **Línea‑axioma C1** (`∧`‑intro): `⟨implc a (implc b (andc a b)), 2, a, b⟩`. -/
def c1Line (a b : Term) : Term :=
  cons (implc a (implc b (andc a b))) (cons (numeralM 2) (cons a (cons b nil)))

/-- **Línea‑axioma C2** (`∧`‑elim izq): `⟨implc (andc a b) a, 3, a, b⟩`. -/
def c2Line (a b : Term) : Term :=
  cons (implc (andc a b) a) (cons (numeralM 3) (cons a (cons b nil)))

/-- **Línea‑axioma C3** (`∧`‑elim der): `⟨implc (andc a b) b, 4, a, b⟩`. -/
def c3Line (a b : Term) : Term :=
  cons (implc (andc a b) b) (cons (numeralM 4) (cons a (cons b nil)))

/-- Genérico: una línea‑axioma cuya conclusión es la cabeza `concl` (`carc line =eq concl`), con
    `lineWF` ya descargado y **sin premisas** (`premsOf =eq nil`), da `provFromCode concl`.
    Encapsula el patrón EQREFL/LEIBNIZ (§15.4). -/
private theorem pcc_axline (concl line : Term)
    (hWF : Prf (lineWF line))
    (hcarc : Prf (carc line =eq concl))
    (hprems : Prf (premsOf line =eq nil)) :
    Prf (provFromCode concl) := by
  have hlineOk : Prf (lineOk nil line) :=
    prf_and_intro hWF
      (prf_allIn_subst2 (prf_eq_symm hprems) (prf_allIn_nil nil))
  have hchain : Prf (chainOk nil (cons line nil)) :=
    prf_iff_mpr (prf_chainOk_cons nil line nil)
      (prf_and_intro hlineOk (prf_chainOk_nil _))
  have hrun : Prf (runFn nil (cons line nil) =eq cons concl nil) :=
    prf_eq_trans (prf_runFn_cons nil line nil)
      (prf_eq_trans (prf_runFn_nil _)
        (prf_eq_trans (prf_concat_nil_eq _)
          (prf_congr_cons_head hcarc)))
  exact prf_provFromCode_intro concl (cons line nil) hchain
    (prf_eq_subst_in (prf_eq_symm hrun) (prf_in_cons_head concl nil))

/-- **C1 codificado, libre de muro**: `⊢ Prov(⌜Ac ⇒ Bc ⇒ (Ac ∧ Bc)⌝)`. -/
theorem pcc_c1_code (Ac Bc : Term) :
    Prf (provFromCode (implc Ac (implc Bc (andc Ac Bc)))) :=
  pcc_axline (implc Ac (implc Bc (andc Ac Bc))) (c1Line Ac Bc)
    (prf_iff_mpr (prf_lineWF_c1 (implc Ac (implc Bc (andc Ac Bc))) Ac Bc) (prf_refl _))
    (prf_carc_cons _ _) (prf_premsOf_c1 (implc Ac (implc Bc (andc Ac Bc))) Ac Bc)

/-- **C2 codificado, libre de muro**: `⊢ Prov(⌜(Ac ∧ Bc) ⇒ Ac⌝)`. -/
theorem pcc_c2_code (Ac Bc : Term) :
    Prf (provFromCode (implc (andc Ac Bc) Ac)) :=
  pcc_axline (implc (andc Ac Bc) Ac) (c2Line Ac Bc)
    (prf_iff_mpr (prf_lineWF_c2 (implc (andc Ac Bc) Ac) Ac Bc) (prf_refl _))
    (prf_carc_cons _ _) (prf_premsOf_c2 (implc (andc Ac Bc) Ac) Ac Bc)

/-- **C3 codificado, libre de muro**: `⊢ Prov(⌜(Ac ∧ Bc) ⇒ Bc⌝)`. -/
theorem pcc_c3_code (Ac Bc : Term) :
    Prf (provFromCode (implc (andc Ac Bc) Bc)) :=
  pcc_axline (implc (andc Ac Bc) Bc) (c3Line Ac Bc)
    (prf_iff_mpr (prf_lineWF_c3 (implc (andc Ac Bc) Bc) Ac Bc) (prf_refl _))
    (prf_carc_cons _ _) (prf_premsOf_c3 (implc (andc Ac Bc) Bc) Ac Bc)

/-- **`∧`‑intro a nivel de código**: de `Prov(⌜Ac⌝)` y `Prov(⌜Bc⌝)` sale `Prov(⌜Ac ∧ Bc⌝)`. -/
theorem pcc_and_intro_code {Ac Bc : Term}
    (ha : Prf (provFromCode Ac)) (hb : Prf (provFromCode Bc)) :
    Prf (provFromCode (andc Ac Bc)) :=
  pcc_mp_code_apply (pcc_mp_code_apply (pcc_c1_code Ac Bc) ha) hb

/-- **`∧`‑elim izquierdo a nivel de código**. -/
theorem pcc_and_elim_left_code {Ac Bc : Term}
    (h : Prf (provFromCode (andc Ac Bc))) : Prf (provFromCode Ac) :=
  pcc_mp_code_apply (pcc_c2_code Ac Bc) h

/-- **`∧`‑elim derecho a nivel de código**. -/
theorem pcc_and_elim_right_code {Ac Bc : Term}
    (h : Prf (provFromCode (andc Ac Bc))) : Prf (provFromCode Bc) :=
  pcc_mp_code_apply (pcc_c3_code Ac Bc) h

/-! ### Congruencia de `andc` y cómputo de `substfc` sobre `ltCodeFn` -/

theorem prf_congr_andc {a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (andc a b =eq andc a' b') := by
  unfold andc
  exact prf_congr_cons_tail
    (prf_eq_trans (prf_congr_cons_head ha) (prf_congr_cons_tail (prf_congr_cons_head hb)))

/-- `substfc zero K (ltCodeFn ⌜v₀⌝ B) =eq ltCodeFn K B` (`⌜v₀⌝` recibe el testigo `K`;
    `B` es `substtc`‑invariante). -/
theorem prf_substfc_ltCodeFn_varc0 (B K : Term)
    (hBinv : ∀ W, Prf (substtc zero W B =eq B)) :
    Prf (substfc zero K (ltCodeFn (varc (numeral 0)) B) =eq ltCodeFn K B) := by
  have hts : Prf (substtsc zero K (cons (varc (numeral 0)) (cons B nil))
      =eq cons K (cons B nil)) :=
    prf_eq_trans (prf_substtsc_cons zero K (varc (numeral 0)) (cons B nil))
      (prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 K))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons zero K B nil)
            (prf_eq_trans (prf_congr_cons_head (hBinv K))
              (prf_congr_cons_tail (prf_substtsc_nil zero K))))))
  refine prf_eq_trans (prf_substfc_atom zero K (strCode lt_sym)
    (cons (varc (numeral 0)) (cons B nil))) ?_
  show Prf (atomc (strCode lt_sym) (substtsc zero K (cons (varc (numeral 0)) (cons B nil)))
    =eq atomc (strCode lt_sym) (cons K (cons B nil)))
  unfold atomc
  exact prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head hts))

/-! ### Constructores de código de los cuantificadores acotados -/

/-- Código de `∃i<B. φ(i)` ≡ `∃i. (i<B) ∧ φ(i)`; `Phic` es el código de `φ`, abierto en `⌜v₀⌝`;
    `B` es la cota (cerrada, no depende de `i`). -/
def bdExCode (B Phic : Term) : Term :=
  exc (andc (ltCodeFn (varc (numeral 0)) B) Phic)

/-- Código de `∀i<B. φ(i)` ≡ `∀i. (i<B) ⇒ φ(i)`. -/
def bdAllCode (B Phic : Term) : Term :=
  forallc (implc (ltCodeFn (varc (numeral 0)) B) Phic)

/-! ### `∃i<B`‑INTRO a nivel de código -/

/-- **Introducción del `∃` acotado a nivel de código**: dado un testigo `K`, `Prov(⌜K<B⌝)` y
    `Prov(⌜φ(K)⌝)`, se obtiene `Prov(⌜∃i<B. φ(i)⌝)`. Es `∧`‑intro seguido de `∃`‑intro. -/
theorem pcc_bdEx_intro (B Phic K : Term)
    (hBcl : ∀ c, liftTerm c B = B) (hBinv : ∀ W, Prf (substtc zero W B =eq B))
    (hPcl : ∀ c, liftTerm c Phic = Phic)
    (hlt : Prf (provFromCode (ltCodeFn K B)))
    (hphi : Prf (provFromCode (substfc zero K Phic))) :
    Prf (provFromCode (bdExCode B Phic)) := by
  -- (1) `∧`‑intro de las dos reflexiones
  have hand : Prf (provFromCode (andc (ltCodeFn K B) (substfc zero K Phic))) :=
    pcc_and_intro_code hlt hphi
  -- (2) `substfc zero K` sobre el cuerpo `andc (ltCodeFn ⌜v₀⌝ B) Phic`
  have hsub : Prf (substfc zero K (andc (ltCodeFn (varc (numeral 0)) B) Phic)
      =eq andc (ltCodeFn K B) (substfc zero K Phic)) :=
    prf_eq_trans (prf_substfc_and zero K _ _)
      (prf_congr_andc (prf_substfc_ltCodeFn_varc0 B K hBinv) (prf_refl _))
  have hant : Prf (provFromCode (substfc zero K (andc (ltCodeFn (varc (numeral 0)) B) Phic))) :=
    prf_mp (prf_provCode_congr (prf_eq_symm hsub)) hand
  -- (3) `∃`‑intro (el cuerpo es cerrado: `B`, `Phic` cerrados y `⌜v₀⌝` cerrado)
  have hbody : ∀ c, liftTerm c (andc (ltCodeFn (varc (numeral 0)) B) Phic)
      = andc (ltCodeFn (varc (numeral 0)) B) Phic := fun c => by
    simp only [andc, ltCodeFn, atom2CodeFn, varc, cons, nil, zero, succ, liftTerm, liftTerms,
      liftTerm_numeral, liftTerm_strCode, hBcl c, hPcl c]
  exact prf_mp (pcc_exIntro_code' (andc (ltCodeFn (varc (numeral 0)) B) Phic) K hbody) hant

/-! ### `∀i<B`‑ELIM a nivel de código -/

/-- **Eliminación del `∀` acotado a nivel de código**: de `Prov(⌜∀i<B. φ(i)⌝)` y un testigo `K` con
    `Prov(⌜K<B⌝)`, se obtiene `Prov(⌜φ(K)⌝)`. Es `∀`‑elim seguido de MP interno. -/
theorem pcc_bdAll_elim (B Phic K : Term)
    (hBinv : ∀ W, Prf (substtc zero W B =eq B))
    (hall : Prf (provFromCode (bdAllCode B Phic)))
    (hlt : Prf (provFromCode (ltCodeFn K B))) :
    Prf (provFromCode (substfc zero K Phic)) := by
  -- (1) `∀`‑elim con testigo `K`
  have helim : Prf (provFromCode (substfc zero K (implc (ltCodeFn (varc (numeral 0)) B) Phic))) :=
    prf_mp (pcc_forallElim_code_open (implc (ltCodeFn (varc (numeral 0)) B) Phic) K) hall
  -- (2) `substfc zero K` distribuye sobre el `implc`
  have hsub : Prf (substfc zero K (implc (ltCodeFn (varc (numeral 0)) B) Phic)
      =eq implc (ltCodeFn K B) (substfc zero K Phic)) :=
    prf_eq_trans (prf_substfc_impl zero K _ _)
      (prf_congr_implc (prf_substfc_ltCodeFn_varc0 B K hBinv) (prf_refl _))
  have himp : Prf (provFromCode (implc (ltCodeFn K B) (substfc zero K Phic))) :=
    prf_mp (prf_provCode_congr hsub) helim
  -- (3) MP interno con `Prov(⌜K<B⌝)`
  exact pcc_mp_code_apply himp hlt

end ROBINSON_PlusPlus.Meta.EvalBoundedPrf

export ROBINSON_PlusPlus.Meta.EvalBoundedPrf (
  c1Line c2Line c3Line pcc_c1_code pcc_c2_code pcc_c3_code
  pcc_and_intro_code pcc_and_elim_left_code pcc_and_elim_right_code
  prf_congr_andc prf_substfc_ltCodeFn_varc0
  bdExCode bdAllCode pcc_bdEx_intro pcc_bdAll_elim
)
