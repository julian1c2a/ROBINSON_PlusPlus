/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.D3BodyPrf

/-!
# B3 · EL `pcc_bdAll_intro` **INTERIOR** de `boundedPremsIn`

El `∀` acotado de `boundedPremsIn` es el **segundo** chasis de D3, anidado dentro del de
`chainOkB`. §7.2 de `D3ChainDotPrf` midió que los dos `PsiF` hay que diseñarlos **JUNTOS y de
fuera adentro**; el exterior está desde §8, y el interior sale de él como **sub-término** —
`premsPsi` (`Meta/D3BodyPrf.lean` §3), casado con el destino por `rfl`.

## ⭐⭐ ADR-021 se cumple **sola** aquí, y conviene decir por qué

En el chasis EXTERIOR la obligación `hPl` era **FALSA** para el `PsiF` que casaba el destino, y de
ahí salió ADR-021: hubo que escribir un `PsiF` **dotado** y puentear dentro de `Prov`. Aquí **no
hace falta**, y la razón es estructural:

> En `premsPsi q i = substCodeF2 1 (liftc 0 i̇) (liftc 0 (liftc 0 q̇)) premsBodyF`, el cuerpo
> `premsBodyF` es una fórmula **CERRADA** (menciona sólo `#0`, `#1`, `#2`) y los parámetros entran
> **sólo como TESTIGOS**.

En el exterior, `q` aparecía **dentro** de la fórmula que se codifica, y `substCodeF` manda cada
variable al hueco o a un `varc` cerrado **según su nivel** ⇒ el `liftTerm` la movía fuera del
hueco. ⇒ 🔑 **La regla de ADR-021 se afina**: lo que rompe la naturalidad no es «ser un
`substCodeF`», es que **el parámetro viaje dentro de la fórmula**.

## Lo que este módulo aporta

* **`liftTerm_substCodeF2` / `substTerm_substCodeF2`** (+ los gemelos de términos): la naturalidad
  de `substCodeF2` en sus **dos** testigos. No existían.
* ⭐ **`substfc_id_substCodeF2`** — la **CUARTA** variante de la familia `substfc_inv_*`: nivel
  actuante uno por debajo del **más bajo** de los dos huecos. ⚠️ Y el índice sigue sin ser
  cosmético: la guarda pasa de `liftFormula (v+2)` a **`liftFormula (v+3)`**, porque entre el
  nivel actuante y el hueco alto hay **dos** casillas.
* Las **ocho** obligaciones administrativas del chasis interior, sobre el triple empaquetado.
* El ensamblaje `hbdAllPrems_of_body`, que deja **una sola** obligación abierta —
  `DEUDA_premsBody`, el cuerpo del `∀` interior — **enunciada, no postulada**.

**Footprint**: la base sancionada.
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
open ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.PremsOfDotPrf
open ROBINSON_PlusPlus.Meta.D3ChainDotPrf
open ROBINSON_PlusPlus.Meta.D3BodyPrf
open ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
open ROBINSON_PlusPlus.Meta.TrackedAtomsPrf

set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace ROBINSON_PlusPlus.Meta.PremsBdAllPrf


/-! ## §1 · NATURALIDAD DE `substCodeF2` EN SUS DOS TESTIGOS

⭐ **Es lo que hace que ADR‑021 se cumpla sola aquí**: en `premsPsi q i` los parámetros entran
**sólo como testigos** (el cuerpo `BODY` es una fórmula CERRADA), y `substCodeF2` es natural en
ellos. En el chasis EXTERIOR no lo era porque allí `q` aparecía **dentro de la fórmula**. -/

theorem liftTerm_nil (k : Nat) : liftTerm k nil = nil := rfl

theorem liftTerm_liftc (k : Nat) (x : Term) :
    liftTerm k (liftc zero x) = liftc zero (liftTerm k x) := rfl

mutual

theorem liftTerm_substCodeT2 (k v : Nat) (u W : Term) : ∀ t : Term,
    liftTerm k (substCodeT2 v u W t) = substCodeT2 v (liftTerm k u) (liftTerm k W) t
  | .var n => by
      simp only [substCodeT2]
      rcases Nat.decEq n (v + 1) with h1 | h1
      · rcases Nat.decEq n v with h2 | h2
        · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
          by_cases h3 : n > v + 1 <;> simp only [if_pos, if_neg, h3, reduceIte] <;>
            simp only [varc, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral]
        · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
      · rw [if_pos h1, if_pos h1]
  | .func sym ts => by
      simp only [substCodeT2, funcc, cons, nil, zero, succ, liftTerm, liftTerms,
        liftTerm_strCode, liftTerms_substCodeTs2 k v u W ts]

theorem liftTerms_substCodeTs2 (k v : Nat) (u W : Term) : ∀ ts : List Term,
    liftTerm k (substCodeTs2 v u W ts) = substCodeTs2 v (liftTerm k u) (liftTerm k W) ts
  | [] => by simp only [substCodeTs2, nil, zero, liftTerm, liftTerms]
  | t :: ts => by
      simp only [substCodeTs2, cons, liftTerm, liftTerms,
        liftTerm_substCodeT2 k v u W t, liftTerms_substCodeTs2 k v u W ts]

end

theorem liftTerm_substCodeF2 (k v : Nat) (u W : Term) : ∀ φ : Formula,
    liftTerm k (substCodeF2 v u W φ) = substCodeF2 v (liftTerm k u) (liftTerm k W) φ
  | .bottom => by simp only [substCodeF2, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral]
  | .atom P ts => by
      simp only [substCodeF2, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral,
        liftTerm_strCode, liftTerms_substCodeTs2 k v u W ts]
  | .eq a b => by
      simp only [substCodeF2, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral,
        liftTerm_substCodeT2 k v u W a, liftTerm_substCodeT2 k v u W b]
  | .impl a b => by
      simp only [substCodeF2, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral,
        liftTerm_substCodeF2 k v u W a, liftTerm_substCodeF2 k v u W b]
  | .and a b => by
      simp only [substCodeF2, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral,
        liftTerm_substCodeF2 k v u W a, liftTerm_substCodeF2 k v u W b]
  | .or a b => by
      simp only [substCodeF2, cons, nil, zero, liftTerm, liftTerms, liftTerm_numeral,
        liftTerm_substCodeF2 k v u W a, liftTerm_substCodeF2 k v u W b]
  | Formula.forall a => by
      simp only [substCodeF2, cons, liftTerm, liftTerms, liftTerm_numeral, liftTerm_nil,
        liftTerm_substCodeF2 k (v + 1) (liftc zero u) (liftc zero W) a, liftTerm_liftc]
  | .ex a => by
      simp only [substCodeF2, cons, liftTerm, liftTerms, liftTerm_numeral, liftTerm_nil,
        liftTerm_substCodeF2 k (v + 1) (liftc zero u) (liftc zero W) a, liftTerm_liftc]


/-! ### El gemelo para `substTerm` -/

theorem substTerm_nil (v : Nat) (s : Term) : substTerm v s nil = nil := rfl

theorem substTerm_liftc (v : Nat) (s x : Term) :
    substTerm v s (liftc zero x) = liftc zero (substTerm v s x) := rfl

mutual

theorem substTerm_substCodeT2 (c v : Nat) (s u W : Term) : ∀ t : Term,
    substTerm c s (substCodeT2 v u W t) = substCodeT2 v (substTerm c s u) (substTerm c s W) t
  | .var n => by
      simp only [substCodeT2]
      rcases Nat.decEq n (v + 1) with h1 | h1
      · rcases Nat.decEq n v with h2 | h2
        · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
          by_cases h3 : n > v + 1 <;> simp only [if_pos, if_neg, h3, reduceIte] <;>
            simp only [varc, cons, nil, zero, substTerm, substTerms, substTerm_numeral]
        · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
      · rw [if_pos h1, if_pos h1]
  | .func sym ts => by
      simp only [substCodeT2, funcc, cons, nil, zero, succ, substTerm, substTerms,
        substTerm_strCode, substTerms_substCodeTs2 c v s u W ts]

theorem substTerms_substCodeTs2 (c v : Nat) (s u W : Term) : ∀ ts : List Term,
    substTerm c s (substCodeTs2 v u W ts) = substCodeTs2 v (substTerm c s u) (substTerm c s W) ts
  | [] => by simp only [substCodeTs2, nil, zero, substTerm, substTerms]
  | t :: ts => by
      simp only [substCodeTs2, cons, substTerm, substTerms,
        substTerm_substCodeT2 c v s u W t, substTerms_substCodeTs2 c v s u W ts]

end

theorem substTerm_substCodeF2 (c v : Nat) (s u W : Term) : ∀ φ : Formula,
    substTerm c s (substCodeF2 v u W φ) = substCodeF2 v (substTerm c s u) (substTerm c s W) φ
  | .bottom => by simp only [substCodeF2, cons, nil, zero, substTerm, substTerms, substTerm_numeral]
  | .atom P ts => by
      simp only [substCodeF2, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_strCode, substTerms_substCodeTs2 c v s u W ts]
  | .eq a b => by
      simp only [substCodeF2, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_substCodeT2 c v s u W a, substTerm_substCodeT2 c v s u W b]
  | .impl a b => by
      simp only [substCodeF2, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_substCodeF2 c v s u W a, substTerm_substCodeF2 c v s u W b]
  | .and a b => by
      simp only [substCodeF2, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_substCodeF2 c v s u W a, substTerm_substCodeF2 c v s u W b]
  | .or a b => by
      simp only [substCodeF2, cons, nil, zero, substTerm, substTerms, substTerm_numeral,
        substTerm_substCodeF2 c v s u W a, substTerm_substCodeF2 c v s u W b]
  | Formula.forall a => by
      simp only [substCodeF2, cons, substTerm, substTerms, substTerm_numeral, substTerm_nil,
        substTerm_substCodeF2 c (v + 1) s (liftc zero u) (liftc zero W) a, substTerm_liftc]
  | .ex a => by
      simp only [substCodeF2, cons, substTerm, substTerms, substTerm_numeral, substTerm_nil,
        substTerm_substCodeF2 c (v + 1) s (liftc zero u) (liftc zero W) a, substTerm_liftc]

/-! ## §2 · `premsPsi` ES NATURAL — ADR-021 se cumple **sola** aquí

⚠️ **Y conviene decir por qué**, porque en el chasis EXTERIOR (§10 de `D3ChainDotPrf`) la misma
obligación era **FALSA**. Allí el parámetro `q` aparecía **dentro de la fórmula** que se codifica
(`lineOkB nil (liftTerm 0 q) #0`), y `substCodeF` manda cada variable al hueco o a un `varc`
cerrado **según su nivel**. Aquí el cuerpo es una fórmula **CERRADA** (sólo `#0`, `#1`, `#2`) y
los parámetros entran **sólo como testigos** ⇒ `substCodeF2` es natural en ellos. -/

theorem hPl_premsPsi (k : Nat) (q i : Term) :
    liftTerm k (premsPsi q i) = premsPsi (liftTerm k q) (liftTerm k i) := by
  simp only [premsPsi, liftTerm_substCodeF2, liftTerm_liftc, tcFn, liftTerm, liftTerms]

theorem hPs_premsPsi (v : Nat) (s q i : Term) :
    substTerm v s (premsPsi q i) = premsPsi (substTerm v s q) (substTerm v s i) := by
  simp only [premsPsi, substTerm_substCodeF2, substTerm_liftc, tcFn, substTerm, substTerms]

/-! ## §3 · EL PAQUETE y el `PsiF` del chasis interior -/

/-- El `PsiF` del chasis interior: el cuerpo del `∀` de `boundedPremsIn`, leído del paquete. -/
noncomputable def premsPsiPk (r : Term) : Term := premsPsi (carc r) (cdrc r)

theorem hPl_premsPsiPk (k : Nat) (r : Term) :
    liftTerm k (premsPsiPk r) = premsPsiPk (liftTerm k r) := by
  simp only [premsPsiPk, hPl_premsPsi, carc, cdrc, liftTerm, liftTerms]

theorem hPs_premsPsiPk (v : Nat) (s r : Term) :
    substTerm v s (premsPsiPk r) = premsPsiPk (substTerm v s r) := by
  simp only [premsPsiPk, hPs_premsPsi, carc, cdrc, substTerm, substTerms]

/-- `CF` del chasis interior: las DOS hipótesis, empaquetadas. -/
def premsCF (r : Term) : Formula := land (chainOk nil (carc r)) (lt (cdrc r) (lenc (carc r)))

theorem hCl_premsCF (k : Nat) (r : Term) :
    liftFormula k (premsCF r) = premsCF (liftTerm k r) := by
  simp only [premsCF, land, chainOk, lt, lenc, carc, cdrc, nil, zero,
    liftFormula, liftTerm, liftTerms]

theorem hCs_premsCF (v : Nat) (s r : Term) :
    substFormula v s (premsCF r) = premsCF (substTerm v s r) := by
  simp only [premsCF, land, chainOk, lt, lenc, carc, cdrc, nil, zero,
    substFormula, substTerm, substTerms]

/-- `bndF` del chasis interior: la longitud de las premisas de la línea `i`-ésima. -/
def premsBnd (r : Term) : Term := lenc (premsOf (nthc (carc r) (cdrc r)))

theorem hbl_premsBnd (k : Nat) (r : Term) :
    liftTerm k (premsBnd r) = premsBnd (liftTerm k r) := by
  simp only [premsBnd, lenc, premsOf, nthc, carc, cdrc, liftTerm, liftTerms]

theorem hbs_premsBnd (v : Nat) (s r : Term) :
    substTerm v s (premsBnd r) = premsBnd (substTerm v s r) := by
  simp only [premsBnd, lenc, premsOf, nthc, carc, cdrc, substTerm, substTerms]


/-! ## §4 · `hPsiId` PARA DOS HUECOS — la CUARTA variante de la familia

§11 de `D3ChainDotPrf` necesitó la **tercera** variante (`substfc_id_substCodeF`: nivel actuante
uno por debajo del hueco). El chasis INTERIOR tiene **dos** huecos, así que hace falta la cuarta:
nivel actuante uno por debajo del **más bajo** de los dos.

⚠️ Y el índice sigue sin ser cosmético, ahora con más razón: la guarda pasa de `liftFormula (v+2)`
a **`liftFormula (v+3)`**, porque entre el nivel actuante y el hueco alto hay **dos** casillas. Con
`v := 0` eso dice exactamente que el cuerpo menciona a lo sumo `#0`, `#1`, `#2` — que es lo que
`boundedPremsIn` cumple. -/

mutual

theorem substtc_id_substCodeT2 (v : Nat) (u0 W : Term)
    (hu0 : ∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w u0 =eq u0))
    (hW : ∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w W =eq W)) :
    ∀ (t : Term), liftTerm (v + 3) t = t →
      ∀ u, Prf (u =eq varc (numeral v)) →
        Prf (substtc (numeral v) u (substCodeT2 (v + 1) u0 W t)
          =eq substCodeT2 (v + 1) u0 W t)
  | .var n, hfv, u, hu => by
      have hn : Nat.le n (v + 2) := by
        rcases Nat.lt_or_ge n (v + 3) with h | h
        · exact Nat.le_of_lt_succ h
        · have hne : ¬ (n < v + 3) := Nat.not_lt.mpr h
          simp only [liftTerm, if_neg hne, Term.var.injEq] at hfv
          exact absurd hfv (Nat.succ_ne_self n)
      rcases Nat.lt_or_ge n (v + 1) with hlt | hge
      · -- n ≤ v : casilla de variable de código CERRADA
        have hsub : substCodeT2 (v + 1) u0 W (.var n) = varc (numeral n) := by
          simp only [substCodeT2]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [hsub]
        rcases Nat.lt_or_ge n v with hlt2 | hge2
        · exact prf_mp (prf_substtc_var_lt (numeral v) u (numeral n)) (prf_gnum_lt (by omega))
        · have hnv : n = v := by omega
          subst hnv
          exact prf_eq_trans
            (prf_mp (prf_substtc_var_eq (numeral n) u (numeral n)) (prf_refl (numeral n))) hu
      · rcases Nat.lt_or_ge n (v + 2) with hlt3 | hge3
        · -- n = v+1 : el hueco BAJO
          have hnv : n = v + 1 := by omega
          subst hnv
          have hsub : substCodeT2 (v + 1) u0 W (.var (v + 1)) = u0 := by
            simp only [substCodeT2]; rw [if_neg (by omega)]; simp
          rw [hsub]; exact hu0 v u
        · -- n = v+2 : el hueco ALTO
          have hnv : n = v + 2 := Nat.le_antisymm hn hge3
          subst hnv
          have hsub : substCodeT2 (v + 1) u0 W (.var (v + 2)) = W := by
            simp only [substCodeT2]; simp
          rw [hsub]; exact hW v u
  | .func sym ts, hfv, u, hu => by
      have hall := hfv
      simp only [liftTerm, Term.func.injEq, true_and] at hall
      show Prf (substtc (numeral v) u (funcc (strCode sym) (substCodeTs2 (v + 1) u0 W ts))
        =eq funcc (strCode sym) (substCodeTs2 (v + 1) u0 W ts))
      refine prf_eq_trans (prf_substtc_func (numeral v) u _ _) ?_
      unfold funcc
      refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
      exact substtc_id_substCodeTs2 v u0 W hu0 hW ts hall u hu

theorem substtc_id_substCodeTs2 (v : Nat) (u0 W : Term)
    (hu0 : ∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w u0 =eq u0))
    (hW : ∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w W =eq W)) :
    ∀ (ts : List Term), liftTerms (v + 3) ts = ts →
      ∀ u, Prf (u =eq varc (numeral v)) →
        Prf (substtsc (numeral v) u (substCodeTs2 (v + 1) u0 W ts)
          =eq substCodeTs2 (v + 1) u0 W ts)
  | [], _, u, _ => by
      show Prf (substtsc (numeral v) u nil =eq nil)
      exact prf_substtsc_nil (numeral v) u
  | t :: ts, hfv, u, hu => by
      have h1 := hfv
      simp only [liftTerms, List.cons.injEq] at h1
      show Prf (substtsc (numeral v) u
          (cons (substCodeT2 (v + 1) u0 W t) (substCodeTs2 (v + 1) u0 W ts))
        =eq cons (substCodeT2 (v + 1) u0 W t) (substCodeTs2 (v + 1) u0 W ts))
      refine prf_eq_trans (prf_substtsc_cons (numeral v) u _ _) ?_
      exact prf_eq_trans
        (prf_congr_cons_head (substtc_id_substCodeT2 v u0 W hu0 hW t h1.1 u hu))
        (prf_congr_cons_tail (substtc_id_substCodeTs2 v u0 W hu0 hW ts h1.2 u hu))

end

theorem substfc_id_substCodeF2 : ∀ (v : Nat) (u0 W : Term),
    (∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w u0 =eq u0)) →
    Prf (liftc zero u0 =eq u0) →
    (∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w W =eq W)) →
    Prf (liftc zero W =eq W) →
    ∀ (φ : Formula), liftFormula (v + 3) φ = φ →
      ∀ u, Prf (u =eq varc (numeral v)) →
        Prf (substfc (numeral v) u (substCodeF2 (v + 1) u0 W φ)
          =eq substCodeF2 (v + 1) u0 W φ)
  | v, u0, W, _, _, _, _, .bottom, _, u, _ => by
      show Prf (substfc (numeral v) u botc =eq botc)
      exact prf_substfc_bottom (numeral v) u
  | v, u0, W, hu0, _, hW, _, .atom P ts, hfv, u, hu => by
      have hts : liftTerms (v + 3) ts = ts := by
        simpa only [liftFormula, Formula.atom.injEq, true_and] using hfv
      show Prf (substfc (numeral v) u (atomc (strCode P) (substCodeTs2 (v + 1) u0 W ts))
        =eq atomc (strCode P) (substCodeTs2 (v + 1) u0 W ts))
      refine prf_eq_trans (prf_substfc_atom (numeral v) u _ _) ?_
      unfold atomc
      refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
      exact substtc_id_substCodeTs2 v u0 W hu0 hW ts hts u hu
  | v, u0, W, hu0, _, hW, _, .eq a b, hfv, u, hu => by
      have h1 := hfv
      simp only [liftFormula, Formula.eq.injEq] at h1
      show Prf (substfc (numeral v) u
          (eqCodeFn (substCodeT2 (v + 1) u0 W a) (substCodeT2 (v + 1) u0 W b))
        =eq eqCodeFn (substCodeT2 (v + 1) u0 W a) (substCodeT2 (v + 1) u0 W b))
      refine prf_eq_trans (prf_substfc_eq (numeral v) u _ _) ?_
      exact prf_congr_eqCodeFn (substtc_id_substCodeT2 v u0 W hu0 hW a h1.1 u hu)
        (substtc_id_substCodeT2 v u0 W hu0 hW b h1.2 u hu)
  | v, u0, W, hu0, hLu, hW, hL, .impl a b, hfv, u, hu => by
      have h1 := hfv
      simp only [liftFormula, Formula.impl.injEq] at h1
      show Prf (substfc (numeral v) u
          (implc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
        =eq implc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
      refine prf_eq_trans (prf_substfc_impl (numeral v) u _ _) ?_
      exact prf_congr_implc (substfc_id_substCodeF2 v u0 W hu0 hLu hW hL a h1.1 u hu)
        (substfc_id_substCodeF2 v u0 W hu0 hLu hW hL b h1.2 u hu)
  | v, u0, W, hu0, hLu, hW, hL, .and a b, hfv, u, hu => by
      have h1 := hfv
      simp only [liftFormula, Formula.and.injEq] at h1
      show Prf (substfc (numeral v) u
          (andc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
        =eq andc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
      refine prf_eq_trans (prf_substfc_and (numeral v) u _ _) ?_
      exact prf_congr_andc (substfc_id_substCodeF2 v u0 W hu0 hLu hW hL a h1.1 u hu)
        (substfc_id_substCodeF2 v u0 W hu0 hLu hW hL b h1.2 u hu)
  | v, u0, W, hu0, hLu, hW, hL, .or a b, hfv, u, hu => by
      have h1 := hfv
      simp only [liftFormula, Formula.or.injEq] at h1
      show Prf (substfc (numeral v) u
          (orc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
        =eq orc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
      refine prf_eq_trans (prf_substfc_or (numeral v) u _ _) ?_
      exact prf_congr_orc (substfc_id_substCodeF2 v u0 W hu0 hLu hW hL a h1.1 u hu)
        (substfc_id_substCodeF2 v u0 W hu0 hLu hW hL b h1.2 u hu)
  | v, u0, W, hu0, hLu, hW, hL, Formula.forall a, hfv, u, hu => by
      have h1 : liftFormula (v + 4) a = a := by
        simpa only [liftFormula, Formula.forall.injEq] using hfv
      show Prf (substfc (numeral v) u
          (forallc (substCodeF2 (v + 2) (liftc zero u0) (liftc zero W) a))
        =eq forallc (substCodeF2 (v + 2) (liftc zero u0) (liftc zero W) a))
      refine prf_eq_trans (prf_substfc_forall (numeral v) u _) ?_
      unfold forallc
      refine prf_congr_cons_tail (prf_congr_cons_head ?_)
      obtain ⟨hu0', hLu'⟩ := substCode_hyps_lift hu0 hLu
      obtain ⟨hW', hL'⟩ := substCode_hyps_lift hW hL
      have hu' : Prf (liftc zero u =eq varc (numeral (v + 1))) :=
        prf_eq_trans (prf_congr_liftc hu) (prf_liftc_varc_numeral v)
      exact substfc_id_substCodeF2 (v + 1) (liftc zero u0) (liftc zero W)
        hu0' hLu' hW' hL' a h1 (liftc zero u) hu'
  | v, u0, W, hu0, hLu, hW, hL, .ex a, hfv, u, hu => by
      have h1 : liftFormula (v + 4) a = a := by
        simpa only [liftFormula, Formula.ex.injEq] using hfv
      show Prf (substfc (numeral v) u
          (exc (substCodeF2 (v + 2) (liftc zero u0) (liftc zero W) a))
        =eq exc (substCodeF2 (v + 2) (liftc zero u0) (liftc zero W) a))
      refine prf_eq_trans (prf_substfc_ex (numeral v) u _) ?_
      unfold exc
      refine prf_congr_cons_tail (prf_congr_cons_head ?_)
      obtain ⟨hu0', hLu'⟩ := substCode_hyps_lift hu0 hLu
      obtain ⟨hW', hL'⟩ := substCode_hyps_lift hW hL
      have hu' : Prf (liftc zero u =eq varc (numeral (v + 1))) :=
        prf_eq_trans (prf_congr_liftc hu) (prf_liftc_varc_numeral v)
      exact substfc_id_substCodeF2 (v + 1) (liftc zero u0) (liftc zero W)
        hu0' hLu' hW' hL' a h1 (liftc zero u) hu'


/-! ## §5 · `hPsiId` y `hwPsi` PARA `premsPsi` -/

/-- El cuerpo del `∀` de `boundedPremsIn` no menciona variables `≥ 3`. -/
def premsBodyF : Formula :=
  lor (In (nthc (liftTerm 0 (premsOf (nthc (.var 1) (.var 0)))) (.var 0)) (liftTerm 0 nil))
      (boundedCarcLt (nthc (liftTerm 0 (premsOf (nthc (.var 1) (.var 0)))) (.var 0))
        (liftTerm 0 (.var 1)) (liftTerm 0 (.var 0)))

theorem premsPsi_eq (q i : Term) :
    premsPsi q i = substCodeF2 1 (liftc zero (tcFn i)) (liftc zero (liftc zero (tcFn q)))
      premsBodyF := rfl

theorem hfv_premsBodyF : liftFormula 3 premsBodyF = premsBodyF := by
  simp only [premsBodyF, lor, In, boundedCarcLt, nthc, premsOf, carc, lt, nil, zero, succ,
    land, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT, reduceIte]

/-- Las dos hipótesis del testigo BAJO (el de `i`). -/
theorem hu0_premsPsi (i : Term) : ∀ (k : Nat) (w : Term),
    Prf (substtc (numeral k) w (liftc zero (tcFn i)) =eq liftc zero (tcFn i)) :=
  hW_chainOkBPsi i

theorem hLu0_premsPsi (i : Term) :
    Prf (liftc zero (liftc zero (tcFn i)) =eq liftc zero (tcFn i)) := hL_chainOkBPsi i

/-- Y las del testigo ALTO (el de `q`), que lleva **una capa más** de `liftc`. -/
theorem hW_premsPsi (q : Term) : ∀ (k : Nat) (w : Term),
    Prf (substtc (numeral k) w (liftc zero (liftc zero (tcFn q)))
      =eq liftc zero (liftc zero (tcFn q))) :=
  (substCode_hyps_lift (hW_chainOkBPsi q) (hL_chainOkBPsi q)).1

theorem hLW_premsPsi (q : Term) :
    Prf (liftc zero (liftc zero (liftc zero (tcFn q)))
      =eq liftc zero (liftc zero (tcFn q))) :=
  (substCode_hyps_lift (hW_chainOkBPsi q) (hL_chainOkBPsi q)).2

/-- 🏁 **`hPsiId` del chasis INTERIOR**, por la cuarta variante. -/
theorem hPsiId_premsPsi (q i : Term) :
    Prf (substfc zero (varc (numeral 0)) (premsPsi q i) =eq premsPsi q i) :=
  substfc_id_substCodeF2 0 (liftc zero (tcFn i)) (liftc zero (liftc zero (tcFn q)))
    (hu0_premsPsi i) (hLu0_premsPsi i) (hW_premsPsi q) (hLW_premsPsi q)
    premsBodyF hfv_premsBodyF (varc (numeral 0)) (prf_refl _)

theorem hPsiId_premsPsiPk (r : Term) :
    Prf (substfc zero (varc (numeral 0)) (premsPsiPk r) =eq premsPsiPk r) :=
  hPsiId_premsPsi (carc r) (cdrc r)


/-! ## §6 · `hwPsi` — el TESTIGO del cuerpo interior

⭐ Sale por el mismo dividendo que §10.4 del exterior: **abrir el `substCodeF2` hacia su forma
DOTADA** (dos `substfc` anidados sobre un `formCode` cerrado) y aplicar dos veces la rama C de
ADR-020. Es la cuarta vez que el par dotado/computable paga en este frente. -/

/-- ⭐ El puente `dotado ↦ computable` del cuerpo interior: los dos `substfc` compuestos. -/
theorem premsPsi_dot_eq (q i : Term) :
    Prf (substfc (numeral 1) (liftc zero (tcFn i))
        (substfc (numeral 2) (liftc zero (liftc zero (tcFn q))) (formCode premsBodyF))
      =eq premsPsi q i) :=
  prf_eq_trans
    (prf_congr_substfc3
      (prf_substfc_arith_open 2 (liftc zero (liftc zero (tcFn q))) premsBodyF))
    (substfc_comp_substCodeF 1 (liftc zero (tcFn i)) (liftc zero (liftc zero (tcFn q)))
      (hW_premsPsi q) (hLW_premsPsi q) premsBodyF hfv_premsBodyF)

theorem hwS_liftc_tcFn (x : Term) : Prf (hasWit (liftc zero (tcFn x))) :=
  prf_mp (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.CRIT_hasWit_lift (tcFn x))
    (ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_hasWit_tcFn x)

theorem hwS_liftc2_tcFn (x : Term) : Prf (hasWit (liftc zero (liftc zero (tcFn x)))) :=
  prf_mp (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.CRIT_hasWit_lift (liftc zero (tcFn x)))
    (hwS_liftc_tcFn x)

/-- 🏁 **`hwPsi` del chasis INTERIOR.** -/
theorem hwPsi_premsPsi (q i : Term) : Prf (hasWitF (premsPsi q i)) := by
  have hdot : Prf (hasWitF (substfc (numeral 1) (liftc zero (tcFn i))
      (substfc (numeral 2) (liftc zero (liftc zero (tcFn q))) (formCode premsBodyF)))) :=
    prf_mp (prf_mp (prf_hasWitF_substfc (numeral 1) (liftc zero (tcFn i)) _)
      (prf_mp (prf_mp (prf_hasWitF_substfc (numeral 2)
          (liftc zero (liftc zero (tcFn q))) (formCode premsBodyF))
        (ROBINSON_PlusPlus.Meta.Representability2.prf_hasWitF_fc _)) (hwS_liftc2_tcFn q)))
      (hwS_liftc_tcFn i)
  exact prf_congr_hasWitF (premsPsi_dot_eq q i) hdot

theorem hwPsi_premsPsiPk (r : Term) : Prf (hasWitF (premsPsiPk r)) :=
  hwPsi_premsPsi (carc r) (cdrc r)


/-! ## §7 · EL CHASIS INTERIOR, con OCHO de sus nueve obligaciones -/

/-- La NOVENA obligación. ⚠️ **HISTÓRICO**: se enunció como deuda y quedó **PROBADA el mismo
    día** (§9bis.8, `premsBody_deuda`). Se conserva el `abbrev` porque es la forma en que
    `hbdAllPrems_of_body` la consume. -/
abbrev DEUDA_premsBody : Prop :=
  ∀ r j : Term, Prf (premsCF r ⇒ (lt j (premsBnd r) ⇒
    provFromCode (substfc zero (tcFn j) (premsPsiPk r))))

/-- ⭐⭐ **`pcc_bdAll_intro` INTERIOR**, con las ocho administrativas descargadas. -/
theorem hbdAllPrems_of_body (hbody : DEUDA_premsBody) (r : Term) :
    Prf (premsCF r ⇒ provFromCode (bdAllCode (tcFn (premsBnd r)) (premsPsiPk r))) :=
  pcc_bdAll_intro premsCF premsBnd premsPsiPk r
    hCl_premsCF hCs_premsCF hbl_premsBnd hbs_premsBnd
    hPl_premsPsiPk hPs_premsPsiPk hPsiId_premsPsiPk hwPsi_premsPsiPk hbody

/-! ### §7.1 · Los PUENTES DEL PAQUETE

⚠️ §7 de `D3ChainDotPrf` lo dejó medido: `carc (cons q i) ≐ q` **no es `rfl`** — `carc` es un
símbolo de función OBJETO. Los puentes hay que arrastrarlos. -/

theorem prf_pkQ (q i : Term) : Prf (carc (cons q i) =eq q) := prf_carc_cons q i
theorem prf_pkI (q i : Term) : Prf (cdrc (cons q i) =eq i) := prf_cdrc_cons q i


/-! ### §7.2 · ⚠️ ESTA SECCIÓN ERA UNA PREVISIÓN — y se cumplió **el mismo día**

Decía que `DEUDA_premsBody` era «lo único que queda de D3» y trazaba su ruta. **La ruta era
correcta** y está ejecutada en §9bis. Se conserva porque su valor es de método: una obstrucción
**bien medida** se convierte en el guion de la prueba.

**Lo que la previsión acertó, punto por punto:**
* el disyunto **izquierdo** es vacuo y su código queda **arbitrario** (§9bis.8);
* el **derecho** lo refleja `pcc_bdCarcLt_reflect`, **generalizado en su `Phic`** (§9bis.3);
* la fricción es **la MONEDA de §3.55.2 por cuarta vez**, y sus dos piezas ya existían
  (§9bis.4, §9bis.7);
* el sitio donde el salto **sí** se puede dar es la obligación `hphi`, con el binder **ya
  abierto** (§9bis.7).

**Lo que la previsión NO vio, y salió al escribir** — tres cosas, todas de forma:
* ⚠️ `hphi` necesita la cota `j < lenc L`, que **no viajaba** por el genérico ⇒ hubo que darle una
  **hipótesis extra `A`** que atraviese el `∃`‑elim;
* ⚠️ dejar que `rfl` case `liftTerm 0 (miPhiAt …)` hace que Lean despliegue `strCode "premsOf"`
  **carácter a carácter** y agota los heartbeats: hay que dárselo por **lemas**;
* ⚠️ al desempaquetar con Leibniz, el argumento que **no** se sustituye puede mencionar `#0` ⇒ hay
  que protegerlo con `liftTerm 0`, o el lema es **FALSO**. -/

/-! # §9bis · 🏁 LA NOVENA OBLIGACIÓN, PROBADA (2026‑09‑10g) -/


/-! ## §1 · LA MEDICIÓN DEL CUERPO INTERIOR — `rfl` o nada -/

/-- Abreviaturas de los dos testigos, con las capas de `liftc` que impone la posición. -/
noncomputable def WQ (q : Term) : Term := liftc zero (liftc zero (tcFn q))
noncomputable def UI (i : Term) : Term := liftc zero (tcFn i)

/-- ⭐ El cuerpo del `∀` interior **se parte por el `lor`**, y el disyunto derecho es un
    `bdExCode` cuya cota y cuyo `Phic` quedan a la vista. -/
theorem premsPsi_split (q i : Term) :
    premsPsi q i
      = orc (substCodeF2 1 (UI i) (WQ q)
              (In (nthc (premsOf (nthc (.var 2) (.var 1))) (.var 0)) nil))
            (bdExCode (liftc zero (UI i))
              (eqCodeFn (carcT (nthcT (liftc zero (WQ q)) (varc (numeral 0))))
                (nthcT (premsOfT (nthcT (liftc zero (WQ q)) (liftc zero (UI i))))
                  (varc (numeral 1))))) := rfl


/-! ## §2 · EL `substfc` DEL ÍNDICE — el cuerpo, ya instanciado en `j` -/

/-- La cota del `∃` interior. -/
noncomputable def miB (i : Term) : Term := liftc zero (UI i)

/-- El `Phic` del `∃` interior, **antes** de instanciar el índice del `∀`. -/
noncomputable def miPhi (q i : Term) : Term :=
  eqCodeFn (carcT (nthcT (liftc zero (WQ q)) (varc (numeral 0))))
    (nthcT (premsOfT (nthcT (liftc zero (WQ q)) (liftc zero (UI i)))) (varc (numeral 1)))

/-- Y **después**: el `varc 1̄` recibe el testigo `ȷ̇`, levantado por el binder del `∃`. -/
noncomputable def miPhiAt (q i j : Term) : Term :=
  eqCodeFn (carcT (nthcT (liftc zero (WQ q)) (varc (numeral 0))))
    (nthcT (premsOfT (nthcT (liftc zero (WQ q)) (liftc zero (UI i)))) (liftc zero (tcFn j)))

/-! ### Las invariancias `substtc` de los dos testigos, a nivel ARBITRARIO -/

theorem hinv_UI (i : Term) : ∀ (k : Nat) (w : Term),
    Prf (substtc (numeral k) w (liftc zero (UI i)) =eq liftc zero (UI i)) :=
  (substCode_hyps_lift (hu0_premsPsi i) (hLu0_premsPsi i)).1

theorem hinv_WQ (q : Term) : ∀ (k : Nat) (w : Term),
    Prf (substtc (numeral k) w (liftc zero (WQ q)) =eq liftc zero (WQ q)) :=
  (substCode_hyps_lift (hW_premsPsi q) (hLW_premsPsi q)).1

/-- ⭐ El `substfc` del índice, distribuido hasta el fondo. El `varc 0̄` (el testigo del `∃`)
    **sobrevive** —está por debajo del nivel actuante— y el `varc 1̄` (el índice del `∀`) **recibe
    el testigo**, levantado por el binder. -/
theorem substfc_bdEx_at (q i j : Term) :
    Prf (substfc zero (tcFn j) (bdExCode (miB i) (miPhi q i))
      =eq bdExCode (miB i) (miPhiAt q i j)) := by
  unfold bdExCode
  refine prf_eq_trans (prf_substfc_ex zero (tcFn j) _) (prf_congr_exc ?_)
  refine prf_eq_trans (prf_substfc_and (succ zero) (liftc zero (tcFn j)) _ _) ?_
  refine prf_congr_andc ?_ ?_
  · -- la COTA: `varc 0̄` sobrevive, `miB i` es invariante
    unfold ltCodeFn
    refine prf_eq_trans (prf_substfc_atom (succ zero) (liftc zero (tcFn j)) _ _) ?_
    unfold atom2CodeFn
    refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
    refine prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero (tcFn j)) _ _) ?_
    refine prf_eq_trans
      (prf_congr_cons_head (prf_substtc_varc_lt (by omega : 0 < 1) (liftc zero (tcFn j))))
      (prf_congr_cons_tail ?_)
    refine prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero (tcFn j)) _ _) ?_
    exact prf_eq_trans (prf_congr_cons_head (hinv_UI i 1 (liftc zero (tcFn j))))
      (prf_congr_cons_tail (prf_substtsc_nil (succ zero) (liftc zero (tcFn j))))
  · -- el `Phic`
    unfold miPhi miPhiAt
    refine prf_eq_trans (prf_substfc_eq (succ zero) (liftc zero (tcFn j)) _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_carcT (succ zero) (liftc zero (tcFn j)) _) ?_
      refine prf_congr_carcT ?_
      refine prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero (tcFn j)) _ _) ?_
      exact prf_congr_nthcT (hinv_WQ q 1 (liftc zero (tcFn j)))
        (prf_substtc_varc_lt (by omega : 0 < 1) (liftc zero (tcFn j)))
    · refine prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero (tcFn j)) _ _) ?_
      refine prf_congr_nthcT ?_ (prf_substtc_varc_eq 1 (liftc zero (tcFn j)))
      refine prf_eq_trans (prf_substtc_premsOfT (succ zero) (liftc zero (tcFn j)) _) ?_
      refine prf_congr_premsOfT ?_
      refine prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero (tcFn j)) _ _) ?_
      exact prf_congr_nthcT (hinv_WQ q 1 (liftc zero (tcFn j)))
        (hinv_UI i 1 (liftc zero (tcFn j)))


/-! ## §3 · §5 DE `D3ChainDotPrf`, GENERALIZADA EN SU `Phic`

⛔ **Por qué hace falta.** El `Phic` que `substCodeF2` produce **no** es el `bdCarcLtPhic` de §5:
su lado derecho es el **accesor dotado** `nthcT (premsOfT (nthcT q̇ i̇)) ȷ̇` y no `liftc 0 ẏ`. Es la
MONEDA de §3.55.2 por cuarta vez. Y el salto **no se puede dar donde está**, porque ese hueco vive
**bajo el binder del `exc`** y `pcc_rw` (que reescribe con `substfc zero`) no llega ahí.

⭐ **Dónde sí se puede dar**: en la obligación `hphi` — el cuerpo **ya instanciado en el testigo**
del `∃`, o sea con el binder **ya abierto**. `PrfH_bdEx_intro_open` es genérico en `Phic` desde
siempre; lo único que estaba especializado era la envoltura. -/

theorem pcc_bdEx_carc_reflect_gen (y p b Phic Phic' : Term) (A A' : Formula)
    (hPlift : liftTerm 0 Phic = Phic')
    (hAlift : liftFormula 0 A = A')
    (hwPhi : Prf (hasWitF (liftTerm 0 Phic')))
    (hphi : Prf (A' ⇒ (chainOk nil (liftTerm 0 p) ⇒ (lt (liftTerm 0 b) (lenc (liftTerm 0 p)) ⇒
        (land (lt (.var 0) (liftTerm 0 b))
              (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y))
         ⇒ provFromCode (substfc zero (tcFn (.var 0)) Phic')))))) :
    Prf (A ⇒ (chainOk nil p ⇒ (lt b (lenc p) ⇒ (boundedCarcLt y p b ⇒
      provFromCode (bdExCode (liftc zero (tcFn b)) Phic))))) := by
  refine prf_deduction (deduction_aux (deduction_aux (deduction_aux ?_
    (boundedCarcLt y p b) [lt b (lenc p), chainOk nil p, A] rfl)
    (lt b (lenc p)) [chainOk nil p, A] rfl)
    (chainOk nil p) [A] rfl)
  have hex : PrfH [boundedCarcLt y p b, lt b (lenc p), chainOk nil p, A]
      (boundedCarcLt y p b) := PrfH.hyp _ _ (List.Mem.head _)
  refine PrfH_ex_elim hex ?_
  rw [liftFormula_provFromCode_open]
  have hLb : liftTerm 0 (bdExCode (liftc zero (tcFn b)) Phic)
      = bdExCode (liftc zero (tcFn (liftTerm 0 b))) Phic' := by
    simp only [bdExCode, exc, andc, ltCodeFn, atom2CodeFn, liftc, varc, numeral, funcc,
      cons, nil, zero, succ, tcFn, liftTerm, liftTerms, liftTerm_strCode, liftTerm_numeral,
      hPlift]
  rw [hLb]
  let exBody : Formula := land (lt (.var 0) (liftTerm 0 b))
    (Formula.eq (carc (nthc (liftTerm 0 p) (.var 0))) (liftTerm 0 y))
  let Gm : List Formula :=
    [exBody, liftFormula 0 (boundedCarcLt y p b), liftFormula 0 (lt b (lenc p)),
     liftFormula 0 (chainOk nil p), liftFormula 0 A]
  show PrfH Gm (provFromCode (bdExCode (liftc zero (tcFn (liftTerm 0 b))) Phic'))
  have hC : PrfH Gm exBody := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Gm (lt (.var 0) (liftTerm 0 b)) := PrfH_and_elim_left hC
  have hble : PrfH Gm (lt (liftTerm 0 b) (lenc (liftTerm 0 p))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hchain : PrfH Gm (chainOk nil (liftTerm 0 p)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hA : PrfH Gm A' := hAlift ▸ PrfH.hyp _ _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  -- COTA: directa, sin evaluación
  have hlt1 : PrfH Gm (provFromCode (ltCodeFn (tcFn (.var 0)) (tcFn (liftTerm 0 b)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked (.var 0) (liftTerm 0 b)) _) hlt
  have hltB : PrfH Gm (provFromCode
      (ltCodeFn (tcFn (.var 0)) (liftc zero (tcFn (liftTerm 0 b))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_atom2CodeFn (prf_refl _)
      (prf_eq_symm (prf_liftc_tcFn (liftTerm 0 b))))) _) hlt1
  -- CUERPO: la obligación genérica, ya con el binder ABIERTO
  have hphi' : PrfH Gm (provFromCode (substfc zero (tcFn (.var 0)) Phic')) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH hphi _) hA) hchain) hble) hC
  exact PrfH_bdEx_intro_open _ _ (tcFn (.var 0))
    (substtc_inv_bdCarcLtB (liftTerm 0 b)) hltB hphi'
    (by hw_auto) hwPhi (by hw_auto)


/-! ## §4 · EL PUENTE `premsOfT (nthcT q̇ i̇) ↦ L̇`, extraído de B2

Es el paso intermedio de `pcc_bnd_bridge` (`Meta/D3BodyPrf.lean` §2). Se expone porque `hphi` lo
necesita **sin** el `lencT` de encima. -/

theorem pcc_premsOfT_bridge (q i : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
      provFromCode (eqc (premsOfT (nthcT (tcFn q) (tcFn i)))
        (tcFn (premsOf (nthc q i)))))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  let Gm : List Formula := [lt i (lenc q), chainOk nil q]
  let X : Term := nthc q i
  let L : Term := premsOf X
  have hch : PrfH Gm (chainOk nil q) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH Gm (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hline : PrfH Gm (lineWF X) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_lineWF_of_chainOk q i) _) hch) hlt
  have e1 : PrfH Gm (provFromCode (eqc (nthcT (tcFn q) (tcFn i)) (tcFn X))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have e1s : PrfH Gm (provFromCode (eqc (tcFn X) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_eq_symm_code_internal
      (nthcT (tcFn q) (tcFn i)) (tcFn X)
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i))
      (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))
      (prf_hasWit_tcFn X)) _) e1
  have e2 : PrfH Gm (provFromCode (eqc (premsOfT (tcFn X)) (tcFn L))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_premsOf X) _) hline
  exact PrfH_pcc_rw (fun c => eqCodeFn (premsOfT c) (tcFn L)) (hG_premsOfT L) _ _ e1s e2
    (prf_hasWitF_eq2 _ _ (prf_hasWit_premsOfT (prf_hasWit_varc (numeral 0)))
      (prf_hasWit_tcFn L))
    (prf_hasWit_tcFn X)
    (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i))

/-- ⭐ **LA MONEDA, cruzada del todo**: el accesor dotado triple `nthcT (premsOfT (nthcT q̇ i̇)) ȷ̇`
    llevado a la reflexión pura `(nthc (premsOf (nthc q i)) j)˙`. Dos eslabones: el puente de
    arriba (bajo `i < lenc q`) y `pcc_eval_nthc` (bajo `j < lenc L`). -/
theorem pcc_nthc_premsOf_bridge (q i j : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒ (lt j (lenc (premsOf (nthc q i))) ⇒
      provFromCode (eqc (nthcT (premsOfT (nthcT (tcFn q) (tcFn i))) (tcFn j))
        (tcFn (nthc (premsOf (nthc q i)) j)))))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (lt j (lenc (premsOf (nthc q i)))) [lt i (lenc q), chainOk nil q] rfl)
    (lt i (lenc q)) [chainOk nil q] rfl)
  let Gm : List Formula :=
    [lt j (lenc (premsOf (nthc q i))), lt i (lenc q), chainOk nil q]
  let L : Term := premsOf (nthc q i)
  have hch : PrfH Gm (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hlt : PrfH Gm (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hltj : PrfH Gm (lt j (lenc L)) := PrfH.hyp _ _ (List.Mem.head _)
  -- (1) el argumento interior: `premsOfT (nthcT q̇ i̇) ↦ L̇`
  have h1 : PrfH Gm (provFromCode (eqc (premsOfT (nthcT (tcFn q) (tcFn i))) (tcFn L))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_premsOfT_bridge q i) _) hch) hlt
  -- (2) `nthcT L̇ ȷ̇ ↦ (nthc L j)˙`
  have h2 : PrfH Gm (provFromCode (eqc (nthcT (tcFn L) (tcFn j)) (tcFn (nthc L j)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc L j) _) hltj
  -- (3) reescribir el argumento y componer — todo **sin binder**
  have hG : ∀ s : Term, Prf (substfc zero s
      (eqCodeFn (nthcT (varc (numeral 0)) (tcFn j)) (tcFn (nthc L j)))
      =eq eqCodeFn (nthcT s (tcFn j)) (tcFn (nthc L j))) := by
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_tcFn s (nthc L j))
    exact prf_eq_trans (prf_substtc_nthcT zero s _ _)
      (prf_congr_nthcT (prf_substtc_varc0 s) (prf_substtc_tcFn s j))
  have h1s : PrfH Gm (provFromCode (eqc (tcFn L) (premsOfT (nthcT (tcFn q) (tcFn i))))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_eq_symm_code_internal
      (premsOfT (nthcT (tcFn q) (tcFn i))) (tcFn L)
      (substtc_inv_premsOfT (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)))
      (prf_hasWit_premsOfT (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i)))
      (prf_hasWit_tcFn L)) _) h1
  exact PrfH_pcc_rw (fun c => eqCodeFn (nthcT c (tcFn j)) (tcFn (nthc L j))) hG _ _ h1s h2
    (prf_hasWitF_eq2 _ _
      (prf_hasWit_nthcT (prf_hasWit_varc (numeral 0)) (prf_hasWit_tcFn j))
      (prf_hasWit_tcFn (nthc L j)))
    (prf_hasWit_tcFn L)
    (prf_hasWit_premsOfT (prf_hasWit_nthcT (prf_hasWit_tcFn q) (prf_hasWit_tcFn i)))


/-! ## §5 · LA DISYUNCIÓN DEL CUERPO, desde la cadena

Es el `∀`-elim **interior**: de `chainOk nil q` sale `lineOkB nil q i`, su segundo conjunto es
`boundedPremsIn nil q i L`, y con `j < lenc L` sale el disyunto. ⭐ La cota `j < lenc L` es
**exactamente** la hipótesis que el `hbody` del chasis interior tiene a mano. -/

theorem prf_premsDisj_of_chainOk (q i j : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒ (lt j (lenc (premsOf (nthc q i))) ⇒
      lor (In (nthc (premsOf (nthc q i)) j) nil)
          (boundedCarcLt (nthc (premsOf (nthc q i)) j) q i)))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (lt j (lenc (premsOf (nthc q i)))) [lt i (lenc q), chainOk nil q] rfl)
    (lt i (lenc q)) [chainOk nil q] rfl)
  let Gm : List Formula :=
    [lt j (lenc (premsOf (nthc q i))), lt i (lenc q), chainOk nil q]
  let L : Term := premsOf (nthc q i)
  have hch : PrfH Gm (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hlt : PrfH Gm (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hltj : PrfH Gm (lt j (lenc L)) := PrfH.hyp _ _ (List.Mem.head _)
  have hB : PrfH Gm (chainOkB nil q) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_chainOk_iff_chainOkB nil q)) _) hch
  have hB' : PrfH Gm (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (lineOkB (liftTerm 0 nil) (liftTerm 0 q) (.var 0)))) := hB
  have hspec := PrfH_spec hB' i
  have heq : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (lineOkB (liftTerm 0 nil) (liftTerm 0 q) (.var 0)))
      = Formula.impl (lt i (lenc q)) (lineOkB nil q i) := by
    simp only [substFormula, substFormula_lineOkB, lt, lenc, nil, zero, substTerm, substTerms,
      FOL.substTerm_liftTerm, if_true]
  rw [heq] at hspec
  have hline : PrfH Gm (lineOkB nil q i) := PrfH.mp _ _ _ hspec hlt
  have hprems : PrfH Gm (boundedPremsIn nil q i L) := PrfH_and_elim_right hline
  have hp' : PrfH Gm (Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc L)))
      (lor (In (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 nil))
           (boundedCarcLt (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 q) (liftTerm 0 i))))) :=
    hprems
  have hspec2 := PrfH_spec hp' j
  have heq2 : substFormula 0 j (Formula.impl (lt (.var 0) (liftTerm 0 (lenc L)))
      (lor (In (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 nil))
           (boundedCarcLt (nthc (liftTerm 0 L) (.var 0)) (liftTerm 0 q) (liftTerm 0 i))))
      = Formula.impl (lt j (lenc L))
          (lor (In (nthc L j) nil) (boundedCarcLt (nthc L j) q i)) := by
    simp only [substFormula, substFormula_boundedCarcLt, lor, In, lt, lenc, nthc, nil, zero,
      substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  rw [heq2] at hspec2
  exact PrfH.mp _ _ _ hspec2 hltj


/-! ## §6 · LOS COLAPSOS DE `liftc` y el `substfc` del testigo -/

theorem prf_liftc2_tcFn (x : Term) :
    Prf (liftc zero (liftc zero (tcFn x)) =eq tcFn x) :=
  prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn x)) (prf_liftc_tcFn x)

theorem prf_liftc3_tcFn (x : Term) :
    Prf (liftc zero (liftc zero (liftc zero (tcFn x))) =eq tcFn x) :=
  prf_eq_trans (prf_congr_liftc (prf_liftc2_tcFn x)) (prf_liftc_tcFn x)

theorem prf_liftc_WQ (q : Term) : Prf (liftc zero (WQ q) =eq tcFn q) := prf_liftc3_tcFn q
theorem prf_liftc_UI (i : Term) : Prf (liftc zero (UI i) =eq tcFn i) := prf_liftc2_tcFn i

/-- El `substfc` del testigo del `∃`, con **todos** los `liftc` colapsados. -/
theorem substfc_miPhiAt (Q I J K : Term) :
    Prf (substfc zero K (miPhiAt Q I J)
      =eq eqCodeFn (carcT (nthcT (tcFn Q) K))
          (nthcT (premsOfT (nthcT (tcFn Q) (tcFn I))) (tcFn J))) := by
  unfold miPhiAt
  refine prf_eq_trans (prf_substfc_eq zero K _ _) ?_
  refine prf_congr_eqCodeFn ?_ ?_
  · refine prf_eq_trans (prf_substtc_carcT zero K _) (prf_congr_carcT ?_)
    refine prf_eq_trans (prf_substtc_nthcT zero K _ _) ?_
    exact prf_congr_nthcT
      (prf_eq_trans (hinv_WQ Q 0 K) (prf_liftc_WQ Q)) (prf_substtc_varc0 K)
  · refine prf_eq_trans (prf_substtc_nthcT zero K _ _) ?_
    refine prf_congr_nthcT ?_
      (prf_eq_trans (hW_chainOkBPsi J 0 K) (prf_liftc_tcFn J))
    refine prf_eq_trans (prf_substtc_premsOfT zero K _) (prf_congr_premsOfT ?_)
    refine prf_eq_trans (prf_substtc_nthcT zero K _ _) ?_
    exact prf_congr_nthcT (prf_eq_trans (hinv_WQ Q 0 K) (prf_liftc_WQ Q))
      (prf_eq_trans (hinv_UI I 0 K) (prf_liftc_UI I))


/-! ## §7 · `hphi` — el cuerpo instanciado en el testigo, **ya sin binder**

⭐ Aquí es donde se paga la MONEDA. Tres pasos, todos fuera de cualquier binder:
`pcc_eval_carc_nthc` evalúa el accesor, la hipótesis del `∃` reescribe el valor, y
`pcc_nthc_premsOf_bridge` cruza el accesor dotado triple a la reflexión pura. -/

theorem hwLiftc_tcFn (x : Term) : Prf (hasWit (liftc zero (tcFn x))) :=
  prf_mp (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.CRIT_hasWit_lift (tcFn x))
    (ROBINSON_PlusPlus.Meta.HasWitTcFnPrf.prf_hasWit_tcFn x)

theorem hwLiftc2_tcFn (x : Term) : Prf (hasWit (liftc zero (liftc zero (tcFn x)))) :=
  prf_mp (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.CRIT_hasWit_lift _) (hwLiftc_tcFn x)

theorem hwLiftc3_tcFn (x : Term) :
    Prf (hasWit (liftc zero (liftc zero (liftc zero (tcFn x))))) :=
  prf_mp (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.CRIT_hasWit_lift _) (hwLiftc2_tcFn x)

theorem hw_miPhiAt (Q I J : Term) : Prf (hasWitF (miPhiAt Q I J)) :=
  prf_hasWitF_eq2 _ _
    (prf_hasWit_carcT (prf_hasWit_nthcT (hwLiftc3_tcFn Q) (prf_hasWit_varc (numeral 0))))
    (prf_hasWit_nthcT
      (prf_hasWit_premsOfT (prf_hasWit_nthcT (hwLiftc3_tcFn Q) (hwLiftc2_tcFn I)))
      (hwLiftc_tcFn J))

theorem hphi_gen (Q I J : Term) :
    Prf (lt J (lenc (premsOf (nthc Q I))) ⇒
      (chainOk nil Q ⇒ (lt I (lenc Q) ⇒
        (land (lt (.var 0) I)
              (Formula.eq (carc (nthc Q (.var 0))) (nthc (premsOf (nthc Q I)) J))
         ⇒ provFromCode (substfc zero (tcFn (.var 0)) (miPhiAt Q I J)))))) := by
  refine prf_deduction (deduction_aux (deduction_aux (deduction_aux ?_
    (land (lt (.var 0) I)
      (Formula.eq (carc (nthc Q (.var 0))) (nthc (premsOf (nthc Q I)) J)))
    [lt I (lenc Q), chainOk nil Q, lt J (lenc (premsOf (nthc Q I)))] rfl)
    (lt I (lenc Q)) [chainOk nil Q, lt J (lenc (premsOf (nthc Q I)))] rfl)
    (chainOk nil Q) [lt J (lenc (premsOf (nthc Q I)))] rfl)
  let Gm : List Formula :=
    [land (lt (.var 0) I) (Formula.eq (carc (nthc Q (.var 0))) (nthc (premsOf (nthc Q I)) J)),
     lt I (lenc Q), chainOk nil Q, lt J (lenc (premsOf (nthc Q I)))]
  have hC : PrfH Gm (land (lt (.var 0) I)
      (Formula.eq (carc (nthc Q (.var 0))) (nthc (premsOf (nthc Q I)) J))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hltk : PrfH Gm (lt (.var 0) I) := PrfH_and_elim_left hC
  have heqc : PrfH Gm (Formula.eq (carc (nthc Q (.var 0))) (nthc (premsOf (nthc Q I)) J)) :=
    PrfH_and_elim_right hC
  have hIq : PrfH Gm (lt I (lenc Q)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hch : PrfH Gm (chainOk nil Q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hJL : PrfH Gm (lt J (lenc (premsOf (nthc Q I)))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  -- (1) el testigo del `∃` cae bajo `lenc Q`, por transitividad
  have hk : PrfH Gm (lt (.var 0) (lenc Q)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (prf_lt_trans _ _ _) _) hltk) hIq
  -- (2) evaluación del accesor `carc ∘ nthc`
  have hev : PrfH Gm (provFromCode (eqCodeFn (carcT (nthcT (tcFn Q) (tcFn (.var 0))))
      (tcFn (carc (nthc Q (.var 0)))))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (pcc_eval_carc_nthc Q (.var 0)) _) hch) hk
  -- (3) la hipótesis del `∃` reescribe el VALOR — congruencia OBJETO
  have hev2 : PrfH Gm (provFromCode (eqCodeFn (carcT (nthcT (tcFn Q) (tcFn (.var 0))))
      (tcFn (nthc (premsOf (nthc Q I)) J)))) :=
    PrfH_provCode_congr (PrfH_congr_eqCodeFn (prf_to_prfH (prf_refl _) _)
      (PrfH_congr_tcFn heqc)) hev
  -- (4) ⭐ LA MONEDA: el accesor dotado triple ↦ la reflexión pura
  have hbr : PrfH Gm (provFromCode (eqc
      (nthcT (premsOfT (nthcT (tcFn Q) (tcFn I))) (tcFn J))
      (tcFn (nthc (premsOf (nthc Q I)) J)))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (pcc_nthc_premsOf_bridge Q I J) _) hch) hIq) hJL
  have hbrs : PrfH Gm (provFromCode (eqc (tcFn (nthc (premsOf (nthc Q I)) J))
      (nthcT (premsOfT (nthcT (tcFn Q) (tcFn I))) (tcFn J)))) :=
    PrfH_mp_code_apply (prf_to_prfH (pcc_eq_symm_code_internal
      (nthcT (premsOfT (nthcT (tcFn Q) (tcFn I))) (tcFn J))
      (tcFn (nthc (premsOf (nthc Q I)) J))
      (substtc_inv_nthcT
        (substtc_inv_premsOfT (substtc_inv_nthcT (substtc_inv_tcFn Q) (substtc_inv_tcFn I)))
        (substtc_inv_tcFn J))
      (prf_hasWit_nthcT
        (prf_hasWit_premsOfT (prf_hasWit_nthcT (prf_hasWit_tcFn Q) (prf_hasWit_tcFn I)))
        (prf_hasWit_tcFn J))
      (prf_hasWit_tcFn (nthc (premsOf (nthc Q I)) J))) _) hbr
  -- (5) reescribir el lado derecho — **sin binder**
  have hG : ∀ s : Term, Prf (substfc zero s
      (eqCodeFn (carcT (nthcT (tcFn Q) (tcFn (.var 0)))) (varc (numeral 0)))
      =eq eqCodeFn (carcT (nthcT (tcFn Q) (tcFn (.var 0)))) s) := by
    intro s
    refine prf_eq_trans (prf_substfc_eq zero s _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_varc0 s)
    refine prf_eq_trans (prf_substtc_carcT zero s _) (prf_congr_carcT ?_)
    exact prf_eq_trans (prf_substtc_nthcT zero s _ _)
      (prf_congr_nthcT (prf_substtc_tcFn s Q) (prf_substtc_tcFn s (.var 0)))
  have hfin : PrfH Gm (provFromCode (eqCodeFn (carcT (nthcT (tcFn Q) (tcFn (.var 0))))
      (nthcT (premsOfT (nthcT (tcFn Q) (tcFn I))) (tcFn J)))) :=
    PrfH_pcc_rw (fun c => eqCodeFn (carcT (nthcT (tcFn Q) (tcFn (.var 0)))) c) hG _ _ hbrs hev2
      (prf_hasWitF_eq2 _ _
        (prf_hasWit_carcT (prf_hasWit_nthcT (prf_hasWit_tcFn Q) (prf_hasWit_tcFn (.var 0))))
        (prf_hasWit_varc (numeral 0)))
      (prf_hasWit_tcFn (nthc (premsOf (nthc Q I)) J))
      (prf_hasWit_nthcT
        (prf_hasWit_premsOfT (prf_hasWit_nthcT (prf_hasWit_tcFn Q) (prf_hasWit_tcFn I)))
        (prf_hasWit_tcFn J))
  -- (6) volver a la forma `substfc` del chasis
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
    (prf_eq_symm (substfc_miPhiAt Q I J (tcFn (.var 0))))) _) hfin


/-! ### Naturalidad, por LEMAS y no por `rfl`

⚠️ **Medido**: dejar que `rfl` case `liftTerm 0 (miPhiAt …)` hace que Lean despliegue
`strCode "premsOf"` **carácter a carácter** y agota los heartbeats. Con `liftTerm_strCode` en el
`simp` set sale en un instante. -/

theorem liftTerm_miPhiAt (c : Nat) (Q I J : Term) :
    liftTerm c (miPhiAt Q I J) = miPhiAt (liftTerm c Q) (liftTerm c I) (liftTerm c J) := by
  simp only [miPhiAt, WQ, UI, eqCodeFn, carcT, nthcT, premsOfT, funcc, varc,
    liftc, tcFn, cons, nil, zero, succ, liftTerm, liftTerms,
    liftTerm_strCode, liftTerm_numeral]

theorem liftFormula_ltPrems (c : Nat) (q i j : Term) :
    liftFormula c (lt j (lenc (premsOf (nthc q i))))
      = lt (liftTerm c j) (lenc (premsOf (nthc (liftTerm c q) (liftTerm c i)))) := by
  simp only [lt, lenc, premsOf, nthc, liftFormula, liftTerm, liftTerms]

/-! ## §8 · 🏁 EL ENSAMBLAJE — `DEUDA_premsBody`

El cuerpo se parte por el `lor`. El disyunto **izquierdo** es `In y nil`, **refutable**
(`prf_not_in_nil`) ⇒ su código queda **arbitrario** y no hay que calcularlo. El **derecho** lo
cierra `pcc_bdEx_carc_reflect_gen` con el `hphi` de §7. -/

theorem prf_congr_bdExCode_bnd {B B' P : Term} (h : Prf (B =eq B')) :
    Prf (bdExCode B P =eq bdExCode B' P) :=
  prf_congr_exc (prf_congr_andc (prf_congr_atom2CodeFn (prf_refl _) h) (prf_refl _))

/-- El cuerpo del `∀` interior, con el índice ya instanciado y partido por el `lor`. -/
theorem substfc_premsPsi_at (q i j : Term) :
    Prf (substfc zero (tcFn j) (premsPsi q i)
      =eq orc (substfc zero (tcFn j) (substCodeF2 1 (UI i) (WQ q)
              (In (nthc (premsOf (nthc (.var 2) (.var 1))) (.var 0)) nil)))
          (bdExCode (miB i) (miPhiAt q i j))) := by
  rw [premsPsi_split]
  refine prf_eq_trans (prf_substfc_or zero (tcFn j) _ _) ?_
  exact prf_congr_orc (prf_refl _) (substfc_bdEx_at q i j)

/-- 🏁🏁🏁 **LA NOVENA OBLIGACIÓN, PROBADA.** -/
theorem premsBody_reflect (q i j : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒ (lt j (lenc (premsOf (nthc q i))) ⇒
      provFromCode (substfc zero (tcFn j) (premsPsi q i))))) := by
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (lt j (lenc (premsOf (nthc q i)))) [lt i (lenc q), chainOk nil q] rfl)
    (lt i (lenc q)) [chainOk nil q] rfl)
  let Gm : List Formula :=
    [lt j (lenc (premsOf (nthc q i))), lt i (lenc q), chainOk nil q]
  have hltj : PrfH Gm (lt j (lenc (premsOf (nthc q i)))) := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Gm (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hch : PrfH Gm (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  refine PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
    (prf_eq_symm (substfc_premsPsi_at q i j))) _) ?_
  -- la disyunción OBJETO, desde la cadena
  have hdisj : PrfH Gm (lor (In (nthc (premsOf (nthc q i)) j) nil)
      (boundedCarcLt (nthc (premsOf (nthc q i)) j) q i)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_premsDisj_of_chainOk q i j) _) hch) hlt) hltj
  refine PrfH_or_elim hdisj ?_ ?_
  · -- ⭐ RAMA IZQUIERDA: `In y nil` es refutable ⇒ explosión. El código no se toca.
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_in_nil (nthc (premsOf (nthc q i)) j)) _)
        (PrfH.hyp _ _ (List.Mem.head _)))
  · -- RAMA DERECHA: el `∃` acotado, con el `Phic` que el destino impone
    refine PrfH_orR_code _ _ ?_
    have hgen : Prf (lt j (lenc (premsOf (nthc q i))) ⇒
        (chainOk nil q ⇒ (lt i (lenc q) ⇒
          (boundedCarcLt (nthc (premsOf (nthc q i)) j) q i ⇒
            provFromCode (bdExCode (liftc zero (tcFn i)) (miPhiAt q i j)))))) :=
      pcc_bdEx_carc_reflect_gen (nthc (premsOf (nthc q i)) j) q i
        (miPhiAt q i j) (miPhiAt (liftTerm 0 q) (liftTerm 0 i) (liftTerm 0 j))
        (lt j (lenc (premsOf (nthc q i))))
        (lt (liftTerm 0 j) (lenc (premsOf (nthc (liftTerm 0 q) (liftTerm 0 i)))))
        (liftTerm_miPhiAt 0 q i j) (liftFormula_ltPrems 0 q i j) (hw_miPhiAt _ _ _)
        (hphi_gen (liftTerm 0 q) (liftTerm 0 i) (liftTerm 0 j))
    have hbd : PrfH (boundedCarcLt (nthc (premsOf (nthc q i)) j) q i :: Gm)
        (provFromCode (bdExCode (liftc zero (tcFn i)) (miPhiAt q i j))) :=
      PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
        (prf_to_prfH hgen _)
        (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))))
        (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
        (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
        (PrfH.hyp _ _ (List.Mem.head _))
    -- ⚠️ la cota del destino lleva **una capa más** de `liftc`, que colapsa a nivel OBJETO
    exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_bdExCode_bnd
      (prf_eq_symm (prf_congr_liftc (prf_liftc_tcFn i))))) _) hbd

/-- 🏁🏁🏁 **`DEUDA_premsBody`, SALDADA** — con los puentes del paquete. -/
theorem premsBody_deuda : DEUDA_premsBody := by
  intro r j
  refine prf_deduction (deduction_aux ?_ (lt j (ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsBnd r))
    [ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsCF r] rfl)
  have hCF : PrfH [lt j (ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsBnd r),
      ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsCF r]
      (ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsCF r) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hltj : PrfH [lt j (ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsBnd r),
      ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsCF r]
      (lt j (ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsBnd r)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (premsBody_reflect (carc r) (cdrc r) j) _)
    (PrfH_and_elim_left hCF)) (PrfH_and_elim_right hCF)) hltj


/-! ## §9 · EL DESEMPAQUETADO — los puentes objeto que §7 anticipó

⚠️ §7 de `D3ChainDotPrf` lo dejó medido: `carc (cons q i) ≐ q` **no es `rfl`** (`carc` es un
símbolo de función OBJETO). Hay que arrastrarlo, y se arrastra con **Leibniz objeto** sobre la
fórmula entera — dos pasos, uno por accesor.

⚠️ **Y el hueco hay que PROTEGERLO**: el argumento que no se sustituye puede mencionar `#0`, así
que va bajo un `liftTerm 0` y se recupera con `FOL.substTerm_liftTerm`. Sin eso el Leibniz
**capturaría** la variable y el lema sería falso. -/

/-- Las piezas del chasis, **desempaquetadas**. -/
def premsCF2 (Q I : Term) : Formula := land (chainOk nil Q) (lt I (lenc Q))
def premsBnd2 (Q I : Term) : Term := lenc (premsOf (nthc Q I))

/-- El enunciado del chasis interior, desempaquetado y como FÓRMULA (para el Leibniz). -/
noncomputable def bodyF (Q I : Term) : Formula :=
  Formula.impl (premsCF2 Q I)
    (provFromCode (bdAllCode (tcFn (premsBnd2 Q I)) (premsPsi Q I)))

theorem substFormula_bodyF_snd (s X X2 : Term) (hX : substTerm 0 s X = X2) :
    substFormula 0 s (bodyF X (.var 0)) = bodyF X2 s := by
  simp only [bodyF, premsCF2, premsBnd2, chainOk, lt, lenc, premsOf, nthc, nil, zero, succ,
    land, bdAllCode, forallc, implc, ltCodeFn, atom2CodeFn, varc, tcFn, cons,
    substFormula_provFromCode_open, substFormula, substTerm, substTerms,
    substTerm_strCode, substTerm_numeral,
    hPs_premsPsi, hX, if_true]

theorem substFormula_bodyF_fst (s Y Y2 : Term) (hY : substTerm 0 s Y = Y2) :
    substFormula 0 s (bodyF (.var 0) Y) = bodyF s Y2 := by
  simp only [bodyF, premsCF2, premsBnd2, chainOk, lt, lenc, premsOf, nthc, nil, zero, succ,
    land, bdAllCode, forallc, implc, ltCodeFn, atom2CodeFn, varc, tcFn, cons,
    substFormula_provFromCode_open, substFormula, substTerm, substTerms,
    substTerm_strCode, substTerm_numeral,
    hPs_premsPsi, hY, if_true]

/-- El chasis interior, ya **desempaquetado**. -/
theorem hbdAllPrems_unpacked (q i : Term) : Prf (bodyF q i) := by
  have h0 : Prf (bodyF (carc (cons q i)) (cdrc (cons q i))) :=
    hbdAllPrems_of_body premsBody_deuda (cons q i)
  -- (1) Leibniz sobre el SEGUNDO accesor: `cdrc (cons q i) ↦ i`
  have hs2 : ∀ s : Term,
      substFormula 0 s (bodyF (liftTerm 0 (carc (cons q i))) (.var 0))
        = bodyF (carc (cons q i)) s := fun s =>
    substFormula_bodyF_snd s _ _ (FOL.substTerm_liftTerm (carc (cons q i)) 0 s)
  have h1 : Prf (bodyF (carc (cons q i)) i) :=
    (hs2 i) ▸ prf_mp (prf_mp (Prf.incl (Prf₀.leibniz
      (bodyF (liftTerm 0 (carc (cons q i))) (.var 0)) (cdrc (cons q i)) i))
      (prf_cdrc_cons q i)) ((hs2 (cdrc (cons q i))) ▸ h0)
  -- (2) Leibniz sobre el PRIMERO: `carc (cons q i) ↦ q`
  have hs1 : ∀ s : Term, substFormula 0 s (bodyF (.var 0) (liftTerm 0 i)) = bodyF s i :=
    fun s => substFormula_bodyF_fst s _ _ (FOL.substTerm_liftTerm i 0 s)
  exact (hs1 q) ▸ prf_mp (prf_mp (Prf.incl (Prf₀.leibniz
    (bodyF (.var 0) (liftTerm 0 i)) (carc (cons q i)) q))
    (prf_carc_cons q i)) ((hs1 (carc (cons q i))) ▸ h1)


/-! # §10 · 🏁🏁🏁 **D3, PROBADA** (2026‑09‑10g)

Con la novena obligación saldada (§9bis), sólo faltaba meter la cota en el `bdAllCode` — que es
§4 de `D3ChainDotPrf` otra vez, **un nivel más adentro**. -/


/-! ## §1 · LA QUINTA VARIANTE: `substfc` al nivel del hueco BAJO

⭐ Y es la **más barata de la familia**: el testigo del `substfc` **no aparece** en el resultado,
así que no hace falta la hipótesis `u ≐ varc v̄` que la cuarta sí necesitaba. La razón es que a
nivel `v+1` las variables que sobreviven en `substCodeF2 (v+1) u₀ W φ` son todas `≤ v`. -/

mutual

theorem substtc_inv_substCodeT2 (v : Nat) (u0 W : Term)
    (hu0 : ∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w u0 =eq u0))
    (hW : ∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w W =eq W)) :
    ∀ (t : Term), liftTerm (v + 3) t = t →
      ∀ u, Prf (substtc (numeral (v + 1)) u (substCodeT2 (v + 1) u0 W t)
        =eq substCodeT2 (v + 1) u0 W t)
  | .var n, hfv, u => by
      have hn : Nat.le n (v + 2) := by
        rcases Nat.lt_or_ge n (v + 3) with h | h
        · exact Nat.le_of_lt_succ h
        · have hne : ¬ (n < v + 3) := Nat.not_lt.mpr h
          simp only [liftTerm, if_neg hne, Term.var.injEq] at hfv
          exact absurd hfv (Nat.succ_ne_self n)
      rcases Nat.lt_or_ge n (v + 1) with hlt | hge
      · have hsub : substCodeT2 (v + 1) u0 W (.var n) = varc (numeral n) := by
          simp only [substCodeT2]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [hsub]
        exact prf_mp (prf_substtc_var_lt (numeral (v + 1)) u (numeral n))
          (prf_gnum_lt (by omega))
      · rcases Nat.lt_or_ge n (v + 2) with hlt3 | hge3
        · have hnv : n = v + 1 := by omega
          subst hnv
          have hsub : substCodeT2 (v + 1) u0 W (.var (v + 1)) = u0 := by
            simp only [substCodeT2]; rw [if_neg (by omega)]; simp
          rw [hsub]; exact hu0 (v + 1) u
        · have hnv : n = v + 2 := Nat.le_antisymm hn hge3
          subst hnv
          have hsub : substCodeT2 (v + 1) u0 W (.var (v + 2)) = W := by
            simp only [substCodeT2]; simp
          rw [hsub]; exact hW (v + 1) u
  | .func sym ts, hfv, u => by
      have hall := hfv
      simp only [liftTerm, Term.func.injEq, true_and] at hall
      show Prf (substtc (numeral (v + 1)) u (funcc (strCode sym) (substCodeTs2 (v + 1) u0 W ts))
        =eq funcc (strCode sym) (substCodeTs2 (v + 1) u0 W ts))
      refine prf_eq_trans (prf_substtc_func (numeral (v + 1)) u _ _) ?_
      unfold funcc
      refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
      exact substtc_inv_substCodeTs2 v u0 W hu0 hW ts hall u

theorem substtc_inv_substCodeTs2 (v : Nat) (u0 W : Term)
    (hu0 : ∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w u0 =eq u0))
    (hW : ∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w W =eq W)) :
    ∀ (ts : List Term), liftTerms (v + 3) ts = ts →
      ∀ u, Prf (substtsc (numeral (v + 1)) u (substCodeTs2 (v + 1) u0 W ts)
        =eq substCodeTs2 (v + 1) u0 W ts)
  | [], _, u => by
      show Prf (substtsc (numeral (v + 1)) u nil =eq nil)
      exact prf_substtsc_nil (numeral (v + 1)) u
  | t :: ts, hfv, u => by
      have h1 := hfv
      simp only [liftTerms, List.cons.injEq] at h1
      show Prf (substtsc (numeral (v + 1)) u
          (cons (substCodeT2 (v + 1) u0 W t) (substCodeTs2 (v + 1) u0 W ts))
        =eq cons (substCodeT2 (v + 1) u0 W t) (substCodeTs2 (v + 1) u0 W ts))
      refine prf_eq_trans (prf_substtsc_cons (numeral (v + 1)) u _ _) ?_
      exact prf_eq_trans
        (prf_congr_cons_head (substtc_inv_substCodeT2 v u0 W hu0 hW t h1.1 u))
        (prf_congr_cons_tail (substtc_inv_substCodeTs2 v u0 W hu0 hW ts h1.2 u))

end

theorem substfc_inv_substCodeF2 : ∀ (v : Nat) (u0 W : Term),
    (∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w u0 =eq u0)) →
    Prf (liftc zero u0 =eq u0) →
    (∀ (k : Nat) (w : Term), Prf (substtc (numeral k) w W =eq W)) →
    Prf (liftc zero W =eq W) →
    ∀ (φ : Formula), liftFormula (v + 3) φ = φ →
      ∀ u, Prf (substfc (numeral (v + 1)) u (substCodeF2 (v + 1) u0 W φ)
        =eq substCodeF2 (v + 1) u0 W φ)
  | v, u0, W, _, _, _, _, .bottom, _, u => by
      show Prf (substfc (numeral (v + 1)) u botc =eq botc)
      exact prf_substfc_bottom (numeral (v + 1)) u
  | v, u0, W, hu0, _, hW, _, .atom P ts, hfv, u => by
      have hts : liftTerms (v + 3) ts = ts := by
        simpa only [liftFormula, Formula.atom.injEq, true_and] using hfv
      show Prf (substfc (numeral (v + 1)) u (atomc (strCode P) (substCodeTs2 (v + 1) u0 W ts))
        =eq atomc (strCode P) (substCodeTs2 (v + 1) u0 W ts))
      refine prf_eq_trans (prf_substfc_atom (numeral (v + 1)) u _ _) ?_
      unfold atomc
      refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
      exact substtc_inv_substCodeTs2 v u0 W hu0 hW ts hts u
  | v, u0, W, hu0, _, hW, _, .eq a b, hfv, u => by
      have h1 := hfv
      simp only [liftFormula, Formula.eq.injEq] at h1
      show Prf (substfc (numeral (v + 1)) u
          (eqCodeFn (substCodeT2 (v + 1) u0 W a) (substCodeT2 (v + 1) u0 W b))
        =eq eqCodeFn (substCodeT2 (v + 1) u0 W a) (substCodeT2 (v + 1) u0 W b))
      refine prf_eq_trans (prf_substfc_eq (numeral (v + 1)) u _ _) ?_
      exact prf_congr_eqCodeFn (substtc_inv_substCodeT2 v u0 W hu0 hW a h1.1 u)
        (substtc_inv_substCodeT2 v u0 W hu0 hW b h1.2 u)
  | v, u0, W, hu0, hLu, hW, hL, .impl a b, hfv, u => by
      have h1 := hfv
      simp only [liftFormula, Formula.impl.injEq] at h1
      show Prf (substfc (numeral (v + 1)) u
          (implc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
        =eq implc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
      refine prf_eq_trans (prf_substfc_impl (numeral (v + 1)) u _ _) ?_
      exact prf_congr_implc (substfc_inv_substCodeF2 v u0 W hu0 hLu hW hL a h1.1 u)
        (substfc_inv_substCodeF2 v u0 W hu0 hLu hW hL b h1.2 u)
  | v, u0, W, hu0, hLu, hW, hL, .and a b, hfv, u => by
      have h1 := hfv
      simp only [liftFormula, Formula.and.injEq] at h1
      show Prf (substfc (numeral (v + 1)) u
          (andc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
        =eq andc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
      refine prf_eq_trans (prf_substfc_and (numeral (v + 1)) u _ _) ?_
      exact prf_congr_andc (substfc_inv_substCodeF2 v u0 W hu0 hLu hW hL a h1.1 u)
        (substfc_inv_substCodeF2 v u0 W hu0 hLu hW hL b h1.2 u)
  | v, u0, W, hu0, hLu, hW, hL, .or a b, hfv, u => by
      have h1 := hfv
      simp only [liftFormula, Formula.or.injEq] at h1
      show Prf (substfc (numeral (v + 1)) u
          (orc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
        =eq orc (substCodeF2 (v + 1) u0 W a) (substCodeF2 (v + 1) u0 W b))
      refine prf_eq_trans (prf_substfc_or (numeral (v + 1)) u _ _) ?_
      exact prf_congr_orc (substfc_inv_substCodeF2 v u0 W hu0 hLu hW hL a h1.1 u)
        (substfc_inv_substCodeF2 v u0 W hu0 hLu hW hL b h1.2 u)
  | v, u0, W, hu0, hLu, hW, hL, Formula.forall a, hfv, u => by
      have h1 : liftFormula (v + 4) a = a := by
        simpa only [liftFormula, Formula.forall.injEq] using hfv
      show Prf (substfc (numeral (v + 1)) u
          (forallc (substCodeF2 (v + 2) (liftc zero u0) (liftc zero W) a))
        =eq forallc (substCodeF2 (v + 2) (liftc zero u0) (liftc zero W) a))
      refine prf_eq_trans (prf_substfc_forall (numeral (v + 1)) u _) ?_
      unfold forallc
      refine prf_congr_cons_tail (prf_congr_cons_head ?_)
      obtain ⟨hu0', hLu'⟩ := substCode_hyps_lift hu0 hLu
      obtain ⟨hW', hL'⟩ := substCode_hyps_lift hW hL
      exact substfc_inv_substCodeF2 (v + 1) (liftc zero u0) (liftc zero W)
        hu0' hLu' hW' hL' a h1 (liftc zero u)
  | v, u0, W, hu0, hLu, hW, hL, .ex a, hfv, u => by
      have h1 : liftFormula (v + 4) a = a := by
        simpa only [liftFormula, Formula.ex.injEq] using hfv
      show Prf (substfc (numeral (v + 1)) u
          (exc (substCodeF2 (v + 2) (liftc zero u0) (liftc zero W) a))
        =eq exc (substCodeF2 (v + 2) (liftc zero u0) (liftc zero W) a))
      refine prf_eq_trans (prf_substfc_ex (numeral (v + 1)) u _) ?_
      unfold exc
      refine prf_congr_cons_tail (prf_congr_cons_head ?_)
      obtain ⟨hu0', hLu'⟩ := substCode_hyps_lift hu0 hLu
      obtain ⟨hW', hL'⟩ := substCode_hyps_lift hW hL
      exact substfc_inv_substCodeF2 (v + 1) (liftc zero u0) (liftc zero W)
        hu0' hLu' hW' hL' a h1 (liftc zero u)

/-- `hPinv` del chasis INTERIOR: el cuerpo es invariante bajo `substfc` de NIVEL 1. -/
theorem hPinv_premsPsi (q i : Term) :
    ∀ u : Term, Prf (substfc (succ zero) u (premsPsi q i) =eq premsPsi q i) :=
  fun u => substfc_inv_substCodeF2 0 (liftc zero (tcFn i)) (liftc zero (liftc zero (tcFn q)))
    (hu0_premsPsi i) (hLu0_premsPsi i) (hW_premsPsi q) (hLW_premsPsi q)
    premsBodyF hfv_premsBodyF u


/-! ## §2 · EL PUENTE DE LA COTA DEL CHASIS INTERIOR

Es §4 de `D3ChainDotPrf` otra vez, un nivel más adentro: `pcc_bdAll_intro` entrega la cota como
**reflexión pura** `(lenc L)˙` y el destino la pide como **accesor dotado**
`lencT (premsOfT (nthcT …))`. El salto lo dio **B2**; aquí sólo se mete en el `bdAllCode`. -/

theorem hBc'_prems (q i : Term) :
    Prf (liftc zero (lencT (premsOfT (nthcT (WQ q) (UI i))))
      =eq lencT (premsOfT (nthcT (WQ q) (UI i)))) := by
  refine prf_eq_trans (prf_liftc_lencT zero _) (prf_congr_lencT ?_)
  refine prf_eq_trans (prf_liftc_funcc1 zero (strCode "premsOf") _) (prf_congr_premsOfT ?_)
  refine prf_eq_trans (prf_liftc_nthcT zero _ _) ?_
  exact prf_congr_nthcT
    (prf_congr_liftc (prf_congr_liftc (prf_liftc_tcFn q)))
    (prf_congr_liftc (prf_liftc_tcFn i))

theorem hwP_premsPsi (q i : Term) : Prf (hasWitF (bdAllBndCtx (premsPsi q i))) := by
  unfold bdAllBndCtx bdAllCode
  exact prf_hasWitF_forallc _ (prf_hasWitF_implc _ _ (by hw_auto) (hwPsi_premsPsi q i))

/-- 🏁🏁 **`hbody`(b) de D3** — la mitad que faltaba. -/
theorem hB_premsDotAt (q i : Term) :
    Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒ provFromCode (premsDotAt q i))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [chainOk nil q] rfl)
  have hch : PrfH [lt i (lenc q), chainOk nil q] (chainOk nil q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [lt i (lenc q), chainOk nil q] (lt i (lenc q)) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hCF : PrfH [lt i (lenc q), chainOk nil q] (premsCF2 q i) := PrfH_and_intro hch hlt
  have h0 : PrfH [lt i (lenc q), chainOk nil q]
      (provFromCode (bdAllCode (tcFn (premsBnd2 q i)) (premsPsi q i))) :=
    PrfH.mp _ _ _ (prf_to_prfH (hbdAllPrems_unpacked q i) _) hCF
  rw [premsDotAt_split]
  exact PrfH_bdAllCode_congr_bnd _ _ (premsPsi q i) (hPinv_premsPsi q i)
    (prf_liftc_tcFn (premsBnd2 q i)) (hBc'_prems q i)
    (PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_bnd_bridge_at q i) _) hch) hlt)
    h0 (by hw_auto) (by hw_auto) (hwP_premsPsi q i)

/-! ## §3 · 🏁🏁🏁 **D3, PROBADA** -/

/-- El `hbody` del `pcc_bdAll_intro` EXTERIOR, desde sus dos mitades. -/
theorem hbody_prems : ∀ q i : Term, Prf (chainOk nil q ⇒ (lt i (lenc q) ⇒
    provFromCode (substfc zero (tcFn i) (chainOkBPsiDot q)))) :=
  hbody_of_halves hA_lineWFDotAt hB_premsDotAt

/-- 🏁🏁🏁 **LA TERCERA CONDICIÓN DE DERIVABILIDAD, PROBADA.** -/
theorem d3_prf_real (φ : Formula) : Prf (provCodeC' φ ⇒ provCodeC' (provCodeC' φ)) :=
  d3_prf_of_halves φ hA_lineWFDotAt hB_premsDotAt


end ROBINSON_PlusPlus.Meta.PremsBdAllPrf

/-! ## `export` — por CONSUMO -/
export ROBINSON_PlusPlus.Meta.PremsBdAllPrf (
  liftTerm_nil liftTerm_liftc liftTerm_substCodeT2 liftTerms_substCodeTs2 liftTerm_substCodeF2
  substTerm_nil substTerm_liftc substTerm_substCodeT2 substTerms_substCodeTs2
  substTerm_substCodeF2
  hPl_premsPsi hPs_premsPsi premsPsiPk hPl_premsPsiPk hPs_premsPsiPk
  premsCF hCl_premsCF hCs_premsCF premsBnd hbl_premsBnd hbs_premsBnd
  substtc_id_substCodeT2 substtc_id_substCodeTs2 substfc_id_substCodeF2
  premsBodyF premsPsi_eq hfv_premsBodyF
  hu0_premsPsi hLu0_premsPsi hW_premsPsi hLW_premsPsi
  hPsiId_premsPsi hPsiId_premsPsiPk
  premsPsi_dot_eq hwS_liftc_tcFn hwS_liftc2_tcFn hwPsi_premsPsi hwPsi_premsPsiPk
  DEUDA_premsBody hbdAllPrems_of_body prf_pkQ prf_pkI
  WQ UI premsPsi_split miB miPhi miPhiAt hinv_UI hinv_WQ substfc_bdEx_at
  pcc_bdEx_carc_reflect_gen
  pcc_premsOfT_bridge pcc_nthc_premsOf_bridge prf_premsDisj_of_chainOk
  prf_liftc2_tcFn prf_liftc3_tcFn prf_liftc_WQ prf_liftc_UI substfc_miPhiAt
  hwLiftc_tcFn hwLiftc2_tcFn hwLiftc3_tcFn hw_miPhiAt hphi_gen
  liftTerm_miPhiAt liftFormula_ltPrems
  prf_congr_bdExCode_bnd substfc_premsPsi_at premsBody_reflect premsBody_deuda
  premsCF2 premsBnd2 bodyF substFormula_bodyF_snd substFormula_bodyF_fst
  hbdAllPrems_unpacked
  substtc_inv_substCodeT2 substtc_inv_substCodeTs2 substfc_inv_substCodeF2
  hPinv_premsPsi hBc'_prems hwP_premsPsi hB_premsDotAt hbody_prems d3_prf_real
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.substfc_id_substCodeF2
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hPsiId_premsPsi
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hwPsi_premsPsi
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hbdAllPrems_of_body
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.premsBody_deuda
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hbdAllPrems_unpacked
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hB_premsDotAt
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real
