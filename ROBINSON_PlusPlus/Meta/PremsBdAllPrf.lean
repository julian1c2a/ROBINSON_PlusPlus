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

set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000

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

/-- La NOVENA obligación, **enunciada** (no postulada): el cuerpo del `∀` interior, reflejado. -/
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


/-! ### §7.2 · Lo que queda de D3, con la ruta MEDIDA

| pieza | estado |
|---|---|
| **B1** · `pcc_eval_premsOf` — `premsOf` dentro de `Prov` | 🏁 `Meta/PremsOfDotPrf.lean` |
| **B2** · el puente de la COTA | 🏁 `Meta/D3BodyPrf.lean` §2 |
| **B3** · el chasis interior, **ocho** obligaciones | 🏁 aquí |
| **B3** · `DEUDA_premsBody` — la novena | ⬜ **lo único que queda de D3** |

⭐ **La ruta de la novena está medida y no tiene sorpresas de forma.** El cuerpo se parte por el
`lor` (`prf_substfc_or`), y de sus dos disyuntos:

* el **izquierdo** (`In y nil`) es **vacuo** —`prf_not_in_nil`— y §6 de `D3ChainDotPrf` ya lo
  explota dejando su código **ARBITRARIO** (el parámetro `Ac`): no hay que calcularlo;
* el **derecho** es `boundedCarcLt`, y `pcc_bdCarcLt_reflect` (§5) lo refleja con `y`, `p`, `b`
  **abstractos**.

⚠️ **La única fricción que queda, y está localizada**: §5 escribe el testigo del `∃` como
`liftc 0 ẏ`, y lo que `substCodeF2` produce en esa posición es el **accesor dotado**
`nthcT (premsOfT (nthcT q̇ i̇)) j̇`. Es **la misma moneda de §3.55.2 por cuarta vez**, y las dos
piezas que la cruzan ya existen: **B2** lleva `premsOfT (nthcT q̇ i̇)` a `L̇`, y `pcc_eval_nthc L j`
lleva `nthcT L̇ j̇` a `(nthc L j)˙` **bajo `j < lenc L`** — que es exactamente la cota del `∀`
interior, o sea una hipótesis que el `hbody` **tiene a mano**.

⇒ Lo que hace falta es **generalizar `pcc_bdCarcLt_reflect` en su `Phic`** (hoy fijo a
`bdCarcLtPhic`), porque el hueco a reescribir queda **bajo el binder del `exc`** y `pcc_rw` no
llega ahí. -/

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
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.substfc_id_substCodeF2
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hPsiId_premsPsi
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hwPsi_premsPsi
#print axioms ROBINSON_PlusPlus.Meta.PremsBdAllPrf.hbdAllPrems_of_body
