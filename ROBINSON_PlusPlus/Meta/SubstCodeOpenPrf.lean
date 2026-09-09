/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ArithPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf

/-!
## META — NIVEL D real (§20): aritmetización de la sustitución con testigo‑código **ARBITRARIO**

Primer paso real de la **evaluación provable** (§18.3/§19.4).

`prf_substTerm_arith` / `prf_substFormula_arith` (`Meta/ArithPrf.lean`) computan
`substtc`/`substfc` **sólo** cuando el código sustituido es `termCode s` para una `s` **meta**:

```lean
prf_substFormula_arith (v s f) : substfc (numeral v) (termCode s) (formCode f) =eq formCode (substFormula v s f)
```

Pero la instanciación de axiomas codificados (`pcc_axiom_inst`, §19.3) produce
`substfc zero w (formCode φ)` con `w = tcFn a` — que **no** es `termCode` de nada meta. Aquí se
generaliza el cómputo a un **código‑testigo `w` arbitrario**.

**Por qué sale barato:** en las pruebas originales `termCode s` viaja como argumento **opaco** — se
pasa tal cual a `prf_substtc_var_eq/gt/lt`, que están enunciadas para `s` **cualquiera** (son las
«ecuaciones de variable» de `substtc`, la pieza que §11.3 señaló y que `tcFn` no tiene). Lo único que
cambia es el lado derecho, que ya no puede ser `termCode (substTerm v s t)`: hay que describirlo con
funciones meta propias (`substCodeT`/`substCodeF`).

**Nota De Bruijn:** al entrar bajo un binder, `prf_substfc_forall`/`_ex` **levantan el testigo**
(`liftc zero t`) y suben el nivel (`succ v`). Las funciones meta lo replican. Es la confirmación
*a posteriori* de por qué el `∀`‑elim de código (§19.1) debía admitir **testigos abiertos**: incluso
instanciando un axioma cerrado, el testigo interno acaba abierto.
-/

/-! ### Funciones meta: «código de `t` con el hueco de la variable `v` relleno por `w`» -/

mutual

/-- `substCodeT v w t` = código del término `t` con la variable `v` sustituida por el **código** `w`.
    Espeja `substTerm v s t`, pero el sustituyente es un código, no un término. -/
def substCodeT (v : Nat) (w : Term) : Term → Term
  | .var n => if n = v then w else if n > v then varc (numeral (n - 1)) else varc (numeral n)
  | .func sym ts => funcc (strCode sym) (substCodeTs v w ts)

/-- Versión para listas de términos (espeja `substTerms`/`termsCode`). -/
def substCodeTs (v : Nat) (w : Term) : List Term → Term
  | [] => nil
  | t :: ts => cons (substCodeT v w t) (substCodeTs v w ts)

end

/-- `substCodeF v w f` = código de la fórmula `f` con la variable `v` sustituida por el código `w`.
    Espeja `formCode`; bajo un binder sube el nivel y **levanta el testigo** (`liftc zero w`),
    igual que `prf_substfc_forall`/`_ex`. -/
def substCodeF (v : Nat) (w : Term) : Formula → Term
  | .bottom          => cons (numeral 2) nil
  | .atom p ts       => cons (numeral 3) (cons (strCode p) (cons (substCodeTs v w ts) nil))
  | .eq a b          => cons (numeral 4) (cons (substCodeT v w a) (cons (substCodeT v w b) nil))
  | .impl a b        => cons (numeral 5) (cons (substCodeF v w a) (cons (substCodeF v w b) nil))
  | Formula.forall a => cons (numeral 6) (cons (substCodeF (v + 1) (liftc zero w) a) nil)
  | .and a b         => cons (numeral 7) (cons (substCodeF v w a) (cons (substCodeF v w b) nil))
  | .or a b          => cons (numeral 8) (cons (substCodeF v w a) (cons (substCodeF v w b) nil))
  | .ex a            => cons (numeral 9) (cons (substCodeF (v + 1) (liftc zero w) a) nil)

/-! ### Cómputo de `substtc` con testigo arbitrario (espejo de `prf_substTerm_arith`) -/

mutual

/-- **`substtc` con código‑testigo arbitrario**: `substtc ⌜v⌝ w ⌜t⌝ =eq substCodeT v w t`. -/
theorem prf_substtc_arith_open (v : Nat) (w : Term) : ∀ (t : Term),
    Prf (substtc (numeral v) w (termCode t) =eq substCodeT v w t)
  | .var n => by
      show Prf (substtc (numeral v) w (varc (numeral n)) =eq substCodeT v w (.var n))
      rcases Nat.lt_trichotomy n v with hlt | heq | hgt
      · have hsub : substCodeT v w (.var n) = varc (numeral n) := by
          simp only [substCodeT]; rw [if_neg (by omega), if_neg (by omega)]
        rw [hsub]
        exact prf_mp (prf_substtc_var_lt (numeral v) w (numeral n)) (prf_gnum_lt hlt)
      · subst heq
        have hsub : substCodeT n w (.var n) = w := by simp [substCodeT]
        rw [hsub]
        exact prf_mp (prf_substtc_var_eq (numeral n) w (numeral n)) (prf_refl _)
      · have hsub : substCodeT v w (.var n) = varc (numeral (n - 1)) := by
          simp only [substCodeT]; rw [if_neg (by omega), if_pos (by omega)]
        rw [hsub]
        have hax := prf_mp (prf_substtc_var_gt (numeral v) w (numeral n)) (prf_gnum_lt hgt)
        have hpred : Prf (varc (pred (numeral n)) =eq varc (numeral (n - 1))) := by
          apply prf_congr_cons_tail; apply prf_congr_cons_head
          obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          subst hk
          simpa using prf_pred_numeral k
        exact prf_eq_trans hax hpred
  | .func sym ts => by
      show Prf (substtc (numeral v) w (funcc (strCode sym) (termsCode ts))
        =eq substCodeT v w (.func sym ts))
      have hstep := prf_substtc_func (numeral v) w (strCode sym) (termsCode ts)
      have hih := prf_substtsc_arith_open v w ts
      have hcongr : Prf (funcc (strCode sym) (substtsc (numeral v) w (termsCode ts))
          =eq funcc (strCode sym) (substCodeTs v w ts)) := by
        unfold funcc
        apply prf_congr_cons_tail; apply prf_congr_cons_tail; apply prf_congr_cons_head
        exact hih
      exact prf_eq_trans hstep hcongr

/-- Versión listas (espejo de `prf_substTerms_arith`). -/
theorem prf_substtsc_arith_open (v : Nat) (w : Term) : ∀ (ts : List Term),
    Prf (substtsc (numeral v) w (termsCode ts) =eq substCodeTs v w ts)
  | [] => prf_substtsc_nil (numeral v) w
  | t :: ts => by
      show Prf (substtsc (numeral v) w (cons (termCode t) (termsCode ts))
        =eq substCodeTs v w (t :: ts))
      have hstep := prf_substtsc_cons (numeral v) w (termCode t) (termsCode ts)
      have ih1 := prf_substtc_arith_open v w t
      have ih2 := prf_substtsc_arith_open v w ts
      exact prf_eq_trans hstep (prf_eq_trans (prf_congr_cons_head ih1) (prf_congr_cons_tail ih2))

end

/-! ### Cómputo de `substfc` con testigo arbitrario (espejo de `prf_substFormula_arith`) -/

/-- **`substfc` con código‑testigo arbitrario**: `substfc ⌜v⌝ w ⌜f⌝ =eq substCodeF v w f`.

    Es el lema que permite **usar** las instancias de axiomas codificados (`pcc_axiom_inst`) cuando
    el testigo es `tcFn a` — el primer paso de la evaluación provable. -/
theorem prf_substfc_arith_open : ∀ (v : Nat) (w : Term) (f : Formula),
    Prf (substfc (numeral v) w (formCode f) =eq substCodeF v w f)
  | v, w, .bottom => prf_substfc_bottom (numeral v) w
  | v, w, .atom p ts =>
      prf_eq_trans (prf_substfc_atom (numeral v) w (strCode p) (termsCode ts))
        (prf_congr_bin2 (prf_substtsc_arith_open v w ts))
  | v, w, .eq a b =>
      prf_eq_trans (prf_substfc_eq (numeral v) w (termCode a) (termCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_substtc_arith_open v w a))
          (prf_congr_bin2 (prf_substtc_arith_open v w b)))
  | v, w, .impl a b =>
      prf_eq_trans (prf_substfc_impl (numeral v) w (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_substfc_arith_open v w a))
          (prf_congr_bin2 (prf_substfc_arith_open v w b)))
  | v, w, .and a b =>
      prf_eq_trans (prf_substfc_and (numeral v) w (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_substfc_arith_open v w a))
          (prf_congr_bin2 (prf_substfc_arith_open v w b)))
  | v, w, .or a b =>
      prf_eq_trans (prf_substfc_or (numeral v) w (formCode a) (formCode b))
        (prf_eq_trans (prf_congr_bin1 (prf_substfc_arith_open v w a))
          (prf_congr_bin2 (prf_substfc_arith_open v w b)))
  | v, w, Formula.forall a => by
      -- bajo el binder: nivel `succ ⌜v⌝ = ⌜v+1⌝` y testigo levantado `liftc zero w`
      have hstep := prf_substfc_forall (numeral v) w (formCode a)
      have hih := prf_substfc_arith_open (v + 1) (liftc zero w) a
      refine prf_eq_trans hstep ?_
      unfold forallc
      exact prf_congr_cons_tail (prf_congr_cons_head hih)
  | v, w, .ex a => by
      have hstep := prf_substfc_ex (numeral v) w (formCode a)
      have hih := prf_substfc_arith_open (v + 1) (liftc zero w) a
      refine prf_eq_trans hstep ?_
      unfold exc
      exact prf_congr_cons_tail (prf_congr_cons_head hih)

/-! ### Chequeo de cordura: recupera la versión `termCode` -/

mutual

/-- Con `w = termCode s`, la función meta coincide con `termCode ∘ substTerm`. -/
theorem substCodeT_termCode (v : Nat) (s : Term) : ∀ t : Term,
    substCodeT v (termCode s) t = termCode (substTerm v s t)
  | .var n => by
      rcases Nat.lt_trichotomy n v with hlt | heq | hgt
      · simp only [substCodeT, substTerm]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rfl
      · subst heq; simp [substCodeT, substTerm]
      · simp only [substCodeT, substTerm]
        rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        rfl
  | .func sym ts => by
      simp only [substCodeT, substTerm, termCode, funcc, substCodeTs_termsCode v s ts]
      rfl

theorem substCodeTs_termsCode (v : Nat) (s : Term) : ∀ ts : List Term,
    substCodeTs v (termCode s) ts = termsCode (substTerms v s ts)
  | [] => rfl
  | t :: ts => by
      simp only [substCodeTs, substTerms, termsCode, substCodeT_termCode v s t,
        substCodeTs_termsCode v s ts]

end

/-! ### Sustitución de código sobre términos **cerrados** (sin variables libres)

Si `t` es cerrado (invariante bajo todo `liftTerm c`), entonces `substCodeT v w t = termCode t`
para cualquier `v`, `w`: no hay variable que sustituir, así que la función de código coincide con la
codificación literal. Es la pieza que reduce `substCodeT 0 W (formCode φ) = termCode (formCode φ)`
(un `formCode φ` es siempre cerrado, `liftTerm_formCode`), necesaria para la reflexión punteada de
`In` en `hI_dot`. -/
mutual

/-- `substCodeT` sobre un término **cerrado** coincide con `termCode`. -/
theorem substCodeT_closed (v : Nat) (w : Term) :
    ∀ t : Term, (∀ c : Nat, liftTerm c t = t) → substCodeT v w t = termCode t
  | .var n, ht => by
      have h := ht 0
      simp only [liftTerm] at h
      rw [if_neg (by omega)] at h
      injection h with hn
      omega
  | .func s ts, ht => by
      have hts : ∀ c, liftTerms c ts = ts := fun c => by
        have h := ht c; simp only [liftTerm, Term.func.injEq] at h; exact h.2
      simp only [substCodeT, termCode, funcc, numeral, substCodeTs_closed v w ts hts]

/-- Versión para listas de términos cerrados. -/
theorem substCodeTs_closed (v : Nat) (w : Term) :
    ∀ ts : List Term, (∀ c : Nat, liftTerms c ts = ts) → substCodeTs v w ts = termsCode ts
  | [], _ => rfl
  | t :: ts, hts => by
      have ht : ∀ c, liftTerm c t = t := fun c => by
        have h := hts c; simp only [liftTerms, List.cons.injEq] at h; exact h.1
      have hts' : ∀ c, liftTerms c ts = ts := fun c => by
        have h := hts c; simp only [liftTerms, List.cons.injEq] at h; exact h.2
      simp only [substCodeTs, termsCode, substCodeT_closed v w t ht, substCodeTs_closed v w ts hts']

end


/-! ## §4 · INVARIANCIA DE `substCodeT` BAJO `substtc` DE NIVEL SUPERIOR (2026‑09‑09g)

⭐ **La obligación `hPinv` de TODA aplicación de `pcc_bdAll_intro`**, en su forma genérica y a
nivel de TÉRMINO. Hasta ahora se pagaba a mano en cada frente (`hPinv_wfAll1Psi`,
`Meta/HasWitTrackedPrf.lean` §10, ~40 líneas de recorrido); esto la hace de una vez.

**El enunciado.** Si el testigo `W` es `substtc`‑invariante al nivel `v+1`, y la fórmula/término
no tiene variables libres por encima de `v+1`, entonces el código `substCodeT v W t` es
`substtc (v+1)`‑invariante.

🔑 **Por qué la condición es la que es.** `substCodeT v W (.var n)` vale `W` si `n = v`,
`⌜v_n⌝` si `n < v` y `⌜v_(n-1)⌝` si `n > v`. Para que `substtc (v+1)` no toque nada hace falta
que ningún `⌜v_(v+1)⌝` aparezca, o sea que ninguna variable libre valga `v+2`. La cota
`liftTerm (v+2) t = t` —que dice «sin variables libres ≥ v+2»— es más fuerte y **se comprueba
por `simp`** para todo término concreto, que es lo que la hace usable. -/

mutual

/-- **La invariancia, nivel TÉRMINO.** -/
theorem substtc_inv_substCodeT (v : Nat) (W : Term)
    (hW : ∀ u, Prf (substtc (numeral (v+1)) u W =eq W)) :
    ∀ (t : Term), liftTerm (v+2) t = t →
      ∀ u, Prf (substtc (numeral (v+1)) u (substCodeT v W t) =eq substCodeT v W t)
  | .var n, hfv, u => by
      have hn : Nat.le n (v + 1) := by
        rcases Nat.lt_or_ge n (v + 2) with h | h
        · exact Nat.le_of_lt_succ h
        · have hne : ¬ (n < v + 2) := Nat.not_lt.mpr h
          simp only [liftTerm, if_neg hne, Term.var.injEq] at hfv
          exact absurd hfv (Nat.succ_ne_self n)
      rcases Nat.lt_trichotomy n v with hlt | heq | hgt
      · have hsub : substCodeT v W (.var n) = varc (numeral n) := by
          simp only [substCodeT]; rw [if_neg (by omega), if_neg (by omega)]
        rw [hsub]
        exact prf_mp (prf_substtc_var_lt (numeral (v+1)) u (numeral n)) (prf_gnum_lt (by omega))
      · subst heq
        have hsub : substCodeT n W (.var n) = W := by simp [substCodeT]
        rw [hsub]; exact hW u
      · have hsub : substCodeT v W (.var n) = varc (numeral (n - 1)) := by
          simp only [substCodeT]; rw [if_neg (by omega), if_pos (by omega)]
        rw [hsub]
        have hnv : n = v + 1 := Nat.le_antisymm hn hgt
        subst hnv
        exact prf_mp (prf_substtc_var_lt (numeral (v+1)) u (numeral (v+1-1)))
          (prf_gnum_lt (by omega))
  | .func sym ts, hfv, u => by
      have hall := hfv
      simp only [liftTerm, Term.func.injEq, true_and] at hall
      show Prf (substtc (numeral (v+1)) u (funcc (strCode sym) (substCodeTs v W ts))
        =eq funcc (strCode sym) (substCodeTs v W ts))
      refine prf_eq_trans (prf_substtc_func (numeral (v+1)) u _ _) ?_
      unfold funcc
      refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
      exact substtc_inv_substCodeTs v W hW ts hall u

/-- **La invariancia, nivel LISTA.** -/
theorem substtc_inv_substCodeTs (v : Nat) (W : Term)
    (hW : ∀ u, Prf (substtc (numeral (v+1)) u W =eq W)) :
    ∀ (ts : List Term), liftTerms (v+2) ts = ts →
      ∀ u, Prf (substtsc (numeral (v+1)) u (substCodeTs v W ts) =eq substCodeTs v W ts)
  | [], _, u => by
      show Prf (substtsc (numeral (v+1)) u nil =eq nil)
      exact prf_substtsc_nil (numeral (v+1)) u
  | t :: ts, hfv, u => by
      have hall := hfv
      simp only [liftTerms, List.cons.injEq] at hall
      show Prf (substtsc (numeral (v+1)) u (cons (substCodeT v W t) (substCodeTs v W ts))
        =eq cons (substCodeT v W t) (substCodeTs v W ts))
      refine prf_eq_trans (prf_substtsc_cons (numeral (v+1)) u _ _) ?_
      exact prf_eq_trans (prf_congr_cons_head (substtc_inv_substCodeT v W hW t hall.1 u))
        (prf_congr_cons_tail (substtc_inv_substCodeTs v W hW ts hall.2 u))

end

/-! ### ⚠️ POR QUÉ ESTO NO SUBE AL NIVEL FÓRMULA SIN MÁS, y qué haría falta

El nivel fórmula funcionaría igual **salvo en los binders**. El caso

    substCodeF v w (∀a) = cons 6̄ (cons (substCodeF (v+1) (liftc 0 w) a) nil)

recursa con el testigo **`liftc 0 w`**, y la hipótesis de invariancia sobre `w` **no se
transfiere** a `liftc 0 w`: haría falta darla ya cerrada bajo `liftc 0`, o sea para todos los
lifts iterados `liftcⁿ w`. Con la hipótesis tal como está, la inducción no cierra ese caso.

⭐ Y para los testigos REALES sí vale, porque son códigos punteados y **todos los `liftc`
iterados COLAPSAN**: `prf_liftc_tcFn` da `liftc 0 ṫ ≐ ṫ`, y de ahí `substtc_inv_liftc_tcFn`
(`Meta/D3InDotPrf.lean`). ⇒ la versión fórmula es alcanzable, pero pide la hipótesis en forma
**iterada** (`∀ j, invariante (liftcⁿ W)`), no en la forma simple de arriba.

Se deja medido en vez de descubrirlo dentro de una inducción de ocho casos. -/

end ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf

export ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf (
  substCodeT substCodeTs substCodeF
  prf_substtc_arith_open prf_substtsc_arith_open prf_substfc_arith_open
  substCodeT_termCode substCodeTs_termsCode
  substCodeT_closed substCodeTs_closed
  substtc_inv_substCodeT substtc_inv_substCodeTs
)
