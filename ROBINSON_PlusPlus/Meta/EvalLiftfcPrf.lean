import ROBINSON_PlusPlus.Meta.EvalSubstfcPrf
import ROBINSON_PlusPlus.Meta.EvalLiftcPrf
/-!
# `Meta/EvalLiftfcPrf.lean` — `pcc_eval_liftfc`: la base, y la deuda MEDIDA

`pcc_eval_liftfc` es lo único que separa a C3 del cierre: bloquea **4 de los 7** reflectores de
sustitución (q3 · 11, qconf · 19, ind · 18, listInd · 20), que son exactamente los que llevan
`liftfc` (§3.47.1). Este módulo pone la **base** y deja la obligación **enunciada, no
postulada** — idioma de `Meta/Sigma1BoundedPrf.lean` y `Meta/LineWFGuardPrf.lean`.

## Lo que la medición encontró, y que reclasifica una tarea

⚠️⚠️ **`pcc_eval_liftc` sólo vale a nivel `zero`.**

    pcc_eval_liftc (w s) (h : isTC1 w s) :
      Prf (provFromCode (eqc (liftcT (termCode zero) ṡ) ((liftc zero s)˙)))

(`Meta/EvalLiftcPrf.lean`, B2 · el DESCENSO). Y los axiomas `ax_liftfc_forall` / `ax_liftfc_ex`
**suben el nivel**:

    liftfc c (forallc a) = forallc (liftfc (σc) a)
    liftfc c (exc a)     = exc     (liftfc (σc) a)

⇒ una inducción sobre el código de fórmula **no puede quedarse en el nivel 0**: el predicado
tiene que cuantificar el nivel, y los casos `atom`/`eq` bajan a `liftsc`/`liftc` **a ese nivel**.

🔑 **Por tanto A5 —«generalizar más allá del nivel `zero`»— no es una mejora opcional: es
PRERREQUISITO de `pcc_eval_liftfc`, y por tanto de los cuatro tags que faltan.** Estaba
catalogada como generalización suelta; está en la ruta crítica.

## Lo que sí está, medido

* ✅ **Las ocho ecuaciones objeto** ya existen y son **genéricas en el nivel**:
  `prf_liftfc_bottom/atom/eq/impl/forall/and/or/ex` (`Meta/ArithPrf.lean:386-442`).
* ✅ La maquinaria de inducción fuerte es **genérica en `Φ`** (`prf_strong_induction`,
  `psi_lift_form1/2/3`, `PSI_inst*`, `Meta/StrongInductionPrf.lean`).
* ✅ El chasis de B3.4 (`pcc_eval_substfc_modulo_8`) es el **molde**: predicado + gate +
  instanciación de binders + un paso de 41 líneas que delega en ocho `Caso*`.
  ⚠️ **No es reutilizable tal cual**: sus `Caso*` están escritos sobre `targetSubstfc v s X`.
  Hacerlo genérico en el operador obligaría a refactorizar en vivo un módulo de 1 625 líneas
  que está en la ruta crítica de todo lo demás — se mide antes de tocarlo.
* ❌ `liftfcT` **no existía**: la imagen dotada de `liftfc`. Entra aquí, y **como DEFINICIÓN**
  (⛔ postular su ecuación de recursión como axioma OBJETO hace la teoría INCONSISTENTE — es la
  regla que ADR‑015/020 fijaron para `substfcT`).
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
open ROBINSON_PlusPlus.Meta.TrackedCorePrf ROBINSON_PlusPlus.Meta.EvalLiftcPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.EvalLiftfcPrf

/-! ## §1 · LA IMAGEN DOTADA DE `liftfc`, Y EL OBJETIVO

⛔ `liftfcT` entra como **definición**, igual que `substfcT` (`Meta/EvalArithPrf.lean:184`) y
`liftcT` (`Meta/LiftcCodePrf.lean:111`). Nunca como axioma. -/

/-- `⌜liftfc c f⌝` como constructor de código. -/
def liftfcT (c f : Term) : Term := funcc (strCode "liftfc") (cons c (cons f nil))

/-- El puente definicional con `termCode`: es lo que `formCode` produce de un `liftfc`. -/
theorem liftfcT_termCode (c f : Term) :
    liftfcT (termCode c) (termCode f) = termCode (liftfc c f) := rfl

/-- El código de la ecuación que hay que probar dentro de `Prov`. -/
def evalLiftfcCode (v X : Term) : Term :=
  eqc (liftfcT (tcFn v) (tcFn X)) (tcFn (liftfc v X))

/-- **EL OBJETIVO**: la evaluación provable de `liftfc`, con `v` y `X` abstractos. -/
def targetLiftfc (v X : Term) : Formula := provFromCode (evalLiftfcCode v X)

/-! ### Naturalidad (la piden el predicado de la inducción y su gate) -/

theorem liftTerm_evalLiftfcCode (k : Nat) (v X : Term) :
    liftTerm k (evalLiftfcCode v X)
      = evalLiftfcCode (liftTerm k v) (liftTerm k X) := by
  simp only [evalLiftfcCode, liftfcT, eqc, funcc, tcFn, liftfc, cons, nil, zero, succ,
    liftTerm, liftTerms, liftTerm_strCode]

theorem substTerm_evalLiftfcCode (k : Nat) (u v X : Term) :
    substTerm k u (evalLiftfcCode v X)
      = evalLiftfcCode (substTerm k u v) (substTerm k u X) := by
  simp only [evalLiftfcCode, liftfcT, eqc, funcc, tcFn, liftfc, cons, nil, zero, succ,
    substTerm, substTerms, substTerm_strCode]

theorem liftF_targetLiftfc (k : Nat) (v X : Term) :
    liftFormula k (targetLiftfc v X) = targetLiftfc (liftTerm k v) (liftTerm k X) := by
  simp only [targetLiftfc, liftFormula_provFromCode_open, liftTerm_evalLiftfcCode]

theorem substF_targetLiftfc (k : Nat) (u v X : Term) :
    substFormula k u (targetLiftfc v X) = targetLiftfc (substTerm k u v) (substTerm k u X) := by
  simp only [targetLiftfc, substFormula_provFromCode_open, substTerm_evalLiftfcCode]

/-! ### CONTROLES NEGATIVOS: el enunciado no es una reflexividad disfrazada

Mismo control que `Meta/EvalLiftcPrf.lean` pone sobre `liftcT`/`liftscT`. Sin él, un objetivo
como éste puede ser cierto por `rfl` y no decir nada. -/

example (v X : Term) : True := by
  fail_if_success
    exact (rfl : liftfcT (tcFn v) (tcFn X) = tcFn (liftfc v X))
  trivial

/-- Y el control POSITIVO de que la imagen es la buena: `liftfcT` **es** lo que `formCode`
    produce de un `liftfc` (ya está arriba como `liftfcT_termCode`, aquí sobre un caso real). -/
example (X : Term) :
    termCode (liftfc zero X) = liftfcT (termCode zero) (termCode X) := rfl


/-! ## §1bis · FONTANERÍA de `liftfcT` — espejo literal de la de `liftcT` (§1–§2 de
    `Meta/LiftcCodePrf.lean`). Cinco líneas por pieza, cero contenido nuevo: `liftfcT` es un
    `funcc` binario, así que todo sale del mismo escalón §28 del KIT. -/

theorem prf_hasWit_liftfcT {c f : Term} (hc : Prf (hasWit c)) (hf : Prf (hasWit f)) :
    Prf (hasWit (liftfcT c f)) := prf_hasWit_funcc2 (strCode "liftfc") c f hc hf

theorem prf_congr_liftfcT {c c' f f' : Term} (hc : Prf (c =eq c')) (hf : Prf (f =eq f')) :
    Prf (liftfcT c f =eq liftfcT c' f') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head hf)))

theorem prf_substtc_liftfcT (v W x y : Term) :
    Prf (substtc v W (liftfcT x y) =eq liftfcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftfc") x y

theorem substtc_inv_liftfcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftfcT X Y) =eq liftfcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftfcT zero W X Y) (prf_congr_liftfcT (hX W) (hY W))

/-! ### Los tags: `liftfc` recorre los MISMOS constructores del KIT que `formCode`

⭐ Ni un constructor nuevo. `botc = nulT 2`, `implc = binT 5`, `forallc = unT 6`,
`andc = binT 7`, `orc = binT 8`, `exc = unT 9` — y los puentes son `rfl`. -/

theorem botcT_termCode : nulT 2 = termCode botc := rfl
theorem implcT_termCode (a b : Term) : binT 5 (termCode a) (termCode b) = termCode (implc a b) := rfl
theorem forallcT_termCode (a : Term) : unT 6 (termCode a) = termCode (forallc a) := rfl
theorem andcT_termCode (a b : Term) : binT 7 (termCode a) (termCode b) = termCode (andc a b) := rfl
theorem orcT_termCode (a b : Term) : binT 8 (termCode a) (termCode b) = termCode (orc a b) := rfl
theorem excT_termCode (a : Term) : unT 9 (termCode a) = termCode (exc a) := rfl

/-! ## §3 · LAS ECUACIONES DE `liftfc`, DOTADAS

Receta idéntica a la de §4 de `Meta/LiftcCodePrf.lean`: `prf_substfc_arith_open` calcula el
`substfc` sobre el `formCode` explícito, y `pcc_axiom_inst1/2/3` mete la instancia dentro de
`Prov`. ⚠️ Las ocho son **libres de cuantificador**: ni un `bdAllCode`.

Aquí entran las **seis** que NO piden A5 (tag 2, 5, 7, 8 y 6, 9). Las de `atom` (3) y `eq` (4)
bajan a `liftsc`/`liftc` al nivel corriente y consumen `pcc_eval_liftsc_at`/`_liftc_at`. -/

def LIFTFC_BOT_BODY : Formula := liftfc (.var 0) botc =eq botc
theorem LIFTFC_BOT_BODY_ok : ax_liftfc_bottom = forall_ LIFTFC_BOT_BODY := rfl

/-- **`ax_liftfc_bottom` DOTADA**: `⊢ Prov(⌜ liftfc(ċ, ⌜⊥⌝) = ⌜⊥⌝ ⌝)`, con `c` ABSTRACTO. -/
theorem pcc_liftfc_bottom_code (c : Term) :
    Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (nulT 2)) (nulT 2))) := by
  have hin : Prf (substfc zero (tcFn c) (formCode LIFTFC_BOT_BODY)
      =eq eqCodeFn (liftfcT (tcFn c) (nulT 2)) (nulT 2)) :=
    prf_substfc_arith_open 0 (tcFn c) LIFTFC_BOT_BODY
  exact prf_mp (prf_provCode_congr hin)
    (pcc_axiom_inst LIFTFC_BOT_BODY (show ax_liftfc_bottom ∈ axioms by simp [axioms])
      (tcFn c) (prf_hasWit_tcFn (liftTerm 0 c)))

/-! ### Las tres BINARIAS (`implc` · 5, `andc` · 7, `orc` · 8), de una vez

⭐ Las tres tienen **la misma forma** (`liftfc c (binK a b) = binK (liftfc c a) (liftfc c b)`),
así que se prueban con UN lema genérico en el tag y en el cuerpo, y se instancian tres veces.
Es la lección de *medir la forma*: tres pruebas de 40 líneas serían tres copias. -/

def LIFTFC_BIN_BODY (k : Nat) : Formula :=
  liftfc (.var 2) (cons (numeralM k) (cons (.var 1) (cons (.var 0) nil)))
    =eq cons (numeralM k) (cons (liftfc (.var 2) (.var 1)) (cons (liftfc (.var 2) (.var 0)) nil))

theorem LIFTFC_IMPL_BODY_ok : ax_liftfc_impl = forall_3 (LIFTFC_BIN_BODY 5) := rfl
theorem LIFTFC_AND_BODY_ok  : ax_liftfc_and  = forall_3 (LIFTFC_BIN_BODY 7) := rfl
theorem LIFTFC_OR_BODY_ok   : ax_liftfc_or   = forall_3 (LIFTFC_BIN_BODY 8) := rfl

/-- **Las tres ecuaciones BINARIAS de `liftfc`, DOTADAS de una vez** (genérico en el tag).

    ⚠️ **El `hin` entra como PARÁMETRO, y no es cosmética**: con `k` variable, el `numeralM k`
    de dentro del cuerpo **bloquea el cómputo** de `substCodeF`, así que
    `prf_substfc_arith_open` ya no casa por defeq con la forma explícita. Con el tag CONCRETO
    sí computa. Sacarlo fuera deja las 40 líneas compartidas y una línea por tag. -/
theorem pcc_liftfc_bin_code (k : Nat) (hmem : forall_3 (LIFTFC_BIN_BODY k) ∈ axioms)
    (c a b : Term)
    (hin : Prf (substfc (succ (succ zero)) (liftc zero (liftc zero (tcFn c)))
        (formCode (LIFTFC_BIN_BODY k))
      =eq eqCodeFn
        (liftfcT (liftc zero (liftc zero (tcFn c)))
          (binT k (varc (numeral 1)) (varc (numeral 0))))
        (binT k (liftfcT (liftc zero (liftc zero (tcFn c))) (varc (numeral 1)))
                (liftfcT (liftc zero (liftc zero (tcFn c))) (varc (numeral 0)))))) :
    Prf (provFromCode (eqCodeFn
      (liftfcT (tcFn c) (binT k (tcFn a) (tcFn b)))
      (binT k (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftfcT W2 (binT k (varc (numeral 1)) (varc (numeral 0))))
                   (binT k (liftfcT W2 (varc (numeral 1))) (liftfcT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT k (varc (numeral 1)) (varc (numeral 0))))
                   (binT k (liftfcT (tcFn c) (varc (numeral 1)))
                           (liftfcT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftfcT hA2 (prf_refl _))
      (prf_congr_binT (prf_congr_liftfcT hA2 (prf_refl _))
                      (prf_congr_liftfcT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn a)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftfcT (tcFn c) (binT k (varc (numeral 1)) (varc (numeral 0))))
        (binT k (liftfcT (tcFn c) (varc (numeral 1))) (liftfcT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT k (tcFn a) (varc (numeral 0))))
                   (binT k (liftfcT (tcFn c) (tcFn a))
                           (liftfcT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftfcT (succ zero) W1 _ _) ?_
      refine prf_congr_liftfcT hc1 ?_
      exact prf_eq_trans (prf_substtc_binT_at k 1 W1 _ _) (prf_congr_binT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_binT_at k 1 W1 _ _) ?_
      refine prf_congr_binT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftfcT (succ zero) W1 _ _) (prf_congr_liftfcT hc1 hv1)
      · exact prf_eq_trans (prf_substtc_liftfcT (succ zero) W1 _ _) (prf_congr_liftfcT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftfcT (tcFn c) (binT k (tcFn a) (varc (numeral 0))))
        (binT k (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT k (tcFn a) (tcFn b)))
                   (binT k (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b)))) := by
    have hb : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
    have hcz : Prf (substtc zero W0 (tcFn c) =eq tcFn c) := prf_substtc_tcFn W0 c
    have haz : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftfcT zero W0 _ _) ?_
      refine prf_congr_liftfcT hcz ?_
      exact prf_eq_trans (prf_substtc_binT_at k 0 W0 _ _) (prf_congr_binT haz hb)
    · refine prf_eq_trans (prf_substtc_binT_at k 0 W0 _ _) ?_
      refine prf_congr_binT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftfcT zero W0 _ _) (prf_congr_liftfcT hcz haz)
      · exact prf_eq_trans (prf_substtc_liftfcT zero W0 _ _) (prf_congr_liftfcT hcz hb)
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode (LIFTFC_BIN_BODY k))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT k (tcFn a) (tcFn b)))
                   (binT k (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 (LIFTFC_BIN_BODY k) hmem (tcFn c) (tcFn a) (tcFn b)
      (prf_hasWit_tcFn (liftTerm 0 c)) (prf_hasWit_tcFn (liftTerm 0 a))
      (prf_hasWit_tcFn (liftTerm 0 b)))

theorem pcc_liftfc_impl_code (c a b : Term) :
    Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (binT 5 (tcFn a) (tcFn b)))
      (binT 5 (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b))))) :=
  pcc_liftfc_bin_code 5 (show ax_liftfc_impl ∈ axioms by simp [axioms]) c a b
    (prf_substfc_arith_open 2 (liftc zero (liftc zero (tcFn c))) (LIFTFC_BIN_BODY 5))

theorem pcc_liftfc_and_code (c a b : Term) :
    Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (binT 7 (tcFn a) (tcFn b)))
      (binT 7 (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b))))) :=
  pcc_liftfc_bin_code 7 (show ax_liftfc_and ∈ axioms by simp [axioms]) c a b
    (prf_substfc_arith_open 2 (liftc zero (liftc zero (tcFn c))) (LIFTFC_BIN_BODY 7))

theorem pcc_liftfc_or_code (c a b : Term) :
    Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (binT 8 (tcFn a) (tcFn b)))
      (binT 8 (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b))))) :=
  pcc_liftfc_bin_code 8 (show ax_liftfc_or ∈ axioms by simp [axioms]) c a b
    (prf_substfc_arith_open 2 (liftc zero (liftc zero (tcFn c))) (LIFTFC_BIN_BODY 8))

/-! ### Las dos UNARIAS (`forallc` · 6, `exc` · 9) — ⚠️ **las que SUBEN el nivel**

`liftfc c (forallc a) = forallc (liftfc (σc) a)`. El `σ` del lado derecho es lo que obliga a
que el nivel vaya cuantificado dentro del predicado de la inducción, igual que en A5. -/

def LIFTFC_UN_BODY (k : Nat) : Formula :=
  liftfc (.var 1) (cons (numeralM k) (cons (.var 0) nil))
    =eq cons (numeralM k) (cons (liftfc (succ (.var 1)) (.var 0)) nil)

theorem LIFTFC_FORALL_BODY_ok : ax_liftfc_forall = forall_2 (LIFTFC_UN_BODY 6) := rfl
theorem LIFTFC_EX_BODY_ok : ax_liftfc_ex = forall_2 (LIFTFC_UN_BODY 9) := rfl

/-- **Las dos ecuaciones UNARIAS de `liftfc`, DOTADAS** (genérico en el tag). ⚠️ El nivel del
    lado derecho es `succcT ċ`, no `ċ`: es el `σ` que sube. -/
theorem pcc_liftfc_un_code (k : Nat) (hmem : forall_2 (LIFTFC_UN_BODY k) ∈ axioms) (c a : Term)
    (hin : Prf (substfc (succ zero) (liftc zero (tcFn c)) (formCode (LIFTFC_UN_BODY k))
      =eq eqCodeFn (liftfcT (liftc zero (tcFn c)) (unT k (varc (numeral 0))))
                   (unT k (liftfcT (succcT (liftc zero (tcFn c))) (varc (numeral 0)))))) :
    Prf (provFromCode (eqCodeFn
      (liftfcT (tcFn c) (unT k (tcFn a)))
      (unT k (liftfcT (succcT (tcFn c)) (tcFn a))))) := by
  let W1 : Term := liftc zero (tcFn c)
  let W0 : Term := tcFn a
  have hA1 : Prf (W1 =eq tcFn c) := prf_liftc_tcFn c
  have hnorm : Prf (eqCodeFn (liftfcT W1 (unT k (varc (numeral 0))))
                   (unT k (liftfcT (succcT W1) (varc (numeral 0))))
      =eq eqCodeFn (liftfcT (tcFn c) (unT k (varc (numeral 0))))
                   (unT k (liftfcT (succcT (tcFn c)) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftfcT hA1 (prf_refl _))
      (prf_congr_unT (prf_congr_liftfcT (prf_congr_succcT hA1) (prf_refl _)))
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftfcT (tcFn c) (unT k (varc (numeral 0))))
        (unT k (liftfcT (succcT (tcFn c)) (varc (numeral 0)))))
      =eq eqCodeFn (liftfcT (tcFn c) (unT k (tcFn a)))
                   (unT k (liftfcT (succcT (tcFn c)) (tcFn a)))) := by
    have hb : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn a) := prf_substtc_varc0 W0
    have hcz : Prf (substtc zero W0 (tcFn c) =eq tcFn c) := prf_substtc_tcFn W0 c
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftfcT zero W0 _ _) ?_
      refine prf_congr_liftfcT hcz ?_
      exact prf_eq_trans (prf_substtc_unT_at k 0 W0 _) (prf_congr_unT hb)
    · refine prf_eq_trans (prf_substtc_unT_at k 0 W0 _) ?_
      refine prf_congr_unT ?_
      refine prf_eq_trans (prf_substtc_liftfcT zero W0 _ _) ?_
      exact prf_congr_liftfcT
        (prf_eq_trans (prf_substtc_succcT zero W0 (tcFn c)) (prf_congr_succcT hcz)) hb
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1 (formCode (LIFTFC_UN_BODY k)))
      =eq eqCodeFn (liftfcT (tcFn c) (unT k (tcFn a)))
                   (unT k (liftfcT (succcT (tcFn c)) (tcFn a)))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 (LIFTFC_UN_BODY k) hmem (tcFn c) (tcFn a)
      (prf_hasWit_tcFn (liftTerm 0 c)) (prf_hasWit_tcFn (liftTerm 0 a)))

theorem pcc_liftfc_forall_code (c a : Term) :
    Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (unT 6 (tcFn a)))
      (unT 6 (liftfcT (succcT (tcFn c)) (tcFn a))))) :=
  pcc_liftfc_un_code 6 (show ax_liftfc_forall ∈ axioms by simp [axioms]) c a
    (prf_substfc_arith_open 1 (liftc zero (tcFn c)) (LIFTFC_UN_BODY 6))

theorem pcc_liftfc_ex_code (c a : Term) :
    Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (unT 9 (tcFn a)))
      (unT 9 (liftfcT (succcT (tcFn c)) (tcFn a))))) :=
  pcc_liftfc_un_code 9 (show ax_liftfc_ex ∈ axioms by simp [axioms]) c a
    (prf_substfc_arith_open 1 (liftc zero (tcFn c)) (LIFTFC_UN_BODY 9))

/-! ## §2 · LA DEUDA, ENUNCIADA (cero `axiom`)

Idioma de `Meta/LineWFGuardPrf.lean`: se enuncia, no se postula. -/

/-- **La obligación**: `liftfc` evaluado dentro de `Prov`, con el nivel `v` y el código `X`
    **abstractos**, bajo la guarda de buena formación de ADR‑020.

    ⚠️ Nótese que la guarda es **sólo** `hasWitF X`: `liftfc` no tiene sustituyendo, así que no
    hay `hasWit s` que arrastrar. Es más barata que la de `substfc` en ese punto. -/
abbrev DEUDA_evalLiftfc : Prop :=
  ∀ v X : Term, Prf (Formula.impl (hasWitF X) (targetLiftfc v X))

/-- La forma **guardada por el testigo explícito**, que es la que la inducción produce
    (espeja `pcc_eval_substfc`, cuyo antecedente es `isFC1 wF wT f`). -/
abbrev DEUDA_evalLiftfc_isFC1 : Prop :=
  ∀ wF wT v X : Term, Prf (Formula.impl (isFC1 wF wT X) (targetLiftfc v X))

/-- Y el puente entre las dos: el `∃∃` de `hasWitF` se elimina como en C3‑F. -/
theorem deuda_of_isFC1 (h : DEUDA_evalLiftfc_isFC1) : DEUDA_evalLiftfc := by
  intro v X
  refine prf_ex_elim_imp ?_
  refine PrfH.mp _ _ _ ?_ (prfH_hyp_self _)
  refine prf_to_prfH ?_ _
  refine prf_ex_elim_imp ?_
  refine PrfH.mp _ _ _ ?_ (prfH_hyp_self _)
  simpa only [liftFormula, liftF_targetLiftfc, liftF_isFC1, liftTerm, Nat.reduceAdd,
    Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true]
    using prf_to_prfH (h (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 v))
      (liftTerm 0 (liftTerm 0 X))) _

end ROBINSON_PlusPlus.Meta.EvalLiftfcPrf

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es el caso `lift` de `PrfH_tc_objAt` (`Meta/SubstTreeReflect.lean`), que
cerraría los cuatro tags que faltan. Nada lo consume todavía, y se dice en vez de fingir una
medición de consumo. -/
export ROBINSON_PlusPlus.Meta.EvalLiftfcPrf (
  liftfcT liftfcT_termCode evalLiftfcCode targetLiftfc
  liftTerm_evalLiftfcCode substTerm_evalLiftfcCode
  liftF_targetLiftfc substF_targetLiftfc
  DEUDA_evalLiftfc DEUDA_evalLiftfc_isFC1 deuda_of_isFC1
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.liftfcT_termCode
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.deuda_of_isFC1
