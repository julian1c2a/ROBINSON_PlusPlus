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
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.MpCodePrf

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


/-! ## §4 · EL CHASIS — la inducción fuerte sobre códigos de FÓRMULA

Molde: `pcc_eval_substfc_modulo_8` (`Meta/EvalSubstfcPrf.lean`, B3.4). ⭐ Aquí sale **un binder
más barato**: `liftfc` no tiene sustituyendo, así que no hay `s`, no hay `hasWit s` en la guarda
y **no hace falta `HasWitLift`** (la clausura del testigo bajo `liftc zero`, que en `substfc` es
una obligación aparte). Los binders internos son TRES — `wF`, `wT`, `c` — y el código sobre el
que se induce es `#3`.

🔑 El **nivel `c` va cuantificado DENTRO de `Φ`**, por la razón de siempre (el gate
`liftFormula 1 Φ = Φ`) y además por una razón propia de este frente: los casos `forallc`/`exc`
lo **cambian** (`σc`), así que la HI tiene que estar disponible a *otro* nivel del que se
concluye. Es la misma forma que el `v`/`s` de `substfc` en su `CasoUn`. -/

/-- La guarda: aquí es **sólo** el testigo de fórmula. Sin `hasWit s`: no hay `s`. -/
def BODYliftfc (wF wT c X : Term) : Formula :=
  Formula.impl (isFC1 wF wT X) (targetLiftfc c X)

theorem liftF_BODYliftfc (k : Nat) (wF wT c X : Term) :
    liftFormula k (BODYliftfc wF wT c X)
      = BODYliftfc (liftTerm k wF) (liftTerm k wT) (liftTerm k c) (liftTerm k X) := by
  simp only [BODYliftfc, liftFormula, liftF_isFC1, liftF_targetLiftfc]

theorem substF_BODYliftfc (k : Nat) (u wF wT c X : Term) :
    substFormula k u (BODYliftfc wF wT c X)
      = BODYliftfc (substTerm k u wF) (substTerm k u wT) (substTerm k u c) (substTerm k u X) := by
  simp only [BODYliftfc, substFormula, substF_isFC1, substF_targetLiftfc]

/-- `#3` es el CÓDIGO; `#2` = `wF`, `#1` = `wT`, `#0` = `c`. -/
def PHIliftfcBody : Formula := BODYliftfc (.var 2) (.var 1) (.var 0) (.var 3)

def PHIliftfc : Formula := Formula.forall (Formula.forall (Formula.forall PHIliftfcBody))

/-- **EL GATE de `prf_strong_induction`.** -/
theorem hPHIliftfc : liftFormula 1 PHIliftfc = PHIliftfc := by
  simp only [PHIliftfc, PHIliftfcBody, liftFormula, liftF_BODYliftfc, liftTerm, Nat.reduceAdd,
    Nat.reduceLT, reduceIte]

/-! ### Instanciación de los tres binders -/

theorem PHIliftfc_at (t : Term) :
    substFormula 0 t PHIliftfc
      = Formula.forall (Formula.forall (Formula.forall
          (BODYliftfc (.var 2) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 (liftTerm 0 t)))))) := by
  simp only [PHIliftfc, PHIliftfcBody, substFormula, substF_BODYliftfc, substTerm, Nat.reduceAdd,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, if_true]

theorem PHIl_spec1 (t wF : Term) :
    substFormula 0 wF (Formula.forall (Formula.forall
        (BODYliftfc (.var 2) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 (liftTerm 0 t))))))
      = Formula.forall (Formula.forall
          (BODYliftfc (liftTerm 0 (liftTerm 0 wF)) (.var 1) (.var 0)
            (liftTerm 0 (liftTerm 0 t)))) := by
  simp only [substFormula, substF_BODYliftfc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift]

theorem PHIl_spec2 (t wF wT : Term) :
    substFormula 0 wT (Formula.forall
        (BODYliftfc (liftTerm 0 (liftTerm 0 wF)) (.var 1) (.var 0) (liftTerm 0 (liftTerm 0 t))))
      = Formula.forall (BODYliftfc (liftTerm 0 wF) (liftTerm 0 wT) (.var 0) (liftTerm 0 t)) := by
  simp only [substFormula, substF_BODYliftfc, substTerm, Nat.reduceAdd, Nat.reduceEqDiff,
    Nat.reduceGT, Nat.reduceSub, reduceIte, if_true, FOL.substTerm_liftLift]

theorem PHIl_spec3 (t wF wT c : Term) :
    substFormula 0 c (BODYliftfc (liftTerm 0 wF) (liftTerm 0 wT) (.var 0) (liftTerm 0 t))
      = BODYliftfc wF wT c t := by
  simp only [substF_BODYliftfc, substTerm, FOL.substTerm_liftTerm, if_true]

theorem PHIliftfc_use {Γ : List Formula} (t wF wT c : Term)
    (h : PrfH Γ (substFormula 0 t PHIliftfc)) : PrfH Γ (BODYliftfc wF wT c t) := by
  rw [PHIliftfc_at] at h
  have h1 := PrfH_spec h wF
  rw [PHIl_spec1] at h1
  have h2 := PrfH_spec h1 wT
  rw [PHIl_spec2] at h2
  have h3 := PrfH_spec h2 c
  rwa [PHIl_spec3] at h3

/-! ### El `PSI` de la inducción fuerte, en la forma que se usa DENTRO del paso -/

def PSIatL (X : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 X)) PHIliftfc)

theorem PSIatL_inst {Γ : List Formula} {X : Term} (h : PrfH Γ (PSIatL X)) (z : Term) :
    PrfH Γ (Formula.impl (lt z X) (substFormula 0 z PHIliftfc)) := by
  have hi := PrfH_spec h z
  have e : substFormula 0 z (Formula.impl (lt (.var 0) (liftTerm 0 X)) PHIliftfc)
      = Formula.impl (lt z X) (substFormula 0 z PHIliftfc) := by
    simp only [substFormula, lt, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  rwa [e] at hi

/-- **LA HIPÓTESIS DE INDUCCIÓN, ya instanciada**: si `z < X` y `z` tiene testigo de fórmula,
    vale el objetivo en `z` **al nivel `c'` que se quiera** — que es lo que consume el caso
    `forallc`/`exc`, donde el nivel sube a `σc`. -/
theorem IHl_at {Γ : List Formula} {X : Term} (hpsi : PrfH Γ (PSIatL X)) (z : Term)
    (hlt : PrfH Γ (lt z X)) (wF wT c' : Term)
    (hguard : PrfH Γ (isFC1 wF wT z)) : PrfH Γ (targetLiftfc c' z) :=
  PrfH.mp _ _ _ (PHIliftfc_use z wF wT c' (PrfH.mp _ _ _ (PSIatL_inst hpsi z) hlt)) hguard

/-! ## §5 · LOS OCHO CASOS, con el enunciado EXACTO que el paso consume

⭐ Compárense con los de `substfc`: **ninguno lleva `hasWit s`**, y `CasoUnL` pide la HI a
nivel `σc` en vez de a `(σv, liftc 0 s)`. No hay `HasWitLift`. -/

/-- tag 2 · `botc`. -/
def CasoBotL : Prop := ∀ c X : Term, Prf (Formula.impl (clBot X) (targetLiftfc c X))

/-- tag 3 · `atomc`. ⛔ Consume `pcc_eval_liftsc_at` (A5). No se descarga en este tramo. -/
def CasoAtomL : Prop := ∀ wT c X : Term,
  Prf (Formula.impl (land (wfAll1 wT) (clAtom wT X)) (targetLiftfc c X))

/-- tag 4 · `eqc`. ⛔ Consume `pcc_eval_liftc_at` (A5) DOS veces. -/
def CasoEqL : Prop := ∀ wT c X : Term,
  Prf (Formula.impl (land (wfAll1 wT) (clEq wT X)) (targetLiftfc c X))

/-- tags 5/7/8 · `implc`/`andc`/`orc`: el nivel NO cambia. -/
def CasoBinL (k : Nat) : Prop := ∀ c X : Term,
  Prf (Formula.impl
    (land (shapeBin X k)
      (land (targetLiftfc c (nthc X (numeralM 1))) (targetLiftfc c (nthc X (numeralM 2)))))
    (targetLiftfc c X))

/-- tags 6/9 · `forallc`/`exc`: ⚠️ el nivel **SUBE** en la hipótesis. -/
def CasoUnL (k : Nat) : Prop := ∀ c X : Term,
  Prf (Formula.impl
    (land (shapeUn X k) (targetLiftfc (succ c) (nthc X (numeralM 1))))
    (targetLiftfc c X))

/-! ## §6 · EL PASO INDUCTIVO — las ocho ramas -/

/-- Todo lo que la rama necesita del contexto, en UNA fórmula. Una conjunción menos que la de
    `substfc`, porque no hay `hasWit s`. -/
def CTXFliftfc (wF wT X : Term) : Formula :=
  land (land (PSIatL X) (wfAll1 wT)) (wfAllF wF wT)

section RamasL
variable (wF wT c X : Term)

theorem ramaL_bot (hbot : CasoBotL) :
    Prf (Formula.impl (clBot X) (Formula.impl (CTXFliftfc wF wT X) (targetLiftfc c X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFliftfc wF wT X) [clBot X] rfl)
  exact PrfH.mp _ _ _ (prf_to_prfH (hbot c X) _)
    (PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))

theorem ramaL_atom (hatom : CasoAtomL) :
    Prf (Formula.impl (clAtom wT X) (Formula.impl (CTXFliftfc wF wT X) (targetLiftfc c X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFliftfc wF wT X) [clAtom wT X] rfl)
  have hcl : PrfH [CTXFliftfc wF wT X, clAtom wT X] (clAtom wT X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXFliftfc wF wT X, clAtom wT X] (CTXFliftfc wF wT X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwT := PrfH_and_elim_right (PrfH_and_elim_left hctx)
  exact PrfH.mp _ _ _ (prf_to_prfH (hatom wT c X) _) (PrfH_and_intro hwT hcl)

theorem ramaL_eq (heq : CasoEqL) :
    Prf (Formula.impl (clEq wT X) (Formula.impl (CTXFliftfc wF wT X) (targetLiftfc c X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFliftfc wF wT X) [clEq wT X] rfl)
  have hcl : PrfH [CTXFliftfc wF wT X, clEq wT X] (clEq wT X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXFliftfc wF wT X, clEq wT X] (CTXFliftfc wF wT X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hwT := PrfH_and_elim_right (PrfH_and_elim_left hctx)
  exact PrfH.mp _ _ _ (prf_to_prfH (heq wT c X) _) (PrfH_and_intro hwT hcl)

theorem ramaL_bin (k : Nat) (hbin : CasoBinL k) :
    Prf (Formula.impl (clBin wF X k)
      (Formula.impl (CTXFliftfc wF wT X) (targetLiftfc c X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFliftfc wF wT X) [clBin wF X k] rfl)
  have hcl : PrfH [CTXFliftfc wF wT X, clBin wF X k] (clBin wF X k) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXFliftfc wF wT X, clBin wF X k] (CTXFliftfc wF wT X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hpsi := PrfH_and_elim_left (PrfH_and_elim_left hctx)
  have hwT := PrfH_and_elim_right (PrfH_and_elim_left hctx)
  have hwF := PrfH_and_elim_right hctx
  have hshape := PrfH_and_elim_left hcl
  have hin1 := PrfH_and_elim_left (PrfH_and_elim_right hcl)
  have hin2 := PrfH_and_elim_right (PrfH_and_elim_right hcl)
  have hlt1 : PrfH [CTXFliftfc wF wT X, clBin wF X k] (lt (nthc X (numeralM 1)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.descenso_bin1 X k) _) hshape
  have hlt2 : PrfH [CTXFliftfc wF wT X, clBin wF X k] (lt (nthc X (numeralM 2)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.descenso_bin2 X k) _) hshape
  have hIH1 : PrfH [CTXFliftfc wF wT X, clBin wF X k] (targetLiftfc c (nthc X (numeralM 1))) :=
    IHl_at hpsi _ hlt1 wF wT c (PrfH_and_intro (PrfH_and_intro hwT hwF) hin1)
  have hIH2 : PrfH [CTXFliftfc wF wT X, clBin wF X k] (targetLiftfc c (nthc X (numeralM 2))) :=
    IHl_at hpsi _ hlt2 wF wT c (PrfH_and_intro (PrfH_and_intro hwT hwF) hin2)
  exact PrfH.mp _ _ _ (prf_to_prfH (hbin c X) _)
    (PrfH_and_intro hshape (PrfH_and_intro hIH1 hIH2))

/-- ⚠️ **La rama donde el nivel SUBE.** La HI se instancia a `σc`, y eso es legal porque el
    nivel va **cuantificado dentro de `Φ`** — exactamente la razón de §4. -/
theorem ramaL_un (k : Nat) (hun : CasoUnL k) :
    Prf (Formula.impl (clUn wF X k)
      (Formula.impl (CTXFliftfc wF wT X) (targetLiftfc c X))) := by
  refine prf_deduction (deduction_aux ?_ (CTXFliftfc wF wT X) [clUn wF X k] rfl)
  have hcl : PrfH [CTXFliftfc wF wT X, clUn wF X k] (clUn wF X k) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hctx : PrfH [CTXFliftfc wF wT X, clUn wF X k] (CTXFliftfc wF wT X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hpsi := PrfH_and_elim_left (PrfH_and_elim_left hctx)
  have hwT := PrfH_and_elim_right (PrfH_and_elim_left hctx)
  have hwF := PrfH_and_elim_right hctx
  have hshape := PrfH_and_elim_left hcl
  have hin1 := PrfH_and_elim_right hcl
  have hlt1 : PrfH [CTXFliftfc wF wT X, clUn wF X k] (lt (nthc X (numeralM 1)) X) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (ROBINSON_PlusPlus.Meta.EvalSubstfcPrf.descenso_un X k) _) hshape
  have hIH1 : PrfH [CTXFliftfc wF wT X, clUn wF X k]
      (targetLiftfc (succ c) (nthc X (numeralM 1))) :=
    IHl_at hpsi _ hlt1 wF wT (succ c) (PrfH_and_intro (PrfH_and_intro hwT hwF) hin1)
  exact PrfH.mp _ _ _ (prf_to_prfH (hun c X) _) (PrfH_and_intro hshape hIH1)

end RamasL

/-- **LAS OCHO RAMAS, ENSAMBLADAS** por or-elim al nivel `Prf`. -/
theorem clausesL_imp (hbot : CasoBotL) (hatom : CasoAtomL) (heq : CasoEqL)
    (h5 : CasoBinL 5) (h7 : CasoBinL 7) (h8 : CasoBinL 8)
    (h6 : CasoUnL 6) (h9 : CasoUnL 9) (wF wT c X : Term) :
    Prf (Formula.impl (isFormCodeE2 wF wT X)
      (Formula.impl (CTXFliftfc wF wT X) (targetLiftfc c X))) := by
  simp only [isFormCodeE2, lorAll]
  exact prf_or_elim_imp (ramaL_bot wF wT c X hbot)
   (prf_or_elim_imp (ramaL_atom wF wT c X hatom)
    (prf_or_elim_imp (ramaL_eq wF wT c X heq)
     (prf_or_elim_imp (ramaL_bin wF wT c X 5 h5)
      (prf_or_elim_imp (ramaL_un wF wT c X 6 h6)
       (prf_or_elim_imp (ramaL_bin wF wT c X 7 h7)
        (prf_or_elim_imp (ramaL_bin wF wT c X 8 h8)
                         (ramaL_un wF wT c X 9 h9)))))))

/-- ⛔ ADR‑019: `psi_lift_form3` es GENÉRICO en `Φ` y vive en `Meta/StrongInductionPrf.lean`.
    Aquí sólo se pliega el resultado en la abreviatura local `PSIatL`. -/
theorem psi_l3L : liftFormula 0 (liftFormula 0 (liftFormula 0 (PSI PHIliftfc)))
    = PSIatL (.var 3) := by
  rw [psi_lift_form3 PHIliftfc hPHIliftfc]
  simp only [PSIatL, lt, liftFormula, liftTerm, liftTerms, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, hPHIliftfc]

/-- **EL PASO DE LA INDUCCIÓN FUERTE.** -/
theorem PHIliftfc_step (hbot : CasoBotL) (hatom : CasoAtomL) (heq : CasoEqL)
    (h5 : CasoBinL 5) (h7 : CasoBinL 7) (h8 : CasoBinL 8)
    (h6 : CasoUnL 6) (h9 : CasoUnL 9) :
    Prf (Formula.forall (Formula.impl (PSI PHIliftfc) PHIliftfc)) := by
  refine Prf.gen _ (prf_deduction ?_)
  refine PrfH.gen [PSI PHIliftfc] (Formula.forall (Formula.forall PHIliftfcBody)) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ (Formula.forall PHIliftfcBody) ?_
  simp only [List.map_cons, List.map_nil]
  refine PrfH.gen _ PHIliftfcBody ?_
  simp only [List.map_cons, List.map_nil, psi_l3L]
  show PrfH [PSIatL (.var 3)] PHIliftfcBody
  refine deduction_aux ?_ (isFC1 (.var 2) (.var 1) (.var 3)) [PSIatL (.var 3)] rfl
  have hg : PrfH [isFC1 (.var 2) (.var 1) (.var 3), PSIatL (.var 3)]
      (isFC1 (.var 2) (.var 1) (.var 3)) := PrfH.hyp _ _ (List.Mem.head _)
  have hpsi : PrfH [isFC1 (.var 2) (.var 1) (.var 3), PSIatL (.var 3)]
      (PSIatL (.var 3)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hwT := PrfH_and_elim_left (PrfH_and_elim_left hg)
  have hwF := PrfH_and_elim_right (PrfH_and_elim_left hg)
  have hin := PrfH_and_elim_right hg
  have hcode : PrfH [isFC1 (.var 2) (.var 1) (.var 3), PSIatL (.var 3)]
      (isFormCodeE2 (.var 2) (.var 1) (.var 3)) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _
      (prf_to_prfH (prf_isFormCodeE2_of_In (.var 2) (.var 1) (.var 3)) _) hin) hwF
  have hctx : PrfH [isFC1 (.var 2) (.var 1) (.var 3), PSIatL (.var 3)]
      (CTXFliftfc (.var 2) (.var 1) (.var 3)) :=
    PrfH_and_intro (PrfH_and_intro hpsi hwT) hwF
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (clausesL_imp hbot hatom heq h5 h7 h8 h6 h9
      (.var 2) (.var 1) (.var 0) (.var 3)) _) hcode) hctx

/-! ## §7 · EL TEOREMA, MÓDULO LOS OCHO CASOS -/

theorem PHIliftfc_all (hbot : CasoBotL) (hatom : CasoAtomL) (heq : CasoEqL)
    (h5 : CasoBinL 5) (h7 : CasoBinL 7) (h8 : CasoBinL 8)
    (h6 : CasoUnL 6) (h9 : CasoUnL 9) (t : Term) : Prf (substFormula 0 t PHIliftfc) :=
  prf_strong_induction PHIliftfc hPHIliftfc (PHIliftfc_step hbot hatom heq h5 h7 h8 h6 h9) t

theorem DESCENSO_liftfc_imp (hbot : CasoBotL) (hatom : CasoAtomL) (heq : CasoEqL)
    (h5 : CasoBinL 5) (h7 : CasoBinL 7) (h8 : CasoBinL 8)
    (h6 : CasoUnL 6) (h9 : CasoUnL 9) (wF wT c t : Term) :
    Prf (Formula.impl (isFC1 wF wT t) (targetLiftfc c t)) :=
  prfH_nil_to_prf
    (PHIliftfc_use t wF wT c
      (prf_to_prfH (PHIliftfc_all hbot hatom heq h5 h7 h8 h6 h9 t) [])) rfl

/-- ⭐⭐ **EL CHASIS: `pcc_eval_liftfc` MÓDULO LOS OCHO CASOS.** Con esto,
    `DEUDA_evalLiftfc_isFC1` —y por `deuda_of_isFC1` también `DEUDA_evalLiftfc`— quedan a
    distancia de descargar los ocho `Caso*L`. -/
theorem pcc_eval_liftfc_modulo_8
    (hbot : CasoBotL) (hatom : CasoAtomL) (heq : CasoEqL)
    (h5 : CasoBinL 5) (h7 : CasoBinL 7) (h8 : CasoBinL 8)
    (h6 : CasoUnL 6) (h9 : CasoUnL 9) : DEUDA_evalLiftfc_isFC1 :=
  fun wF wT c X => DESCENSO_liftfc_imp hbot hatom heq h5 h7 h8 h6 h9 wF wT c X



/-! ## §8 · DESCARGA de `CasoBotL`, `CasoBinL 5/7/8` y `CasoUnL 6/9`

Los seis que **no** piden A5. Cada uno es la misma jugada: la ecuación dotada de §3, la
ecuación META correspondiente (`prf_liftfc_*`, `Meta/ArithPrf.lean`), y el transporte de
Leibniz desde la forma ecuacional de la guarda. -/

/-- La congruencia interna de `liftfcT` en su argumento CÓDIGO — espejo de
    `pcc_congr_liftcT_arg2_code`. Es lo único de fontanería que faltaba. -/
theorem pcc_congr_liftfcT_arg2_code (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwA : Prf (hasWit A) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (liftfcT A X) (liftfcT A Y))) := by
  let Ac : Term := eqc (liftfcT A X) (liftfcT A (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (liftfcT A X) (liftfcT A w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (liftfcT A X) (liftfcT A (varc (numeral 0)))) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_liftfcT zero w A X) (prf_congr_liftfcT (hA w) (hX w))
    · exact prf_eq_trans (prf_substtc_liftfcT zero w A (varc (numeral 0)))
        (prf_congr_liftfcT (hA w) (prf_substtc_varc0 w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (liftfcT A X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (liftfcT A X) (liftfcT A (varc (numeral 0)))
        (prf_hasWit_liftfcT hwA hwX) (prf_hasWit_liftfcT hwA (prf_hasWit_varc (numeral 0)))) hwX hwY)

/-- El transporte de Leibniz del objetivo (espeja `PrfH_congr_targetSubstfc`). -/
theorem substF_targetLiftfc_hole (c t : Term) :
    substFormula 0 t (targetLiftfc (liftTerm 0 c) (.var 0)) = targetLiftfc c t := by
  simp only [substF_targetLiftfc, FOL.substTerm_liftTerm, substTerm, if_true]

theorem PrfH_congr_targetLiftfc {Γ : List Formula} (c : Term) {X X' : Term}
    (h : PrfH Γ (X =eq X')) (ha : PrfH Γ (targetLiftfc c X)) : PrfH Γ (targetLiftfc c X') :=
  (substF_targetLiftfc_hole c X') ▸
    PrfH_leibniz_subst (A := targetLiftfc (liftTerm 0 c) (.var 0)) h
      ((substF_targetLiftfc_hole c X) ▸ ha)

/-! ### §8.1 · `CasoBotL` (tag 2) -/

/-- **`CasoBotL` DESCARGADO.** -/
theorem casoBotL : CasoBotL := by
  intro c X
  refine prf_deduction ?_
  have hbase : Prf (targetLiftfc c botc) := by
    unfold targetLiftfc evalLiftfcCode
    refine prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_liftfc_bottom c))))) ?_
    exact pcc_eq_trans_code _ _ _
      (substtc_inv_liftfcT (substtc_inv_tcFn c) (substtc_inv_tcFn botc))
      (by hw_auto) (by hw_auto) (by hw_auto)
      (prf_mp (pcc_congr_liftfcT_arg2_code (tcFn c) (tcFn botc) (nulT 2)
        (substtc_inv_tcFn c) (substtc_inv_tcFn botc)) (pcc_dot_nul_symm 2))
      (pcc_eq_trans_code _ _ _ (substtc_inv_liftfcT (substtc_inv_tcFn c) (substtc_inv_nulT 2))
        (by hw_auto) (by hw_auto) (by hw_auto)
        (pcc_liftfc_bottom_code c) (pcc_dot_nul 2))
  exact PrfH_congr_targetLiftfc c (PrfH_eq_symm (prfH_hyp_self (clBot X)))
    (prf_to_prfH hbase _)

/-! ### §8.2 · `CasoBinL 5/7/8` — genérico en el tag, tres instancias -/

/-- El núcleo del caso BINARIO en forma IMPLICACION: las dos HI llegan como hipótesis OBJETO.
    ⚠️ Igual que en `substfc`, hay que escribirlo en `PrfH` (deuda B6b). -/
theorem paso_caso_bin_imp_L (k : Nat) (c a b : Term)
    (hax : Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (binT k (tcFn a) (tcFn b)))
      (binT k (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b))))))
    (hobj : Prf (liftfc c (cons (numeralM k) (cons a (cons b nil)))
      =eq cons (numeralM k) (cons (liftfc c a) (cons (liftfc c b) nil)))) :
    Prf (Formula.impl (land (targetLiftfc c a) (targetLiftfc c b))
      (targetLiftfc c (cons (numeralM k) (cons a (cons b nil))))) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (targetLiftfc c a) (targetLiftfc c b))
  have hA : PrfH [land (targetLiftfc c a) (targetLiftfc c b)]
      (provFromCode (eqc (liftfcT (tcFn c) (tcFn a)) (tcFn (liftfc c a)))) :=
    PrfH_and_elim_left hh
  have hB : PrfH [land (targetLiftfc c a) (targetLiftfc c b)]
      (provFromCode (eqc (liftfcT (tcFn c) (tcFn b)) (tcFn (liftfc c b)))) :=
    PrfH_and_elim_right hh
  have iLA : ∀ W, Prf (substtc zero W (liftfcT (tcFn c) (tcFn a))
      =eq liftfcT (tcFn c) (tcFn a)) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c) (substtc_inv_tcFn a)
  have iLB : ∀ W, Prf (substtc zero W (liftfcT (tcFn c) (tcFn b))
      =eq liftfcT (tcFn c) (tcFn b)) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c) (substtc_inv_tcFn b)
  have iX0 : ∀ W, Prf (substtc zero W
      (liftfcT (tcFn c) (tcFn (cons (numeralM k) (cons a (cons b nil)))))
      =eq liftfcT (tcFn c) (tcFn (cons (numeralM k) (cons a (cons b nil))))) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c)
      (substtc_inv_tcFn (cons (numeralM k) (cons a (cons b nil))))
  have iX1 : ∀ W, Prf (substtc zero W (liftfcT (tcFn c) (binT k (tcFn a) (tcFn b)))
      =eq liftfcT (tcFn c) (binT k (tcFn a) (tcFn b))) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W
      (binT k (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b)))
      =eq binT k (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b))) :=
    substtc_inv_binT iLA iLB
  have iX3 : ∀ W, Prf (substtc zero W (binT k (tcFn (liftfc c a)) (liftfcT (tcFn c) (tcFn b)))
      =eq binT k (tcFn (liftfc c a)) (liftfcT (tcFn c) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn (liftfc c a)) iLB
  have iX4 : ∀ W, Prf (substtc zero W (binT k (tcFn (liftfc c a)) (tcFn (liftfc c b)))
      =eq binT k (tcFn (liftfc c a)) (tcFn (liftfc c b))) :=
    substtc_inv_binT (substtc_inv_tcFn (liftfc c a)) (substtc_inv_tcFn (liftfc c b))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_liftfcT_arg2_code (tcFn c)
      (tcFn (cons (numeralM k) (cons a (cons b nil)))) (binT k (tcFn a) (tcFn b))
      (substtc_inv_tcFn c) (substtc_inv_tcFn (cons (numeralM k) (cons a (cons b nil)))))
    (pcc_dot_bin_symm k a b)) [land (targetLiftfc c a) (targetLiftfc c b)]
  have h2 := prf_to_prfH hax [land (targetLiftfc c a) (targetLiftfc c b)]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_1_code k
      (liftfcT (tcFn c) (tcFn b)) (liftfcT (tcFn c) (tcFn a)) (tcFn (liftfc c a)) iLB iLA) _) hA
  have h4 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code k (tcFn (liftfc c a))
      (liftfcT (tcFn c) (tcFn b)) (tcFn (liftfc c b))
      (substtc_inv_tcFn (liftfc c a)) iLB) _) hB
  have h5 := prf_to_prfH (pcc_dot_bin k (liftfc c a) (liftfc c b))
    [land (targetLiftfc c a) (targetLiftfc c b)]
  have h6 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm hobj))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM k) (cons (liftfc c a) (cons (liftfc c b) nil))))))
    [land (targetLiftfc c a) (targetLiftfc c b)]
  refine PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4
          (PrfH_eq_trans_code _ _ _ iX4 h5 h6 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_
    <;> hw_auto

theorem casoBinL_gen (k : Nat)
    (hax : ∀ c a b : Term, Prf (provFromCode (eqCodeFn
      (liftfcT (tcFn c) (binT k (tcFn a) (tcFn b)))
      (binT k (liftfcT (tcFn c) (tcFn a)) (liftfcT (tcFn c) (tcFn b))))))
    (hobj : ∀ c a b : Term, Prf (liftfc c (cons (numeralM k) (cons a (cons b nil)))
      =eq cons (numeralM k) (cons (liftfc c a) (cons (liftfc c b) nil)))) :
    CasoBinL k := by
  intro c X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (shapeBin X k)
    (land (targetLiftfc c (nthc X (numeralM 1))) (targetLiftfc c (nthc X (numeralM 2)))))
  have hshape := PrfH_and_elim_left hh
  have hab := PrfH_and_elim_right hh
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (paso_caso_bin_imp_L k c (nthc X (numeralM 1)) (nthc X (numeralM 2))
      (hax c (nthc X (numeralM 1)) (nthc X (numeralM 2)))
      (hobj c (nthc X (numeralM 1)) (nthc X (numeralM 2)))) _) hab
  exact PrfH_congr_targetLiftfc c (PrfH_eq_symm hshape) hC

theorem casoBinL5 : CasoBinL 5 :=
  casoBinL_gen 5 (fun c a b => pcc_liftfc_impl_code c a b) (fun c a b => prf_liftfc_impl c a b)
theorem casoBinL7 : CasoBinL 7 :=
  casoBinL_gen 7 (fun c a b => pcc_liftfc_and_code c a b) (fun c a b => prf_liftfc_and c a b)
theorem casoBinL8 : CasoBinL 8 :=
  casoBinL_gen 8 (fun c a b => pcc_liftfc_or_code c a b) (fun c a b => prf_liftfc_or c a b)

/-! ### §8.3 · `CasoUnL 6/9` — ⚠️ LAS QUE SUBEN EL NIVEL

La HI llega a nivel `σc` y la conclusión es a nivel `c`. Dentro de `Prov` eso se ve como
`liftfcT (succcT ċ) ȧ` en el lado derecho de la ecuación dotada — de ahí que el eslabón que
consume la HI sea el de nivel `succ c`, no el de `c`. -/

theorem paso_caso_un_imp_L (k : Nat) (c a : Term)
    (hax : Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (unT k (tcFn a)))
      (unT k (liftfcT (succcT (tcFn c)) (tcFn a))))))
    (hobj : Prf (liftfc c (cons (numeralM k) (cons a nil))
      =eq cons (numeralM k) (cons (liftfc (succ c) a) nil))) :
    Prf (Formula.impl (targetLiftfc (succ c) a)
      (targetLiftfc c (cons (numeralM k) (cons a nil)))) := by
  refine prf_deduction ?_
  have hA : PrfH [targetLiftfc (succ c) a]
      (provFromCode (eqc (liftfcT (tcFn (succ c)) (tcFn a)) (tcFn (liftfc (succ c) a)))) :=
    prfH_hyp_self _
  -- el nivel dotado `⌜σc⌝` se normaliza a `succcT ċ`
  have hsc : Prf (tcFn (succ c) =eq succcT (tcFn c)) := prf_tc_succ' c
  have hA' : PrfH [targetLiftfc (succ c) a]
      (provFromCode (eqc (liftfcT (succcT (tcFn c)) (tcFn a)) (tcFn (liftfc (succ c) a)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn
      (prf_congr_liftfcT hsc (prf_refl _)) (prf_refl _))) _) hA
  have iLA : ∀ W, Prf (substtc zero W (liftfcT (succcT (tcFn c)) (tcFn a))
      =eq liftfcT (succcT (tcFn c)) (tcFn a)) :=
    substtc_inv_liftfcT (substtc_inv_succcT (substtc_inv_tcFn c)) (substtc_inv_tcFn a)
  have iX0 : ∀ W, Prf (substtc zero W (liftfcT (tcFn c) (tcFn (cons (numeralM k) (cons a nil))))
      =eq liftfcT (tcFn c) (tcFn (cons (numeralM k) (cons a nil)))) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c)
      (substtc_inv_tcFn (cons (numeralM k) (cons a nil)))
  have iX1 : ∀ W, Prf (substtc zero W (liftfcT (tcFn c) (unT k (tcFn a)))
      =eq liftfcT (tcFn c) (unT k (tcFn a))) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c) (substtc_inv_unT (substtc_inv_tcFn a))
  have iX2 : ∀ W, Prf (substtc zero W (unT k (liftfcT (succcT (tcFn c)) (tcFn a)))
      =eq unT k (liftfcT (succcT (tcFn c)) (tcFn a))) := substtc_inv_unT iLA
  have iX3 : ∀ W, Prf (substtc zero W (unT k (tcFn (liftfc (succ c) a)))
      =eq unT k (tcFn (liftfc (succ c) a))) :=
    substtc_inv_unT (substtc_inv_tcFn (liftfc (succ c) a))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_liftfcT_arg2_code (tcFn c)
      (tcFn (cons (numeralM k) (cons a nil))) (unT k (tcFn a))
      (substtc_inv_tcFn c) (substtc_inv_tcFn (cons (numeralM k) (cons a nil))))
    (pcc_dot_un_symm k a)) [targetLiftfc (succ c) a]
  have h2 := prf_to_prfH hax [targetLiftfc (succ c) a]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_unT_code k
      (liftfcT (succcT (tcFn c)) (tcFn a)) (tcFn (liftfc (succ c) a)) iLA) _) hA'
  have h4 := prf_to_prfH (pcc_dot_un k (liftfc (succ c) a)) [targetLiftfc (succ c) a]
  have h5 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm hobj))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM k) (cons (liftfc (succ c) a) nil)))))
    [targetLiftfc (succ c) a]
  refine PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4 h5 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_
    <;> hw_auto

theorem casoUnL_gen (k : Nat)
    (hax : ∀ c a : Term, Prf (provFromCode (eqCodeFn (liftfcT (tcFn c) (unT k (tcFn a)))
      (unT k (liftfcT (succcT (tcFn c)) (tcFn a))))))
    (hobj : ∀ c a : Term, Prf (liftfc c (cons (numeralM k) (cons a nil))
      =eq cons (numeralM k) (cons (liftfc (succ c) a) nil))) :
    CasoUnL k := by
  intro c X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (shapeUn X k) (targetLiftfc (succ c) (nthc X (numeralM 1))))
  have hshape := PrfH_and_elim_left hh
  have ha := PrfH_and_elim_right hh
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (paso_caso_un_imp_L k c (nthc X (numeralM 1))
      (hax c (nthc X (numeralM 1))) (hobj c (nthc X (numeralM 1)))) _) ha
  exact PrfH_congr_targetLiftfc c (PrfH_eq_symm hshape) hC

theorem casoUnL6 : CasoUnL 6 :=
  casoUnL_gen 6 (fun c a => pcc_liftfc_forall_code c a) (fun c a => prf_liftfc_forall c a)
theorem casoUnL9 : CasoUnL 9 :=
  casoUnL_gen 9 (fun c a => pcc_liftfc_ex_code c a) (fun c a => prf_liftfc_ex c a)

/-- ⭐⭐ **SEIS DE LOS OCHO, DESCARGADOS.** Lo que queda de `pcc_eval_liftfc` son
    `CasoAtomL` y `CasoEqL`, que consumen `pcc_eval_liftsc_at` / `pcc_eval_liftc_at` (A5). -/
theorem pcc_eval_liftfc_modulo_2 (hatom : CasoAtomL) (heq : CasoEqL) :
    DEUDA_evalLiftfc_isFC1 :=
  pcc_eval_liftfc_modulo_8 casoBotL hatom heq casoBinL5 casoBinL7 casoBinL8 casoUnL6 casoUnL9

/-- Y su forma con el testigo cuantificado, vía el `∃∃` de C3‑F. -/
theorem deuda_modulo_2 (hatom : CasoAtomL) (heq : CasoEqL) : DEUDA_evalLiftfc :=
  deuda_of_isFC1 (pcc_eval_liftfc_modulo_2 hatom heq)



/-! ## §9 · `CasoAtomL` y `CasoEqL` — los DOS que consumen A5

⭐ Aquí es donde A5 cobra. Los dos casos bajan al sorte TÉRMINO **al nivel corriente `c`**, no a
nivel `zero`, y por eso `pcc_eval_liftc` no valía: lo que consumen es `DESCENSO_at_imp` y
`DESCENSO_at_lista_imp` (`Meta/EvalLiftcPrf.lean` §7bis, A5), que llevan el nivel abierto.

Las dos ecuaciones dotadas que faltaban tienen **otra forma** que las de §3: su lado derecho no
es `liftfc` otra vez, sino `liftsc` (atom) y `liftc` (eq) — el cambio de sorte. -/

def LIFTFC_ATOM_BODY : Formula :=
  liftfc (.var 2) (atomc (.var 1) (.var 0)) =eq atomc (.var 1) (liftsc (.var 2) (.var 0))
theorem LIFTFC_ATOM_BODY_ok : ax_liftfc_atom = forall_3 LIFTFC_ATOM_BODY := rfl

def LIFTFC_EQ_BODY : Formula :=
  liftfc (.var 2) (eqc (.var 1) (.var 0)) =eq eqc (liftc (.var 2) (.var 1)) (liftc (.var 2) (.var 0))
theorem LIFTFC_EQ_BODY_ok : ax_liftfc_eq = forall_3 LIFTFC_EQ_BODY := rfl

/-- **`ax_liftfc_atom` DOTADA** — la casilla 1 (el símbolo) va INTACTA; sólo baja la lista. -/
theorem pcc_liftfc_atom_code (c p ts : Term) :
    Prf (provFromCode (eqCodeFn
      (liftfcT (tcFn c) (binT 3 (tcFn p) (tcFn ts)))
      (binT 3 (tcFn p) (liftscT (tcFn c) (tcFn ts))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn p)
  let W0 : Term := tcFn ts
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode LIFTFC_ATOM_BODY)
      =eq eqCodeFn (liftfcT W2 (binT 3 (varc (numeral 1)) (varc (numeral 0))))
                   (binT 3 (varc (numeral 1)) (liftscT W2 (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 LIFTFC_ATOM_BODY
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftfcT W2 (binT 3 (varc (numeral 1)) (varc (numeral 0))))
                   (binT 3 (varc (numeral 1)) (liftscT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT 3 (varc (numeral 1)) (varc (numeral 0))))
                   (binT 3 (varc (numeral 1)) (liftscT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftfcT hA2 (prf_refl _))
      (prf_congr_binT (prf_refl _) (prf_congr_liftscT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn p) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn p)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftfcT (tcFn c) (binT 3 (varc (numeral 1)) (varc (numeral 0))))
        (binT 3 (varc (numeral 1)) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT 3 (tcFn p) (varc (numeral 0))))
                   (binT 3 (tcFn p) (liftscT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftfcT (succ zero) W1 _ _) ?_
      refine prf_congr_liftfcT hc1 ?_
      exact prf_eq_trans (prf_substtc_binT_at 3 1 W1 _ _) (prf_congr_binT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_binT_at 3 1 W1 _ _) ?_
      refine prf_congr_binT hv1 ?_
      exact prf_eq_trans (prf_substtc_liftscT (succ zero) W1 _ _) (prf_congr_liftscT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftfcT (tcFn c) (binT 3 (tcFn p) (varc (numeral 0))))
        (binT 3 (tcFn p) (liftscT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT 3 (tcFn p) (tcFn ts)))
                   (binT 3 (tcFn p) (liftscT (tcFn c) (tcFn ts)))) := by
    have hb : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn ts) := prf_substtc_varc0 W0
    have hcz : Prf (substtc zero W0 (tcFn c) =eq tcFn c) := prf_substtc_tcFn W0 c
    have hpz : Prf (substtc zero W0 (tcFn p) =eq tcFn p) := prf_substtc_tcFn W0 p
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftfcT zero W0 _ _) ?_
      refine prf_congr_liftfcT hcz ?_
      exact prf_eq_trans (prf_substtc_binT_at 3 0 W0 _ _) (prf_congr_binT hpz hb)
    · refine prf_eq_trans (prf_substtc_binT_at 3 0 W0 _ _) ?_
      refine prf_congr_binT hpz ?_
      exact prf_eq_trans (prf_substtc_liftscT zero W0 _ _) (prf_congr_liftscT hcz hb)
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode LIFTFC_ATOM_BODY)))
      =eq eqCodeFn (liftfcT (tcFn c) (binT 3 (tcFn p) (tcFn ts)))
                   (binT 3 (tcFn p) (liftscT (tcFn c) (tcFn ts)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 LIFTFC_ATOM_BODY (show ax_liftfc_atom ∈ axioms by simp [axioms])
      (tcFn c) (tcFn p) (tcFn ts)
      (prf_hasWit_tcFn (liftTerm 0 c)) (prf_hasWit_tcFn (liftTerm 0 p))
      (prf_hasWit_tcFn (liftTerm 0 ts)))

/-- **`ax_liftfc_eq` DOTADA** — las DOS casillas bajan al sorte TÉRMINO (`liftc`). -/
theorem pcc_liftfc_eq_code (c a b : Term) :
    Prf (provFromCode (eqCodeFn
      (liftfcT (tcFn c) (binT 4 (tcFn a) (tcFn b)))
      (binT 4 (liftcT (tcFn c) (tcFn a)) (liftcT (tcFn c) (tcFn b))))) := by
  let W2 : Term := liftc zero (liftc zero (tcFn c))
  let W1 : Term := liftc zero (tcFn a)
  let W0 : Term := tcFn b
  have hin : Prf (substfc (succ (succ zero)) W2 (formCode LIFTFC_EQ_BODY)
      =eq eqCodeFn (liftfcT W2 (binT 4 (varc (numeral 1)) (varc (numeral 0))))
                   (binT 4 (liftcT W2 (varc (numeral 1))) (liftcT W2 (varc (numeral 0))))) :=
    prf_substfc_arith_open 2 W2 LIFTFC_EQ_BODY
  have hA2 : Prf (W2 =eq tcFn c) :=
    prf_eq_trans (prf_congr_liftc (prf_liftc_tcFn c)) (prf_liftc_tcFn c)
  have hnorm : Prf (eqCodeFn (liftfcT W2 (binT 4 (varc (numeral 1)) (varc (numeral 0))))
                   (binT 4 (liftcT W2 (varc (numeral 1))) (liftcT W2 (varc (numeral 0))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT 4 (varc (numeral 1)) (varc (numeral 0))))
                   (binT 4 (liftcT (tcFn c) (varc (numeral 1)))
                           (liftcT (tcFn c) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn (prf_congr_liftfcT hA2 (prf_refl _))
      (prf_congr_binT (prf_congr_liftcT hA2 (prf_refl _))
                      (prf_congr_liftcT hA2 (prf_refl _)))
  have hv1 : Prf (substtc (succ zero) W1 (varc (numeral 1)) =eq tcFn a) :=
    prf_eq_trans (prf_mp (prf_substtc_var_eq (succ zero) W1 (numeral 1)) (prf_refl _))
      (prf_liftc_tcFn a)
  have hv0 : Prf (substtc (succ zero) W1 (varc (numeral 0)) =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt (succ zero) W1 (numeral 0)) (prf_zero_lt_succ zero)
  have hc1 : Prf (substtc (succ zero) W1 (tcFn c) =eq tcFn c) := prf_substtc_tcFn_at 1 W1 c
  have hmid : Prf (substfc (succ zero) W1 (eqCodeFn
        (liftfcT (tcFn c) (binT 4 (varc (numeral 1)) (varc (numeral 0))))
        (binT 4 (liftcT (tcFn c) (varc (numeral 1))) (liftcT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT 4 (tcFn a) (varc (numeral 0))))
                   (binT 4 (liftcT (tcFn c) (tcFn a))
                           (liftcT (tcFn c) (varc (numeral 0))))) := by
    refine prf_eq_trans (prf_substfc_eq (succ zero) W1 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftfcT (succ zero) W1 _ _) ?_
      refine prf_congr_liftfcT hc1 ?_
      exact prf_eq_trans (prf_substtc_binT_at 4 1 W1 _ _) (prf_congr_binT hv1 hv0)
    · refine prf_eq_trans (prf_substtc_binT_at 4 1 W1 _ _) ?_
      refine prf_congr_binT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _) (prf_congr_liftcT hc1 hv1)
      · exact prf_eq_trans (prf_substtc_liftcT (succ zero) W1 _ _) (prf_congr_liftcT hc1 hv0)
  have hout : Prf (substfc zero W0 (eqCodeFn
        (liftfcT (tcFn c) (binT 4 (tcFn a) (varc (numeral 0))))
        (binT 4 (liftcT (tcFn c) (tcFn a)) (liftcT (tcFn c) (varc (numeral 0)))))
      =eq eqCodeFn (liftfcT (tcFn c) (binT 4 (tcFn a) (tcFn b)))
                   (binT 4 (liftcT (tcFn c) (tcFn a)) (liftcT (tcFn c) (tcFn b)))) := by
    have hb : Prf (substtc zero W0 (varc (numeral 0)) =eq tcFn b) := prf_substtc_varc0 W0
    have hcz : Prf (substtc zero W0 (tcFn c) =eq tcFn c) := prf_substtc_tcFn W0 c
    have haz : Prf (substtc zero W0 (tcFn a) =eq tcFn a) := prf_substtc_tcFn W0 a
    refine prf_eq_trans (prf_substfc_eq zero W0 _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans (prf_substtc_liftfcT zero W0 _ _) ?_
      refine prf_congr_liftfcT hcz ?_
      exact prf_eq_trans (prf_substtc_binT_at 4 0 W0 _ _) (prf_congr_binT haz hb)
    · refine prf_eq_trans (prf_substtc_binT_at 4 0 W0 _ _) ?_
      refine prf_congr_binT ?_ ?_
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _) (prf_congr_liftcT hcz haz)
      · exact prf_eq_trans (prf_substtc_liftcT zero W0 _ _) (prf_congr_liftcT hcz hb)
  have hchain : Prf (substfc zero W0 (substfc (succ zero) W1
        (substfc (succ (succ zero)) W2 (formCode LIFTFC_EQ_BODY)))
      =eq eqCodeFn (liftfcT (tcFn c) (binT 4 (tcFn a) (tcFn b)))
                   (binT 4 (liftcT (tcFn c) (tcFn a)) (liftcT (tcFn c) (tcFn b)))) :=
    prf_eq_trans (prf_congr_substfc_arg3
      (prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hmid)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst3 LIFTFC_EQ_BODY (show ax_liftfc_eq ∈ axioms by simp [axioms])
      (tcFn c) (tcFn a) (tcFn b)
      (prf_hasWit_tcFn (liftTerm 0 c)) (prf_hasWit_tcFn (liftTerm 0 a))
      (prf_hasWit_tcFn (liftTerm 0 b)))

/-! ### §9.1 · Los dos NÚCLEOS, con la evaluación de término como hipótesis OBJETO -/

/-- El núcleo de `atomc`: pide **sólo** la evaluación de la LISTA de argumentos, al nivel `c`. -/
theorem caso_atom_core_L (c p ts : Term) :
    Prf (Formula.impl (targetLiftscAt c ts)
      (targetLiftfc c (cons (numeralM 3) (cons p (cons ts nil))))) := by
  refine prf_deduction ?_
  have hB : PrfH [targetLiftscAt c ts]
      (provFromCode (eqc (liftscT (tcFn c) (tcFn ts)) (tcFn (liftsc c ts)))) := prfH_hyp_self _
  have iLS : ∀ W, Prf (substtc zero W (liftscT (tcFn c) (tcFn ts))
      =eq liftscT (tcFn c) (tcFn ts)) :=
    substtc_inv_liftscT (substtc_inv_tcFn c) (substtc_inv_tcFn ts)
  have iX0 : ∀ W, Prf (substtc zero W
      (liftfcT (tcFn c) (tcFn (cons (numeralM 3) (cons p (cons ts nil)))))
      =eq liftfcT (tcFn c) (tcFn (cons (numeralM 3) (cons p (cons ts nil))))) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c)
      (substtc_inv_tcFn (cons (numeralM 3) (cons p (cons ts nil))))
  have iX1 : ∀ W, Prf (substtc zero W (liftfcT (tcFn c) (binT 3 (tcFn p) (tcFn ts)))
      =eq liftfcT (tcFn c) (binT 3 (tcFn p) (tcFn ts))) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c)
      (substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn ts))
  have iX2 : ∀ W, Prf (substtc zero W (binT 3 (tcFn p) (liftscT (tcFn c) (tcFn ts)))
      =eq binT 3 (tcFn p) (liftscT (tcFn c) (tcFn ts))) :=
    substtc_inv_binT (substtc_inv_tcFn p) iLS
  have iX3 : ∀ W, Prf (substtc zero W (binT 3 (tcFn p) (tcFn (liftsc c ts)))
      =eq binT 3 (tcFn p) (tcFn (liftsc c ts))) :=
    substtc_inv_binT (substtc_inv_tcFn p) (substtc_inv_tcFn (liftsc c ts))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_liftfcT_arg2_code (tcFn c)
      (tcFn (cons (numeralM 3) (cons p (cons ts nil)))) (binT 3 (tcFn p) (tcFn ts))
      (substtc_inv_tcFn c) (substtc_inv_tcFn (cons (numeralM 3) (cons p (cons ts nil)))))
    (pcc_dot_bin_symm 3 p ts)) [targetLiftscAt c ts]
  have h2 := prf_to_prfH (pcc_liftfc_atom_code c p ts) [targetLiftscAt c ts]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 3 (tcFn p)
      (liftscT (tcFn c) (tcFn ts)) (tcFn (liftsc c ts)) (substtc_inv_tcFn p) iLS) _) hB
  have h4 := prf_to_prfH (pcc_dot_bin 3 p (liftsc c ts)) [targetLiftscAt c ts]
  have h5 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_liftfc_atom c p ts)))))
    (prf_provFromCode_eqCodeFn_refl (tcFn (cons (numeralM 3) (cons p (cons (liftsc c ts) nil))))))
    [targetLiftscAt c ts]
  refine PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4 h5 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_
    <;> hw_auto

/-- El núcleo de `eqc`: pide la evaluación de TÉRMINO en las DOS casillas, al nivel `c`. -/
theorem caso_eq_core_L (c a b : Term) :
    Prf (Formula.impl (land (targetLiftAt c a) (targetLiftAt c b))
      (targetLiftfc c (cons (numeralM 4) (cons a (cons b nil))))) := by
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (targetLiftAt c a) (targetLiftAt c b))
  have hA : PrfH [land (targetLiftAt c a) (targetLiftAt c b)]
      (provFromCode (eqc (liftcT (tcFn c) (tcFn a)) (tcFn (liftc c a)))) :=
    PrfH_and_elim_left hh
  have hB : PrfH [land (targetLiftAt c a) (targetLiftAt c b)]
      (provFromCode (eqc (liftcT (tcFn c) (tcFn b)) (tcFn (liftc c b)))) :=
    PrfH_and_elim_right hh
  have iLA : ∀ W, Prf (substtc zero W (liftcT (tcFn c) (tcFn a)) =eq liftcT (tcFn c) (tcFn a)) :=
    substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn a)
  have iLB : ∀ W, Prf (substtc zero W (liftcT (tcFn c) (tcFn b)) =eq liftcT (tcFn c) (tcFn b)) :=
    substtc_inv_liftcT (substtc_inv_tcFn c) (substtc_inv_tcFn b)
  have iX0 : ∀ W, Prf (substtc zero W
      (liftfcT (tcFn c) (tcFn (cons (numeralM 4) (cons a (cons b nil)))))
      =eq liftfcT (tcFn c) (tcFn (cons (numeralM 4) (cons a (cons b nil))))) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c)
      (substtc_inv_tcFn (cons (numeralM 4) (cons a (cons b nil))))
  have iX1 : ∀ W, Prf (substtc zero W (liftfcT (tcFn c) (binT 4 (tcFn a) (tcFn b)))
      =eq liftfcT (tcFn c) (binT 4 (tcFn a) (tcFn b))) :=
    substtc_inv_liftfcT (substtc_inv_tcFn c)
      (substtc_inv_binT (substtc_inv_tcFn a) (substtc_inv_tcFn b))
  have iX2 : ∀ W, Prf (substtc zero W
      (binT 4 (liftcT (tcFn c) (tcFn a)) (liftcT (tcFn c) (tcFn b)))
      =eq binT 4 (liftcT (tcFn c) (tcFn a)) (liftcT (tcFn c) (tcFn b))) :=
    substtc_inv_binT iLA iLB
  have iX3 : ∀ W, Prf (substtc zero W (binT 4 (tcFn (liftc c a)) (liftcT (tcFn c) (tcFn b)))
      =eq binT 4 (tcFn (liftc c a)) (liftcT (tcFn c) (tcFn b))) :=
    substtc_inv_binT (substtc_inv_tcFn (liftc c a)) iLB
  have iX4 : ∀ W, Prf (substtc zero W (binT 4 (tcFn (liftc c a)) (tcFn (liftc c b)))
      =eq binT 4 (tcFn (liftc c a)) (tcFn (liftc c b))) :=
    substtc_inv_binT (substtc_inv_tcFn (liftc c a)) (substtc_inv_tcFn (liftc c b))
  have h1 := prf_to_prfH (prf_mp (pcc_congr_liftfcT_arg2_code (tcFn c)
      (tcFn (cons (numeralM 4) (cons a (cons b nil)))) (binT 4 (tcFn a) (tcFn b))
      (substtc_inv_tcFn c) (substtc_inv_tcFn (cons (numeralM 4) (cons a (cons b nil)))))
    (pcc_dot_bin_symm 4 a b)) [land (targetLiftAt c a) (targetLiftAt c b)]
  have h2 := prf_to_prfH (pcc_liftfc_eq_code c a b) [land (targetLiftAt c a) (targetLiftAt c b)]
  have h3 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_1_code 4
      (liftcT (tcFn c) (tcFn b)) (liftcT (tcFn c) (tcFn a)) (tcFn (liftc c a)) iLB iLA) _) hA
  have h4 := PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_binT_2_code 4 (tcFn (liftc c a))
      (liftcT (tcFn c) (tcFn b)) (tcFn (liftc c b))
      (substtc_inv_tcFn (liftc c a)) iLB) _) hB
  have h5 := prf_to_prfH (pcc_dot_bin 4 (liftc c a) (liftc c b))
    [land (targetLiftAt c a) (targetLiftAt c b)]
  have h6 := prf_to_prfH (prf_mp (prf_provCode_congr (prf_congr_eqCodeFn (prf_refl _)
      (prf_congr_tcFn (prf_eq_symm (prf_liftfc_eq c a b)))))
    (prf_provFromCode_eqCodeFn_refl
      (tcFn (cons (numeralM 4) (cons (liftc c a) (cons (liftc c b) nil))))))
    [land (targetLiftAt c a) (targetLiftAt c b)]
  refine PrfH_eq_trans_code _ _ _ iX0 h1
    (PrfH_eq_trans_code _ _ _ iX1 h2
      (PrfH_eq_trans_code _ _ _ iX2 h3
        (PrfH_eq_trans_code _ _ _ iX3 h4
          (PrfH_eq_trans_code _ _ _ iX4 h5 h6 ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_) ?_ ?_ ?_
    <;> hw_auto

/-! ### §9.2 · Los dos casos, DESCARGADOS — aquí entra A5 -/

/-- **`CasoAtomL` DESCARGADO.** Consume `DESCENSO_at_lista_imp` (A5): la evaluación provable de
    `liftsc` **al nivel `c`**, que es exactamente lo que `pcc_eval_liftc` clavado a `zero` no
    podía dar. -/
theorem casoAtomL_thm : CasoAtomL := by
  intro wT c X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (wfAll1 wT)
    (land (shapeBin X 3) (argsIn wT (nthc X (numeralM 2)))))
  have hwT := PrfH_and_elim_left hh
  have hR := PrfH_and_elim_right hh
  have hshape := PrfH_and_elim_left hR
  have hargs := PrfH_and_elim_right hR
  have hTB := PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_at_lista_imp c wT (nthc X (numeralM 2))) _)
    (PrfH_and_intro hwT hargs)
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (caso_atom_core_L c (nthc X (numeralM 1)) (nthc X (numeralM 2))) _) hTB
  exact PrfH_congr_targetLiftfc c (PrfH_eq_symm hshape) hC

/-- **`CasoEqL` DESCARGADO.** Consume `DESCENSO_at_imp` (A5) DOS veces. -/
theorem casoEqL_thm : CasoEqL := by
  intro wT c X
  refine prf_deduction ?_
  have hh := prfH_hyp_self (land (wfAll1 wT) (land (shapeBin X 4)
    (land (In (nthc X (numeralM 1)) wT) (In (nthc X (numeralM 2)) wT))))
  have hwT := PrfH_and_elim_left hh
  have hR := PrfH_and_elim_right hh
  have hshape := PrfH_and_elim_left hR
  have hin1 := PrfH_and_elim_left (PrfH_and_elim_right hR)
  have hin2 := PrfH_and_elim_right (PrfH_and_elim_right hR)
  have hTA := PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_at_imp c wT (nthc X (numeralM 1))) _)
    (PrfH_and_intro hwT hin1)
  have hTB := PrfH.mp _ _ _
    (prf_to_prfH (DESCENSO_at_imp c wT (nthc X (numeralM 2))) _)
    (PrfH_and_intro hwT hin2)
  have hC := PrfH.mp _ _ _
    (prf_to_prfH (caso_eq_core_L c (nthc X (numeralM 1)) (nthc X (numeralM 2))) _)
    (PrfH_and_intro hTA hTB)
  exact PrfH_congr_targetLiftfc c (PrfH_eq_symm hshape) hC

/-! ## §10 · 🏁🏁 `pcc_eval_liftfc`, SIN HIPÓTESIS -/

/-- ⭐⭐⭐ **`DEUDA_evalLiftfc_isFC1` PROBADA** — los ocho casos descargados. -/
theorem pcc_eval_liftfc_isFC1 : DEUDA_evalLiftfc_isFC1 :=
  pcc_eval_liftfc_modulo_2 casoAtomL_thm casoEqL_thm

/-- ⭐⭐⭐ **`DEUDA_evalLiftfc` PROBADA**: la evaluación provable de `liftfc` con el nivel `v` y
    el código `X` **abstractos**, bajo la sola guarda `hasWitF X`. -/
theorem pcc_eval_liftfc : DEUDA_evalLiftfc := deuda_of_isFC1 pcc_eval_liftfc_isFC1

/-- La forma desplegada, que es la que consumirá `Meta/SubstTreeReflect.lean`. -/
theorem pcc_eval_liftfc_wit (v X : Term) :
    Prf (Formula.impl (hasWitF X)
      (provFromCode (eqc (liftfcT (tcFn v) (tcFn X)) (tcFn (liftfc v X))))) :=
  pcc_eval_liftfc v X


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
  -- §1bis · la fontanería de `liftfcT` y los seis puentes `rfl` con el KIT
  prf_hasWit_liftfcT prf_congr_liftfcT prf_substtc_liftfcT substtc_inv_liftfcT
  botcT_termCode implcT_termCode forallcT_termCode andcT_termCode orcT_termCode excT_termCode
  -- §3 · las SEIS ecuaciones dotadas (faltan `atom` y `eq`, que consumen A5)
  LIFTFC_BOT_BODY LIFTFC_BOT_BODY_ok pcc_liftfc_bottom_code
  LIFTFC_BIN_BODY LIFTFC_IMPL_BODY_ok LIFTFC_AND_BODY_ok LIFTFC_OR_BODY_ok
  pcc_liftfc_bin_code pcc_liftfc_impl_code pcc_liftfc_and_code pcc_liftfc_or_code
  LIFTFC_UN_BODY LIFTFC_FORALL_BODY_ok LIFTFC_EX_BODY_ok
  pcc_liftfc_un_code pcc_liftfc_forall_code pcc_liftfc_ex_code
  -- §4‑§7 · EL CHASIS. ⚠️ `PHIliftfc*`, `PSIatL`, `CTXFliftfc` y las `ramaL_*` se quedan
  --    CUALIFICADOS por la misma razón que sus gemelos de `EvalSubstfcPrf`/`EvalLiftcPrf`:
  --    son el tercer descenso del árbol con esos mismos nombres.
  CasoBotL CasoAtomL CasoEqL CasoBinL CasoUnL
  DESCENSO_liftfc_imp pcc_eval_liftfc_modulo_8
  -- §8 · SEIS de los ocho, DESCARGADOS
  pcc_congr_liftfcT_arg2_code substF_targetLiftfc_hole PrfH_congr_targetLiftfc
  casoBotL casoBinL_gen casoBinL5 casoBinL7 casoBinL8 casoUnL_gen casoUnL6 casoUnL9
  pcc_eval_liftfc_modulo_2 deuda_modulo_2
  -- §9‑§10 · los DOS que consumen A5, y el TEOREMA
  LIFTFC_ATOM_BODY LIFTFC_ATOM_BODY_ok pcc_liftfc_atom_code
  LIFTFC_EQ_BODY LIFTFC_EQ_BODY_ok pcc_liftfc_eq_code
  caso_atom_core_L caso_eq_core_L casoAtomL_thm casoEqL_thm
  pcc_eval_liftfc_isFC1 pcc_eval_liftfc pcc_eval_liftfc_wit
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.liftfcT_termCode
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.deuda_of_isFC1
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_bottom_code
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_impl_code
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_forall_code
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_ex_code
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.PHIliftfc_step
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_modulo_8
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoBotL
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoBinL5
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoUnL6
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoUnL9
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_modulo_2
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_atom_code
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_liftfc_eq_code
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoAtomL_thm
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.casoEqL_thm
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftfcPrf.pcc_eval_liftfc_wit
