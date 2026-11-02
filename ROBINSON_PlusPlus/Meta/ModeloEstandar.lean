/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ModeloCodigo
import FOL.Semantics

/-!
# `Meta/ModeloEstandar.lean` — el modelo `MNV V` y los 34 `coreAxioms` (ADR‑119/120)

`MNV V : Model Nat` interpreta los 27 símbolos de función y los 5 de relación de los 120 (✏️ 28 y 142 hasta ADR‑192), con las funciones de
`Meta/ModeloCodigo.lean`; `V` es el valor de `axiomsCodeT`, y el modelo es PARAMÉTRICO en él: los 119 de la base
valen para TODO `V`, y sólo el ancla (`Meta/ModeloCodificacion.lean`) lo fija en `V₀`.

* Un lema `rfl` por símbolo (`MN_*`), para `V` VARIABLE. ⛔ No se escribe ningún `rfl` contra `V₀`: el núcleo
  despliega primero el lado de MÁS altura —`V₀`— y no acaba (2,5 GB en 12 s, medido; `@[irreducible]` no lo
  evita, ADR‑119 §3). Los 34 `v_*` reescriben con ellos y no despliegan `MNV` (D7, ADR‑129: con `List Char`,
  desplegar `MNV` en el `simp` agotaba el límite de `whnf`).
* La evaluación de los códigos cerrados por inducción, nunca por cómputo: `ev_numeralM`, `ev_strCodeM`,
  `ev_termCodeM`, `ev_formCodeM`, `ev_listFormCodeM`; y la de las guardas, para un término ARBITRARIO
  (`ev_hasWit`, `ev_hasWitF`).
* El `simp` que abre un axioma de codificación (`abre`), y los 34 `coreAxioms` (`MN_coreAxioms`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ROBINSON_PlusPlus.Meta.ModeloEstandar

/-! ## §2 · LA INTERPRETACIÓN

⚠️ `open` acotado: fuera de esta sección `≤` resuelve al símbolo OBJETO `le` (ADR‑085 §3). -/

section Interpretacion
open FOL
open FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.ModeloCodigo

variable {V : Nat}

/-- **El modelo estándar**: los 27 símbolos de función y los 5 de relación de los 120. Las listas, por la
    biyección de Cantor; los símbolos de codificación, por recursión (sobre la etiqueta de su argumento los de
    sustitución y lift, sobre `decodeL` `runFn`/`chainOk`, sobre el número `tcFn`); y
    `axiomsCodeT` por `V`, el PARÁMETRO: sólo la instancia `MNV V₀` lo fija en el valor del lado derecho del
    ancla. Despacha por patrones `sym!"…"` sobre el símbolo (`List Char`, D7). -/
def MNV (V : Nat) : Model Nat where
  func := fun s args =>
    match s, args with
    | sym!"0",  []     => 0
    | sym!"σ",  [a]    => a + 1
    | sym!"+",  [a, b] => a + b
    | sym!"*",  [a, b] => a * b
    | sym!"−",  [a, b] => a - b            -- monus, como dice el comentario de `sub_sym`
    | sym!"√",  [a]    => sqrtN a
    | sym!"/₂", [a]    => a / 2
    | sym!"%₂", [a]    => a % 2
    | sym!"τ",  [a]    => a - 1            -- `pred`
    | sym!"^",  [a, b] => a ^ b
    | sym!"::", [a, b] => consN a b
    | sym!"##", [a, b] => concatN a b
    | sym!"Π_p", [l]   => prodpN l
    | sym!"substtc", [k, s, c] => substtcN k s c
    | sym!"substtsc", [k, s, c] => substtscN k s c
    | sym!"liftc", [c, t] => liftcN c t
    | sym!"liftsc", [c, t] => liftscN c t
    | sym!"substfc", [v, t, f] => substfcN v t f
    | sym!"liftfc", [c, f] => liftfcN c f
    | sym!"carc", [l] => carN l
    | sym!"cdrc", [l] => cdrN l
    | sym!"lenc", [l] => lenN l
    | sym!"nthc", [l, i] => nthN l i
    | sym!"runFn", [c, r] => runFnN c r
    | sym!"tcFn", [t] => tcFnN t
    | sym!"premsOf", [l] => premsOfN l
    | sym!"axiomsCodeT", [] => V
    | _, _         => 0
  rel := fun s args =>
    match s, args with
    | sym!"<", [a, b] => a < b
    | sym!"∈", [x, l] => memN x l
    | sym!"allIn", [c, l] => allInN c l
    | sym!"lineWF", [l] => lineWFN V l
    | sym!"chainOk", [c, p] => chainOkN V c p
    | _, _        => False

/-! ### Un lema `rfl` por símbolo: así `simp` no tiene que abrir el `match` de 33 ramas -/

theorem MN_zero : (MNV V).func sym!"0" [] = 0 := rfl
theorem MN_add (a b : Nat) : (MNV V).func sym!"+" [a, b] = a + b := rfl
theorem MN_mul (a b : Nat) : (MNV V).func sym!"*" [a, b] = a * b := rfl
theorem MN_sub (a b : Nat) : (MNV V).func sym!"−" [a, b] = a - b := rfl
theorem MN_sqrt (a : Nat) : (MNV V).func sym!"√" [a] = sqrtN a := rfl
theorem MN_div2 (a : Nat) : (MNV V).func sym!"/₂" [a] = a / 2 := rfl
theorem MN_mod2 (a : Nat) : (MNV V).func sym!"%₂" [a] = a % 2 := rfl
theorem MN_pow (a b : Nat) : (MNV V).func sym!"^" [a, b] = a ^ b := rfl
theorem MN_prodp (l : Nat) : (MNV V).func sym!"Π_p" [l] = prodpN l := rfl
theorem MN_succ (a : Nat) : (MNV V).func sym!"σ" [a] = a + 1 := rfl
theorem MN_pred (a : Nat) : (MNV V).func sym!"τ" [a] = a - 1 := rfl
theorem MN_cons (a b : Nat) : (MNV V).func sym!"::" [a, b] = consN a b := rfl
theorem MN_concat (a b : Nat) : (MNV V).func sym!"##" [a, b] = concatN a b := rfl
theorem MN_substtc (k s c : Nat) : (MNV V).func sym!"substtc" [k, s, c] = substtcN k s c := rfl
theorem MN_substtsc (k s c : Nat) : (MNV V).func sym!"substtsc" [k, s, c] = substtscN k s c := rfl
theorem MN_liftc (c t : Nat) : (MNV V).func sym!"liftc" [c, t] = liftcN c t := rfl
theorem MN_liftsc (c t : Nat) : (MNV V).func sym!"liftsc" [c, t] = liftscN c t := rfl
theorem MN_substfc (v t f : Nat) : (MNV V).func sym!"substfc" [v, t, f] = substfcN v t f := rfl
theorem MN_liftfc (c f : Nat) : (MNV V).func sym!"liftfc" [c, f] = liftfcN c f := rfl
theorem MN_carc (l : Nat) : (MNV V).func sym!"carc" [l] = carN l := rfl
theorem MN_cdrc (l : Nat) : (MNV V).func sym!"cdrc" [l] = cdrN l := rfl
theorem MN_lenc (l : Nat) : (MNV V).func sym!"lenc" [l] = lenN l := rfl
theorem MN_nthc (l i : Nat) : (MNV V).func sym!"nthc" [l, i] = nthN l i := rfl
theorem MN_runFn (c r : Nat) : (MNV V).func sym!"runFn" [c, r] = runFnN c r := rfl
theorem MN_tcFn (t : Nat) : (MNV V).func sym!"tcFn" [t] = tcFnN t := rfl
theorem MN_premsOf (l : Nat) : (MNV V).func sym!"premsOf" [l] = premsOfN l := rfl
theorem MN_axiomsCodeT : (MNV V).func sym!"axiomsCodeT" [] = V := rfl
theorem MN_lt (a b : Nat) : (MNV V).rel sym!"<" [a, b] = (a < b) := rfl
theorem MN_mem (x l : Nat) : (MNV V).rel sym!"∈" [x, l] = memN x l := rfl
theorem MN_allIn (c l : Nat) : (MNV V).rel sym!"allIn" [c, l] = allInN c l := rfl
theorem MN_lineWF (l : Nat) : (MNV V).rel sym!"lineWF" [l] = lineWFN V l := rfl
theorem MN_chainOk (c p : Nat) : (MNV V).rel sym!"chainOk" [c, p] = chainOkN V c p := rfl

/-! ### La evaluación, constructor a constructor, con PRUEBA

⛔ No van por `rfl`, a propósito (✏️ 2026‑11‑02): `simp` usa un lema `rfl` como reescritura DEFINICIONAL, sin prueba en
el término, y deja al núcleo comprobar que el objetivo de antes y el de después coinciden por definición. Con las
ecuaciones de `evalFormula`, `evalTerm` y `evalTerms`, eso es desplegar la evaluación de un átomo en el modelo CONCRETO
`MNV V`, y nanoda, con cuatro hilos, agota la pila de sus hilos (ADR‑228; medido en WSL: `ev_hasWit` agota, y con estos
lemas en su `simp` acepta en 0,3 s). Con prueba, el núcleo sólo instancia el lema, que se comprobó una vez, para un
modelo cualquiera. -/

theorem evf_bot {D : Type} (M : Model D) (v : Nat → D) : evalFormula M v Formula.bottom = False := by
  rw [evalFormula]
theorem evf_atom {D : Type} (M : Model D) (v : Nat → D) (s : List Char) (ts : List Term) :
    evalFormula M v (Formula.atom s ts) = M.rel s (evalTerms M v ts) := by rw [evalFormula]
theorem evf_eq {D : Type} (M : Model D) (v : Nat → D) (a b : Term) :
    evalFormula M v (Formula.eq a b) = (evalTerm M v a = evalTerm M v b) := by rw [evalFormula]
theorem evf_impl {D : Type} (M : Model D) (v : Nat → D) (f g : Formula) :
    evalFormula M v (Formula.impl f g) = (evalFormula M v f → evalFormula M v g) := by rw [evalFormula]
theorem evf_forall {D : Type} (M : Model D) (v : Nat → D) (f : Formula) :
    evalFormula M v (Formula.forall f) = ∀ d, evalFormula M (shiftEnv v d) f := by rw [evalFormula]
theorem evf_and {D : Type} (M : Model D) (v : Nat → D) (f g : Formula) :
    evalFormula M v (Formula.and f g) = (evalFormula M v f ∧ evalFormula M v g) := by rw [evalFormula]
theorem evf_or {D : Type} (M : Model D) (v : Nat → D) (f g : Formula) :
    evalFormula M v (Formula.or f g) = (evalFormula M v f ∨ evalFormula M v g) := by rw [evalFormula]
theorem evf_ex {D : Type} (M : Model D) (v : Nat → D) (f : Formula) :
    evalFormula M v (Formula.ex f) = ∃ d, evalFormula M (shiftEnv v d) f := by rw [evalFormula]
theorem evt_var {D : Type} (M : Model D) (v : Nat → D) (n : Nat) : evalTerm M v (Term.var n) = v n := by
  rw [evalTerm]
theorem evt_func {D : Type} (M : Model D) (v : Nat → D) (s : List Char) (ts : List Term) :
    evalTerm M v (Term.func s ts) = M.func s (evalTerms M v ts) := by rw [evalTerm]
theorem evts_nil {D : Type} (M : Model D) (v : Nat → D) : evalTerms M v [] = [] := by rw [evalTerms]
theorem evts_cons {D : Type} (M : Model D) (v : Nat → D) (t : Term) (ts : List Term) :
    evalTerms M v (t :: ts) = evalTerm M v t :: evalTerms M v ts := by rw [evalTerms]

/-- `zero` y `cons` en `MNV V`, con prueba (como los de arriba): las usan las evaluaciones de los códigos cerrados. -/
theorem evc_zero (v : Nat → Nat) : evalTerm (MNV V) v zero = 0 := by
  rw [zero, evt_func, evts_nil, zero_sym, MN_zero]
theorem evc_cons (v : Nat → Nat) (a b : Term) :
    evalTerm (MNV V) v (cons a b) = consN (evalTerm (MNV V) v a) (evalTerm (MNV V) v b) := by
  rw [cons, evt_func, evts_cons, evts_cons, evts_nil, cons_sym, MN_cons]

/-! ### La evaluación de los CÓDIGOS cerrados: por inducción, nunca por cómputo -/

theorem ev_numeralM (v : Nat → Nat) : ∀ n : Nat, evalTerm (MNV V) v (numeralM n) = n
  | 0 => rfl
  | n + 1 => by
      show (MNV V).func succ_sym [evalTerm (MNV V) v (numeralM n)] = n + 1
      rw [ev_numeralM v n]; rfl

theorem ev_charsCodeM (v : Nat → Nat) : ∀ cs : List Char, evalTerm (MNV V) v (charsCodeM cs) = codeNatChars cs
  | [] => by rw [charsCodeM, nil, evc_zero, codeNatChars]
  | c :: cs => by rw [charsCodeM, evc_cons, ev_numeralM, ev_charsCodeM v cs, codeNatChars]

theorem ev_strCodeM (v : Nat → Nat) (s : List Char) : evalTerm (MNV V) v (strCodeM s) = codeNatStr s :=
  ev_charsCodeM v s

mutual
theorem ev_termCodeM (v : Nat → Nat) (t : Term) : evalTerm (MNV V) v (termCodeM t) = codeNatTerm t := by
  match t with
  | .var n => rw [termCodeM, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_numeralM, codeNatTerm]
  | .func s ts =>
    rw [termCodeM, evc_cons, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_strCodeM, ev_termsCodeM v ts,
      codeNatTerm]
theorem ev_termsCodeM (v : Nat → Nat) (ts : List Term) : evalTerm (MNV V) v (termsCodeM ts) = codeNatTerms ts := by
  match ts with
  | [] => rw [termsCodeM, nil, evc_zero, codeNatTerms]
  | t :: ts' => rw [termsCodeM, evc_cons, ev_termCodeM v t, ev_termsCodeM v ts', codeNatTerms]
end

theorem ev_formCodeM (v : Nat → Nat) : ∀ φ : Formula, evalTerm (MNV V) v (formCodeM φ) = codeNat φ
  | .bottom => by rw [formCodeM, evc_cons, nil, evc_zero, ev_numeralM, codeNat]
  | .atom p ts => by
      rw [formCodeM, evc_cons, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_strCodeM, ev_termsCodeM, codeNat]
  | .eq t u => by
      rw [formCodeM, evc_cons, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_termCodeM, ev_termCodeM, codeNat]
  | .impl a b => by
      rw [formCodeM, evc_cons, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_formCodeM v a, ev_formCodeM v b,
        codeNat]
  | Formula.forall a => by
      rw [formCodeM, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_formCodeM v a, codeNat]
  | .and a b => by
      rw [formCodeM, evc_cons, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_formCodeM v a, ev_formCodeM v b,
        codeNat]
  | .or a b => by
      rw [formCodeM, evc_cons, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_formCodeM v a, ev_formCodeM v b,
        codeNat]
  | .ex a => by
      rw [formCodeM, evc_cons, evc_cons, nil, evc_zero, ev_numeralM, ev_formCodeM v a, codeNat]

theorem ev_listFormCodeM (v : Nat → Nat) : ∀ L : List Formula, evalTerm (MNV V) v (listFormCodeM L) = codeNatList L
  | [] => by rw [listFormCodeM, nil, evc_zero, codeNatList]
  | f :: fs => by rw [listFormCodeM, evc_cons, ev_formCodeM, ev_listFormCodeM v fs, codeNatList]

/-! ### Las guardas: su evaluación es la `Prop` de §1ter, para un término ARBITRARIO -/

theorem ev_lift0 (v : Nat → Nat) (d : Nat) (t : Term) :
    evalTerm (MNV V) (shiftEnv v d) (liftTerm 0 t) = evalTerm (MNV V) v t := by
  have h := eval_liftTerm_ext (MNV V) v d 0 t
  have heq : updateEnv 0 v d = shiftEnv v d := by funext n; exact updateEnv_zero v d n
  rw [heq] at h; exact h

theorem ev_hasWit (v : Nat → Nat) (t : Term) : evalFormula (MNV V) v (hasWit t) ↔ hasWitN (evalTerm (MNV V) v t) := by
  simp only [hasWit, isTC1, wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn, argsInBody,
    land, lor, lt, In, lenc, nthc, cons, nil, zero, lt_sym, in_sym, cons_sym, zero_sym,
    evf_atom, evf_eq, evf_impl, evf_forall, evf_and, evf_or, evf_ex, evt_var, evt_func, evts_nil, evts_cons, shiftEnv, liftTerm, liftTerms, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, ev_lift0, ev_numeralM,
    MN_lt, MN_mem, MN_lenc, MN_nthc, MN_cons, MN_zero,
    hasWitN, wfAll1N, isTermCodeE1N, shapeUnN, shapeBinN, argsInN]

theorem ev_hasWitF (v : Nat → Nat) (t : Term) : evalFormula (MNV V) v (hasWitF t) ↔ hasWitFN (evalTerm (MNV V) v t) := by
  simp only [hasWitF, isFC1, wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, shapeNul, argsIn, argsInBody,
    wfAllF, wfAllFBody, isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn,
    land, lor, lt, In, lenc, nthc, cons, nil, zero, lt_sym, in_sym, cons_sym, zero_sym,
    evf_atom, evf_eq, evf_impl, evf_forall, evf_and, evf_or, evf_ex, evt_var, evt_func, evts_nil, evts_cons, shiftEnv, liftTerm, liftTerms, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, ev_lift0, ev_numeralM,
    MN_lt, MN_mem, MN_lenc, MN_nthc, MN_cons, MN_zero,
    hasWitFN, wfAll1N, wfAllFN, isTermCodeE1N, isFormCodeE2N, shapeUnN, shapeBinN, argsInN,
    clBotN, clAtomN, clEqN, clBinN, clUnN]

/-- El `simp` que ABRE un axioma de codificación: los conectivos, los constructores de código, la evaluación
    (✏️ 2026‑11‑02, ADR‑251: por los lemas CON PRUEBA de arriba, `evf_*`, `evt_*` y `evts_*`, no por las ecuaciones de
    `evalFormula`, `evalTerm` y `evalTerms`) y un lema `rfl` por símbolo. ⛔ Sin `numeralM`, `termCodeM`, `strCodeM` ni ningún `codeNat*`: los códigos
    cerrados se evalúan por sus lemas ∀ (`ev_*`), nunca desplegándolos. -/
scoped macro "abre" : tactic => `(tactic| simp only [forall_, forall_2, forall_3, forall_4, _root_.iff,
    land, lor, cons, nil, zero, succ, pred, concat, lt, In, cons_sym, zero_sym, succ_sym, pred_sym,
    concat_sym, lt_sym, in_sym, substtc, substtsc, liftc, liftsc, substfc, liftfc, carc, cdrc, lenc, nthc,
    runFn, tcFn, premsOf, allIn, lineWF, chainOk, lineOk, varc, funcc, botc, atomc, eqc,
    implc, forallc, andc, orc, exc, axiomsCodeT, lineTag, tagDisj,
    evf_bot, evf_atom, evf_eq, evf_impl, evf_forall, evf_and, evf_or, evf_ex, evt_var, evt_func, evts_nil, evts_cons, shiftEnv, ev_numeralM, ev_strCodeM, ev_termCodeM, ev_hasWit, ev_hasWitF,
    MN_zero, MN_succ, MN_pred, MN_cons, MN_concat, MN_substtc, MN_substtsc, MN_liftc, MN_liftsc, MN_substfc,
    MN_liftfc, MN_carc, MN_cdrc, MN_lenc, MN_nthc, MN_runFn, MN_tcFn, MN_premsOf, MN_axiomsCodeT,
    MN_lt, MN_mem, MN_allIn, MN_lineWF, MN_chainOk])

/-! ### Los axiomas core de ARITMÉTICA, validados -/

theorem v_ax2  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax2_peano_succ_neq_zero := by
  intro v d; simp [succ, zero, succ_sym, zero_sym, neg,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_succ]

theorem v_ax3  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax3_peano_succ_inj := by
  intro v d d'; simp [succ, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_succ]

theorem v_ax4  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax4_add_zero := by
  intro v d; simp [add, zero, add_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_add]

theorem v_ax18 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax18_lt_irrefl := by
  intro v d; simp [lt, lt_sym, neg,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_lt]

theorem v_ax25 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax25_pred_zero := by
  -- ⚠️ `ax25_pred_zero` NO es un `forall_`: sin su nombre en el `simp` no hay nada que abrir.
  -- El linter lo marcó «no usado» en los OTROS siete (allí `forall_` lo abre) y aquí NO.
  -- 🔑 *Un aviso de «no usado» no es una medición de que sobre.* Segunda vez en esta sesión.
  intro v; simp [ax25_pred_zero, pred, zero, pred_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, MN_zero, MN_pred]

theorem v_ax26 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax26_pred_succ := by
  intro v d; simp [pred, succ, pred_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_succ, MN_pred]

/-- ⭐ Los dos que necesitaban la raíz. -/
theorem v_ax14 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax14_sqrt_le := by
  intro v d
  simp only [le, lt, sq, mul, sqrt, lt_sym, mul_sym, sqrt_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_mul, MN_sqrt, MN_lt]
  have := sqrtN_le d
  omega

theorem v_ax15 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax15_lt_succ_sqrt := by
  intro v d
  simp only [lt, sq, mul, succ, sqrt, lt_sym, mul_sym, succ_sym,
    sqrt_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_succ, MN_mul, MN_sqrt, MN_lt]
  exact lt_sq_succ_sqrtN d

/-! ### §2bis · El resto de la capa ARITMÉTICA

⭐ Todos siguen el mismo molde que los ocho de arriba: `intro` de los binders, `simp` que abre
la evaluación, y un `Nat.*` del core o un `omega` para rematar. **No hubo que inventar nada por
axioma** — que es lo que M2 (ADR‑085) predijo y aquí se confirma sobre quince más. -/

theorem v_ax5  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax5_add_succ := by
  intro v d d'; simp [add, succ, add_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_succ, MN_add]
  omega

theorem v_ax6  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax6_add_comm := by
  intro v d d'; simp [add, add_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_add]
  omega

theorem v_ax7  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax7_add_assoc := by
  intro v d d' d''; simp [add, add_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_add]
  omega

theorem v_ax8  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax8_mul_zero := by
  intro v d; simp [mul, zero, mul_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_mul]

theorem v_ax9  : ∀ v : Nat → Nat, evalFormula (MNV V) v ax9_mul_succ := by
  intro v d d'; simp [mul, add, succ, mul_sym, add_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_succ, MN_add, MN_mul]
  exact Nat.mul_succ _ _

theorem v_ax10 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax10_mul_comm := by
  intro v d d'; simp [mul, mul_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_mul]
  exact Nat.mul_comm _ _

theorem v_ax11 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax11_mul_assoc := by
  intro v d d' d''; simp [mul, mul_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_mul]
  exact Nat.mul_assoc _ _ _

theorem v_ax12 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax12_mul_distrib := by
  intro v d d' d''; simp [mul, add, mul_sym, add_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_add, MN_mul]
  exact Nat.mul_add _ _ _

/-! #### La paridad: `omega` conoce `/2` y `%2` por literales -/

theorem v_ax16 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax16_mod2_succ := by
  -- (✏️ 2026‑10‑21, T61, ADR‑189: sin `simp` a secas ni `omega`, que metían `Classical.propDecidable` en
  -- `consistencia` y en lo que depende de ella; la paridad, por casos con `Nat.mod_two_eq_zero_or_one`.)
  intro v d
  simp only [_root_.iff, mod2, succ, zero, one, mod2_sym, succ_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_succ, MN_mod2]
  have hm := Nat.add_mod d 1 2
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · refine ⟨fun _ => ?_, fun _ => h⟩
    rw [hm, h]
  · refine ⟨fun h0 => absurd (h.symm.trans h0) (by decide), fun h1 => ?_⟩
    rw [hm, h] at h1
    exact absurd h1 (by decide)

theorem v_ax17 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax17_div_mod_eq := by
  intro v d; simp [add, mul, div2, mod2, two, one, succ, zero,
    add_sym, mul_sym, div2_sym, mod2_sym, succ_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_succ, MN_add, MN_mul, MN_div2, MN_mod2]
  omega

theorem v_ax21 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax21_mod2_range := by
  intro v d; simp [mod2, zero, one, succ, mod2_sym, zero_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_succ, MN_mod2]
  omega

theorem v_ax24 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax24_mod2_of_even := by
  intro v d d'; simp [mod2, mul, two, one, succ, zero, mod2_sym, mul_sym, succ_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_succ, MN_mul, MN_mod2]
  omega

/-! #### Monus y potencia -/

theorem v_ax29 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax29_sub_witness := by
  intro v d d'; simp [le, lt, add, sub, lt_sym, add_sym, sub_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_add, MN_sub, MN_lt]
  omega

theorem v_pow_zero : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_pow_zero := by
  intro v d; simp [pow, zero, one, succ, pow_sym, zero_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_succ, MN_pow]

theorem v_pow_succ : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_pow_succ := by
  intro v d d'; simp [pow, mul, succ, pow_sym, mul_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_succ, MN_mul, MN_pow]
  exact Nat.pow_succ _ _

/-! #### El ORDEN. ⭐ `ax13` DEFINE `<` por un `∃`, así que aquí se comprueba que la relación
que el modelo eligió (`a < b` de `Nat`) es **la que el axioma exige**, no una cualquiera. -/

theorem v_ax13 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax13_lt_def := by
  intro v d d'; simp [_root_.iff, lt, add, succ, lt_sym, add_sym, succ_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_succ, MN_add, MN_lt]
  constructor
  · intro h; exact ⟨d' - d - 1, by omega⟩
  · -- ⚠️ `simp` convirtió el `∃k. …` del antecedente en un `∀k`, así que se introduce COMO TAL.
    intro k hk; omega

theorem v_ax19 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax19_lt_trichotomy := by
  intro v d d'; simp [lt, lt_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_lt]
  omega

/-! ### Los axiomas core de LISTAS, validados (2026‑10‑05)

Cada uno se abre con el mismo `simp` que los de aritmética y se cierra con su lema de §1bis: `simp` NO despliega
`decodeL` (recursión bien fundada) ni `consN`, así que el paso que importa lo da el lema, a mano. -/

/-- `pair x y` evaluado en el modelo es `pairN x y`: el polinomio de Cantor es `2·pairN` (`two_mul_pairN`). -/
theorem eval_cantor (a b : Nat) : ((a + b) * (a + b + 1) + 2 * b) / 2 = pairN a b := by
  have h := ROBINSON_PlusPlus.Meta.CodeNumeralPrf.two_mul_pairN a b
  omega

theorem v_axL0 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_L0_cons_def := by
  intro v d d'
  simp only [cons, succ, pair, cantor_func, cantor_poly, div2, add, mul, two, one,
    zero, cons_sym, succ_sym, div2_sym, add_sym, mul_sym, zero_sym, evalFormula, evalTerm, evalTerms,
    shiftEnv, MN_zero, MN_succ, MN_add, MN_mul, MN_div2, MN_cons]
  have h := eval_cantor d d'
  rw [consN_eq]
  omega

theorem v_axL1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_L1_in_nil := by
  intro v d
  simp only [neg, In, nil, zero, in_sym, zero_sym, evalFormula, evalTerm, evalTerms,
    shiftEnv, MN_zero, MN_mem]
  exact memN_zero d

theorem v_axL2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_L2_in_cons := by
  intro v d d' d''
  simp only [_root_.iff, lor, In, cons, in_sym, cons_sym, evalFormula, evalTerm,
    evalTerms, shiftEnv, MN_cons, MN_mem]
  exact ⟨(memN_consN d d' d'').mp, (memN_consN d d' d'').mpr⟩

theorem v_axC1 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_C1_concat_nil := by
  intro v d
  simp only [concat, nil, zero, concat_sym, zero_sym, evalFormula, evalTerm,
    evalTerms, shiftEnv, MN_zero, MN_concat]
  exact concatN_zero d

theorem v_axC2 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_C2_concat_cons := by
  intro v d d' d''
  simp only [concat, cons, concat_sym, cons_sym, evalFormula, evalTerm,
    evalTerms, shiftEnv, MN_cons, MN_concat]
  exact concatN_consN d d' d''

theorem v_axC3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_C3_concat_assoc := by
  intro v d d' d''
  simp only [concat, concat_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_concat]
  exact concatN_assoc d d' d''

theorem v_axL3 : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_L3_in_concat := by
  intro v d d' d''
  simp only [_root_.iff, lor, In, concat, in_sym, concat_sym, evalFormula,
    evalTerm, evalTerms, shiftEnv, MN_concat, MN_mem]
  exact ⟨(memN_concatN d d' d'').mp, (memN_concatN d d' d'').mpr⟩

theorem v_prodp_nil : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_prodp_nil := by
  intro v
  simp only [ax_prodp_nil, prod_pairs, nil, one, succ, zero, prodp_sym, succ_sym, zero_sym, evalFormula,
    evalTerm, evalTerms, MN_zero, MN_succ, MN_prodp]
  exact prodpN_zero

theorem v_prodp_cons : ∀ v : Nat → Nat, evalFormula (MNV V) v ax_prodp_cons := by
  intro v d d' d''
  simp only [prod_pairs, cons, pair, cantor_func, cantor_poly, div2, add, mul, two,
    one, succ, zero, pow, prodp_sym, cons_sym, div2_sym, add_sym, mul_sym, succ_sym, zero_sym, pow_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, MN_zero, MN_succ, MN_add, MN_mul, MN_div2, MN_pow, MN_prodp, MN_cons]
  have h : ((d + d') * (d + d' + 1) + (0 + 1 + 1) * d') / 2 = pairN d d' := by
    have := eval_cantor d d'
    omega
  rw [h, prodpN_consN_pairN]

/-- Para cerrar `∀ φ ∈ a :: l, p φ` de uno en uno (sin `List.Forall`, que el core no trae). -/
theorem mem_cons_elim {α : Type} {p : α → Prop} {a : α} {l : List α} (ha : p a)
    (hl : ∀ x, List.Mem x l → p x) : ∀ x, List.Mem x (a :: l) → p x := by
  intro x hx
  cases hx with
  | head => exact ha
  | tail _ h => exact hl x h

theorem mem_nil_elim {α : Type} {p : α → Prop} : ∀ x, List.Mem x ([] : List α) → p x :=
  fun _ h => nomatch h

/-- 🏁 **El modelo estándar satisface los 34 `coreAxioms`** (2026‑10‑05): la capa aritmética (25) y la de
    listas (9). Los 85 de `codingAxioms` y el ancla van aparte, y `MN_axioms` junta los 120. -/
theorem MN_coreAxioms (v : Nat → Nat) : ∀ φ, List.Mem φ coreAxioms → evalFormula (MNV V) v φ := by
  unfold coreAxioms
  exact mem_cons_elim (v_ax2 v) (mem_cons_elim (v_ax3 v) (mem_cons_elim (v_ax4 v) (mem_cons_elim (v_ax5 v) (mem_cons_elim (v_ax6 v) (mem_cons_elim (v_ax7 v) (mem_cons_elim (v_ax8 v) (mem_cons_elim (v_ax9 v) (mem_cons_elim (v_ax10 v) (mem_cons_elim (v_ax11 v) (mem_cons_elim (v_ax12 v) (mem_cons_elim (v_ax13 v) (mem_cons_elim (v_ax14 v) (mem_cons_elim (v_ax15 v) (mem_cons_elim (v_ax16 v) (mem_cons_elim (v_ax17 v) (mem_cons_elim (v_ax18 v) (mem_cons_elim (v_ax19 v) (mem_cons_elim (v_ax21 v) (mem_cons_elim (v_ax24 v) (mem_cons_elim (v_ax25 v) (mem_cons_elim (v_ax26 v) (mem_cons_elim (v_axL0 v) (mem_cons_elim (v_axL1 v) (mem_cons_elim (v_axL2 v) (mem_cons_elim (v_axC1 v) (mem_cons_elim (v_axC2 v) (mem_cons_elim (v_axC3 v) (mem_cons_elim (v_axL3 v) (mem_cons_elim (v_ax29 v) (mem_cons_elim (v_pow_zero v) (mem_cons_elim (v_pow_succ v) (mem_cons_elim (v_prodp_nil v) (mem_cons_elim (v_prodp_cons v) (mem_nil_elim))))))))))))))))))))))))))))))))))

end Interpretacion

end ROBINSON_PlusPlus.Meta.ModeloEstandar

#print axioms ROBINSON_PlusPlus.Meta.ModeloEstandar.MN_coreAxioms
