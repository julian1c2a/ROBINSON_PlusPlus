/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.RigidezEstandar

/-!
# `Meta/SegundoModelo.lean` — 🏁 UN SEGUNDO modelo estándar: sobre la basura, `M` es libre (T75d, ADR‑175)

`Meta/RigidezEstandar.lean` demuestra W1 y E10 para todo `Estandar M`, y advierte que sobre la basura `M` puede no
ser `MNV V₀`. Aquí está el testigo. `MNB V₀` es `MNV V₀` con OTRA `substfc` —sobre un código que no tiene forma de
fórmula lo deja como está, donde `substfcN` da `0`— y con `validProofFn` recalculada con ella. Valida los 142, es
estándar (`estandar_MB`) y no es `MNV V₀` (`MNB_ne_MNV`).

**Ningún axioma fija `substfc` sobre la basura** (la pregunta (d) de T75): las ocho ecuaciones de `substfc` hablan de
códigos con forma; las cinco reglas de `lineWF` que sustituyen (`q1`, `q2`, `leibniz`, `ind`, `listInd`) piden
`hasWitF`/`hasWit` de sus argumentos —las guardas de ADR‑020—, y sobre los códigos buenos `substfcB` es `substfcN`
(`substfcB_codF`); las 22 de `validProofFn` no tienen guarda, pero `validProofFn` no la usa nadie más y se
reinterpreta con `stepTB`. Ningún axioma lo impide, así que las guardas no se abaratan.

* **§1 · `substfcB`**: la de `substfcN` con otra rama de basura; sus ocho ecuaciones, y `substfcB_codF`.
* **§2 · `vpfNB`**: `validProofFn` con `substfcB` en las cinco etiquetas que sustituyen.
* **§3 · `MNB V`**: `substfc` y `validProofFn` cambiadas, todo lo demás de `MNV V`; `MB_ne_MN`, la diferencia.
* **§4 · `agreeF`**: donde no aparecen `substfc` ni `validProofFn` (`libreF`), los dos modelos evalúan IGUAL.
* **§5 · Los códigos cerrados y las guardas** en `MNB V`: los cerrados, por `agreeF`; las guardas, como en `MNV`.
* **§6 · Los 35 que nombran `substfc` o `validProofFn`**, uno a uno (las cinco de `lineWF`, por las guardas).
* **§7 · El ancla**, por `rw` con lemas ∀ (`substfcB_codF` sobre el código de `ψ`, que es bueno).
* **§8 · Los 142** —los otros 106, transportados por `agreeF`—, `estandar_MB`, `segundo_modelo` y
  `modelo_prov_iff_MB`: las generalizaciones de T75e tienen ahora DOS instancias distintas.

⚙️ **`decide +kernel`** (la primera vez en el proyecto): `libreF φ = true` de los 106 axiomas libres lo evalúa el
NÚCLEO; no añade axiomas (`#print axioms` no cambia), a diferencia del `decide` nativo. El `decide` del elaborador
agota su recursión en `ax_tc_succ` (el numeral 963 del carácter `σ`). Ninguno de los 106 lleva un numeral grande: los
códigos cerrados `TC0`…`TCONS` sólo salen en axiomas que nombran `substfc` o `validProofFn` (medido: los 106 cierran y
el módulo compila en 15 s).
⛔ El ancla, como `v_ancla`, por `rw`: un `show` que escribía su evaluación entera hizo que el núcleo recursara hasta
agotarse (2 min), y la declaración quedó como AXIOMA en `#print axioms` de lo que la usaba (medido, en el sondeo).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL FOL.Metamath.Semantics
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.SolidezPrf
open ROBINSON_PlusPlus.Meta.ModeloEstandar ROBINSON_PlusPlus.Meta.ModeloCodificacion
open ROBINSON_PlusPlus.Meta.RosserNumEval

namespace ROBINSON_PlusPlus.Meta.SegundoModelo

/-! ## §1 · `substfcB`: la sustitución, con OTRA basura -/

def substfcB (v t f : Nat) : Nat :=
  if h : f = 0 then 0
  else if nthN f 0 = 2 then consN 2 0
  else if nthN f 0 = 3 then consN 3 (consN (nthN f 1) (consN (substtscN v t (nthN f 2)) 0))
  else if nthN f 0 = 4 then consN 4 (consN (substtcN v t (nthN f 1)) (consN (substtcN v t (nthN f 2)) 0))
  else if nthN f 0 = 5 then consN 5 (consN (substfcB v t (nthN f 1)) (consN (substfcB v t (nthN f 2)) 0))
  else if nthN f 0 = 6 then consN 6 (consN (substfcB (v + 1) (liftcN 0 t) (nthN f 1)) 0)
  else if nthN f 0 = 7 then consN 7 (consN (substfcB v t (nthN f 1)) (consN (substfcB v t (nthN f 2)) 0))
  else if nthN f 0 = 8 then consN 8 (consN (substfcB v t (nthN f 1)) (consN (substfcB v t (nthN f 2)) 0))
  else if nthN f 0 = 9 then consN 9 (consN (substfcB (v + 1) (liftcN 0 t) (nthN f 1)) 0)
  else f
termination_by f
decreasing_by all_goals exact nthN_lt _ h

theorem substfcB_bot (v t : Nat) : substfcB v t (consN 2 0) = consN 2 0 := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, dite_false, ite_true]

theorem substfcB_atom (v t a b : Nat) : substfcB v t (consN 3 (consN a (consN b 0))) =
    consN 3 (consN a (consN (substtscN v t b) 0)) := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcB_eq (v t a b : Nat) : substfcB v t (consN 4 (consN a (consN b 0))) =
    consN 4 (consN (substtcN v t a) (consN (substtcN v t b) 0)) := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcB_impl (v t a b : Nat) : substfcB v t (consN 5 (consN a (consN b 0))) =
    consN 5 (consN (substfcB v t a) (consN (substfcB v t b) 0)) := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcB_forall (v t a : Nat) : substfcB v t (consN 6 (consN a 0)) =
    consN 6 (consN (substfcB (v + 1) (liftcN 0 t) a) 0) := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcB_and (v t a b : Nat) : substfcB v t (consN 7 (consN a (consN b 0))) =
    consN 7 (consN (substfcB v t a) (consN (substfcB v t b) 0)) := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcB_or (v t a b : Nat) : substfcB v t (consN 8 (consN a (consN b 0))) =
    consN 8 (consN (substfcB v t a) (consN (substfcB v t b) 0)) := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem substfcB_ex (v t a : Nat) : substfcB v t (consN 9 (consN a 0)) =
    consN 9 (consN (substfcB (v + 1) (liftcN 0 t) a) 0) := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

/-- Sobre los códigos BUENOS, `substfcB` es `substfcN`, para todo sustituyendo. -/
theorem substfcB_codF {f : Nat} (hf : CodF f) : ∀ (v t : Nat), substfcB v t f = substfcN v t f := by
  induction hf with
  | bot => intro v t; rw [substfcB_bot, substfcN_bot]
  | atom p ts _ => intro v t; rw [substfcB_atom, substfcN_atom]
  | eq a b _ _ => intro v t; rw [substfcB_eq, substfcN_eq]
  | impl a b _ _ iha ihb => intro v t; rw [substfcB_impl, substfcN_impl, iha, ihb]
  | all a _ iha => intro v t; rw [substfcB_forall, substfcN_forall, iha]
  | and a b _ _ iha ihb => intro v t; rw [substfcB_and, substfcN_and, iha, ihb]
  | or a b _ _ iha ihb => intro v t; rw [substfcB_or, substfcN_or, iha, ihb]
  | ex a _ iha => intro v t; rw [substfcB_ex, substfcN_ex, iha]

theorem substfcB_g {f : Nat} (h : hasWitFN f) (v t : Nat) : substfcB v t f = substfcN v t f :=
  substfcB_codF (codF_of_hasWitFN h) v t

/-- Y sobre la basura, NO: `⟨10⟩` no es el código de nada; `substfcN` lo manda a `0` y `substfcB` lo deja. -/
theorem substfcN_basura : substfcN 0 0 (consN 10 0) = 0 := by
  rw [substfcN]; simp only [consN_ne_zero, nthN_cz, dite_false]; rfl

theorem substfcB_basura : substfcB 0 0 (consN 10 0) = consN 10 0 := by
  rw [substfcB]; simp only [consN_ne_zero, nthN_cz, dite_false]; rfl

/-! ## §2 · `validProofFn` con `substfcB` -/

def stepTB : Nat → Nat → Nat → Nat → Nat
  | 0, a, b, _ => implcN a (implcN b a)
  | 1, a, b, d => implcN (implcN a (implcN b d)) (implcN (implcN a b) (implcN a d))
  | 2, a, b, _ => implcN a (implcN b (andcN a b))
  | 3, a, b, _ => implcN (andcN a b) a
  | 4, a, b, _ => implcN (andcN a b) b
  | 5, a, b, _ => implcN a (orcN a b)
  | 6, a, b, _ => implcN b (orcN a b)
  | 7, a, b, d => implcN (orcN a b) (implcN (implcN a d) (implcN (implcN b d) d))
  | 8, a, _, _ => implcN botcN a
  | 9, a, b, _ => implcN (forallcN a) (substfcB 0 b a)
  | 10, a, b, _ => implcN (substfcB 0 b a) (excN a)
  | 11, a, b, _ => implcN (forallcN (implcN a (liftfcN 0 b))) (implcN (excN a) b)
  | 12, a, _, _ => eqcN a a
  | 13, a, b, d => implcN (eqcN b d) (implcN (substfcB 0 b a) (substfcB 0 d a))
  | 14, a, _, _ => implcN (implcN (implcN a botcN) botcN) a
  | 15, a, _, _ => a
  | 16, a, _, _ => a
  | 17, a, _, _ => forallcN a
  | 18, a, _, _ => implcN (substfcB 0 TC0 a)
      (implcN (forallcN (implcN a (substfcB 0 TCS (liftfcN 1 a)))) (forallcN a))
  | 19, a, b, _ => implcN (forallcN (implcN (liftfcN 0 a) b)) (implcN a (forallcN b))
  | 20, a, _, _ => implcN (substfcB 0 TNIL a)
      (implcN (forallcN (forallcN (implcN (liftfcN 1 a) (substfcB 0 TCONS (liftfcN 2 (liftfcN 1 a))))))
        (forallcN a))
  | _, _, _, _ => 0

def stepNB (x : Nat) : Nat := stepTB (nthN x 0) (nthN x 1) (nthN x 2) (nthN x 3)

def vpfLB : Nat → List Nat → Nat
  | c, [] => c
  | c, x :: r => vpfLB (concatN c (consN (stepNB x) 0)) r

def vpfNB (c r : Nat) : Nat := vpfLB c (decodeL r)

theorem vpfNB_zero (c : Nat) : vpfNB c 0 = c := by rw [vpfNB, decodeL_zero]; rfl

theorem vpfNB_consN (c x r : Nat) : vpfNB c (consN x r) = vpfNB (concatN c (consN (stepNB x) 0)) r := by
  rw [vpfNB, decodeL_consN]; rfl

/-! ## §3 · El modelo `MNB V`: `MNV V` con `substfcB` y `vpfNB` -/

def MNB (V : Nat) : Model Nat where
  func := fun s args =>
    if s = sym!"substfc" then
      (match args with
       | [k, t, f] => substfcB k t f
       | _ => 0)
    else if s = sym!"validProofFn" then
      (match args with
       | [c, r] => vpfNB c r
       | _ => 0)
    else (MNV V).func s args
  rel := (MNV V).rel

variable {V : Nat}

theorem MB_func {s : List Char} (h1 : (s != sym!"substfc") = true) (h2 : (s != sym!"validProofFn") = true)
    (args : List Nat) : (MNB V).func s args = (MNV V).func s args := by
  have e1 : ¬ s = sym!"substfc" := by simpa using h1
  have e2 : ¬ s = sym!"validProofFn" := by simpa using h2
  simp only [MNB, if_neg e1, if_neg e2]

theorem MB_substfc (k t f : Nat) : (MNB V).func sym!"substfc" [k, t, f] = substfcB k t f := rfl
theorem MB_vpf (c r : Nat) : (MNB V).func sym!"validProofFn" [c, r] = vpfNB c r := rfl
theorem MB_zero : (MNB V).func sym!"0" [] = 0 := (MB_func (by decide) (by decide) _).trans MN_zero
theorem MB_succ (a : Nat) : (MNB V).func sym!"σ" [a] = a + 1 := (MB_func (by decide) (by decide) _).trans (MN_succ a)
theorem MB_pred (a : Nat) : (MNB V).func sym!"τ" [a] = a - 1 := (MB_func (by decide) (by decide) _).trans (MN_pred a)
theorem MB_cons (a b : Nat) : (MNB V).func sym!"::" [a, b] = consN a b :=
  (MB_func (by decide) (by decide) _).trans (MN_cons a b)
theorem MB_concat (a b : Nat) : (MNB V).func sym!"##" [a, b] = concatN a b :=
  (MB_func (by decide) (by decide) _).trans (MN_concat a b)
theorem MB_substtc (k s c : Nat) : (MNB V).func sym!"substtc" [k, s, c] = substtcN k s c :=
  (MB_func (by decide) (by decide) _).trans (MN_substtc k s c)
theorem MB_substtsc (k s c : Nat) : (MNB V).func sym!"substtsc" [k, s, c] = substtscN k s c :=
  (MB_func (by decide) (by decide) _).trans (MN_substtsc k s c)
theorem MB_liftc (c t : Nat) : (MNB V).func sym!"liftc" [c, t] = liftcN c t :=
  (MB_func (by decide) (by decide) _).trans (MN_liftc c t)
theorem MB_liftsc (c t : Nat) : (MNB V).func sym!"liftsc" [c, t] = liftscN c t :=
  (MB_func (by decide) (by decide) _).trans (MN_liftsc c t)
theorem MB_liftfc (c f : Nat) : (MNB V).func sym!"liftfc" [c, f] = liftfcN c f :=
  (MB_func (by decide) (by decide) _).trans (MN_liftfc c f)
theorem MB_carc (l : Nat) : (MNB V).func sym!"carc" [l] = carN l := (MB_func (by decide) (by decide) _).trans (MN_carc l)
theorem MB_cdrc (l : Nat) : (MNB V).func sym!"cdrc" [l] = cdrN l := (MB_func (by decide) (by decide) _).trans (MN_cdrc l)
theorem MB_lenc (l : Nat) : (MNB V).func sym!"lenc" [l] = lenN l := (MB_func (by decide) (by decide) _).trans (MN_lenc l)
theorem MB_nthc (l i : Nat) : (MNB V).func sym!"nthc" [l, i] = nthN l i :=
  (MB_func (by decide) (by decide) _).trans (MN_nthc l i)
theorem MB_runFn (c r : Nat) : (MNB V).func sym!"runFn" [c, r] = runFnN c r :=
  (MB_func (by decide) (by decide) _).trans (MN_runFn c r)
theorem MB_tcFn (t : Nat) : (MNB V).func sym!"tcFn" [t] = tcFnN t := (MB_func (by decide) (by decide) _).trans (MN_tcFn t)
theorem MB_premsOf (l : Nat) : (MNB V).func sym!"premsOf" [l] = premsOfN l :=
  (MB_func (by decide) (by decide) _).trans (MN_premsOf l)
theorem MB_axiomsCodeT : (MNB V).func sym!"axiomsCodeT" [] = V :=
  (MB_func (by decide) (by decide) _).trans MN_axiomsCodeT
theorem MB_lt (a b : Nat) : (MNB V).rel sym!"<" [a, b] = (a < b) := MN_lt (V := V) a b
theorem MB_mem (x l : Nat) : (MNB V).rel sym!"∈" [x, l] = memN x l := MN_mem (V := V) x l
theorem MB_allIn (c l : Nat) : (MNB V).rel sym!"allIn" [c, l] = allInN c l := MN_allIn (V := V) c l
theorem MB_lineWF (l : Nat) : (MNB V).rel sym!"lineWF" [l] = lineWFN V l := MN_lineWF l
theorem MB_chainOk (c p : Nat) : (MNB V).rel sym!"chainOk" [c, p] = chainOkN V c p := MN_chainOk c p

/-- ⚠️ Los dos modelos son DISTINTOS: difieren en `substfc` sobre la basura `⟨10⟩`. -/
theorem MB_ne_MN : (MNB V).func sym!"substfc" [0, 0, consN 10 0] ≠ (MNV V).func sym!"substfc" [0, 0, consN 10 0] := by
  rw [MB_substfc, MN_substfc, substfcB_basura, substfcN_basura]
  exact consN_ne_zero _ _

/-! ## §4 · Donde no aparecen `substfc` ni `validProofFn`, los dos modelos evalúan IGUAL -/

mutual
def libreT : Term → Bool
  | .var _ => true
  | .func f ts => (f != sym!"substfc" && f != sym!"validProofFn") && libreTs ts
def libreTs : List Term → Bool
  | [] => true
  | t :: ts => libreT t && libreTs ts
end

def libreF : Formula → Bool
  | .bottom => true
  | .atom _ ts => libreTs ts
  | .eq a b => libreT a && libreT b
  | .impl a b => libreF a && libreF b
  | .forall a => libreF a
  | .and a b => libreF a && libreF b
  | .or a b => libreF a && libreF b
  | .ex a => libreF a

mutual
theorem agreeT (v : Nat → Nat) : ∀ t : Term, libreT t = true → evalTerm (MNB V) v t = evalTerm (MNV V) v t
  | .var _, _ => rfl
  | .func f ts, h => by
      simp only [libreT, Bool.and_eq_true] at h
      show (MNB V).func f (evalTerms (MNB V) v ts) = (MNV V).func f (evalTerms (MNV V) v ts)
      rw [agreeTs v ts h.2, MB_func h.1.1 h.1.2]
theorem agreeTs (v : Nat → Nat) : ∀ ts : List Term, libreTs ts = true →
    evalTerms (MNB V) v ts = evalTerms (MNV V) v ts
  | [], _ => rfl
  | t :: ts, h => by
      simp only [libreTs, Bool.and_eq_true] at h
      show evalTerm (MNB V) v t :: evalTerms (MNB V) v ts = evalTerm (MNV V) v t :: evalTerms (MNV V) v ts
      rw [agreeT v t h.1, agreeTs v ts h.2]
end

theorem agreeF : ∀ (φ : Formula) (v : Nat → Nat), libreF φ = true →
    (evalFormula (MNB V) v φ ↔ evalFormula (MNV V) v φ)
  | .bottom, _, _ => Iff.rfl
  | .atom p ts, v, h => by
      show (MNV V).rel p (evalTerms (MNB V) v ts) ↔ (MNV V).rel p (evalTerms (MNV V) v ts)
      rw [agreeTs v ts h]
  | .eq a b, v, h => by
      simp only [libreF, Bool.and_eq_true] at h
      show evalTerm (MNB V) v a = evalTerm (MNB V) v b ↔ evalTerm (MNV V) v a = evalTerm (MNV V) v b
      rw [agreeT v a h.1, agreeT v b h.2]
  | .impl a b, v, h => by
      simp only [libreF, Bool.and_eq_true] at h
      exact imp_congr (agreeF a v h.1) (agreeF b v h.2)
  | .forall a, v, h => forall_congr' fun d => agreeF a (shiftEnv v d) h
  | .and a b, v, h => by
      simp only [libreF, Bool.and_eq_true] at h
      exact and_congr (agreeF a v h.1) (agreeF b v h.2)
  | .or a b, v, h => by
      simp only [libreF, Bool.and_eq_true] at h
      exact or_congr (agreeF a v h.1) (agreeF b v h.2)
  | .ex a, v, h => exists_congr fun d => agreeF a (shiftEnv v d) h

/-- Lo validado en `MNV V` sin `substfc` ni `validProofFn` vale en `MNB V`. -/
theorem lib {φ : Formula} (h : libreF φ = true) {v : Nat → Nat} (hv : evalFormula (MNV V) v φ) :
    evalFormula (MNB V) v φ :=
  (agreeF φ v h).2 hv

/-! ## §5 · Los códigos cerrados y las guardas, en `MNB V` -/

theorem libre_numeralM : ∀ n : Nat, libreT (numeralM n) = true
  | 0 => rfl
  | n + 1 => by
      show libreT (Term.func succ_sym [numeralM n]) = true
      simp only [libreT, libreTs, libre_numeralM n]; decide

theorem libre_charsCodeM : ∀ cs : List Char, libreT (charsCodeM cs) = true
  | [] => rfl
  | c :: cs => by
      show libreT (Term.func cons_sym [numeralM c.toNat, charsCodeM cs]) = true
      simp only [libreT, libreTs, libre_numeralM, libre_charsCodeM cs]; decide

mutual
theorem libre_termCodeM : ∀ t : Term, libreT (termCodeM t) = true
  | .var n => by
      show libreT (Term.func cons_sym [numeralM 0, Term.func cons_sym [numeralM n, Term.func zero_sym []]]) = true
      simp only [libreT, libreTs, libre_numeralM]; decide
  | .func s ts => by
      show libreT (Term.func cons_sym [numeralM 1, Term.func cons_sym [strCodeM s,
        Term.func cons_sym [termsCodeM ts, Term.func zero_sym []]]]) = true
      simp only [libreT, libreTs, libre_numeralM, strCodeM, libre_charsCodeM, libre_termsCodeM ts]; decide
theorem libre_termsCodeM : ∀ ts : List Term, libreT (termsCodeM ts) = true
  | [] => rfl
  | t :: ts => by
      show libreT (Term.func cons_sym [termCodeM t, termsCodeM ts]) = true
      simp only [libreT, libreTs, libre_termCodeM t, libre_termsCodeM ts]; decide
end

theorem evB_numeralM (v : Nat → Nat) (n : Nat) : evalTerm (MNB V) v (numeralM n) = n :=
  (agreeT v _ (libre_numeralM n)).trans (ev_numeralM v n)
theorem evB_strCodeM (v : Nat → Nat) (s : List Char) : evalTerm (MNB V) v (strCodeM s) = codeNatStr s :=
  (agreeT v _ (libre_charsCodeM s)).trans (ev_strCodeM v s)
theorem evB_termCodeM (v : Nat → Nat) (t : Term) : evalTerm (MNB V) v (termCodeM t) = codeNatTerm t :=
  (agreeT v _ (libre_termCodeM t)).trans (ev_termCodeM v t)

theorem evB_lift0 (v : Nat → Nat) (d : Nat) (t : Term) :
    evalTerm (MNB V) (shiftEnv v d) (liftTerm 0 t) = evalTerm (MNB V) v t := by
  have h := eval_liftTerm_ext (MNB V) v d 0 t
  have heq : updateEnv 0 v d = shiftEnv v d := by funext n; exact updateEnv_zero v d n
  rw [heq] at h; exact h

theorem evB_hasWit (v : Nat → Nat) (t : Term) : evalFormula (MNB V) v (hasWit t) ↔ hasWitN (evalTerm (MNB V) v t) := by
  simp only [hasWit, isTC1, wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, argsIn, argsInBody,
    land, lor, lt, In, lenc, nthc, cons, nil, zero, lt_sym, in_sym, cons_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, liftTerm, liftTerms, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, evB_lift0, evB_numeralM,
    MB_lt, MB_mem, MB_lenc, MB_nthc, MB_cons, MB_zero,
    hasWitN, wfAll1N, isTermCodeE1N, shapeUnN, shapeBinN, argsInN]

theorem evB_hasWitF (v : Nat → Nat) (t : Term) : evalFormula (MNB V) v (hasWitF t) ↔ hasWitFN (evalTerm (MNB V) v t) := by
  simp only [hasWitF, isFC1, wfAll1, wfAll1Body, isTermCodeE1, shapeUn, shapeBin, shapeNul, argsIn, argsInBody,
    wfAllF, wfAllFBody, isFormCodeE2, lorAll, clBot, clAtom, clEq, clBin, clUn,
    land, lor, lt, In, lenc, nthc, cons, nil, zero, lt_sym, in_sym, cons_sym, zero_sym,
    evalFormula, evalTerm, evalTerms, shiftEnv, liftTerm, liftTerms, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add,
    ROBINSON_PlusPlus.Minimal.Axioms.liftTerm_numeralM, evB_lift0, evB_numeralM,
    MB_lt, MB_mem, MB_lenc, MB_nthc, MB_cons, MB_zero,
    hasWitFN, wfAll1N, wfAllFN, isTermCodeE1N, isFormCodeE2N, shapeUnN, shapeBinN, argsInN,
    clBotN, clAtomN, clEqN, clBinN, clUnN]

local macro "abreB" : tactic => `(tactic| simp only [forall_, forall_2, forall_3, forall_4, forall_5, _root_.iff,
    land, lor, cons, nil, zero, succ, pred, concat, lt, In, cons_sym, zero_sym, succ_sym, pred_sym,
    concat_sym, lt_sym, in_sym, substtc, substtsc, liftc, liftsc, substfc, liftfc, carc, cdrc, lenc, nthc,
    runFn, validProofFn, tcFn, premsOf, allIn, lineWF, chainOk, lineOk, varc, funcc, botc, atomc, eqc,
    implc, forallc, andc, orc, exc, axiomsCodeT, lineTag, tagDisj,
    evalFormula, evalTerm, evalTerms, shiftEnv, evB_numeralM, evB_strCodeM, evB_termCodeM, evB_hasWit, evB_hasWitF,
    MB_zero, MB_succ, MB_pred, MB_cons, MB_concat, MB_substtc, MB_substtsc, MB_liftc, MB_liftsc, MB_substfc,
    MB_liftfc, MB_carc, MB_cdrc, MB_lenc, MB_nthc, MB_runFn, MB_vpf, MB_tcFn, MB_premsOf, MB_axiomsCodeT,
    MB_lt, MB_mem, MB_allIn, MB_lineWF, MB_chainOk])

/-! ## §6 · Los 35 que nombran `substfc` o `validProofFn` -/

theorem vB_substfc_bottom : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_substfc_bottom := by
  intro v x t; abreB; exact substfcB_bot x t
theorem vB_substfc_atom : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_substfc_atom := by
  intro v x t a b; abreB; exact substfcB_atom x t a b
theorem vB_substfc_eq : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_substfc_eq := by
  intro v x t a b; abreB; exact substfcB_eq x t a b
theorem vB_substfc_impl : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_substfc_impl := by
  intro v x t a b; abreB; exact substfcB_impl x t a b
theorem vB_substfc_forall : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_substfc_forall := by
  intro v x t a; abreB; exact substfcB_forall x t a
theorem vB_substfc_and : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_substfc_and := by
  intro v x t a b; abreB; exact substfcB_and x t a b
theorem vB_substfc_or : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_substfc_or := by
  intro v x t a b; abreB; exact substfcB_or x t a b
theorem vB_substfc_ex : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_substfc_ex := by
  intro v x t a; abreB; exact substfcB_ex x t a

local macro "vpf_pasoB" : tactic => `(tactic| (rw [vpfNB_consN]; simp only [stepNB, nthN_cz, nthN_cs, nthN_zero_l, stepTB]))

theorem vB_vpf_nil : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_nil := by
  intro v c; abreB; exact vpfNB_zero c
theorem vB_vpf_p1 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_p1 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_p2 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_p2 := by
  intro v c a b d r; abreB; vpf_pasoB
theorem vB_vpf_c1 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_c1 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_c2 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_c2 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_c3 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_c3 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_j1 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_j1 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_j2 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_j2 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_j3 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_j3 := by
  intro v c a b d r; abreB; vpf_pasoB
theorem vB_vpf_efq : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_efq := by
  intro v c a r; abreB; vpf_pasoB
theorem vB_vpf_q1 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_q1 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_q2 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_q2 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_q3 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_q3 := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_eqrefl : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_eqrefl := by
  intro v c a r; abreB; vpf_pasoB
theorem vB_vpf_leibniz : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_leibniz := by
  intro v c a b d r; abreB; vpf_pasoB
theorem vB_vpf_p3 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_p3 := by
  intro v c a r; abreB; vpf_pasoB
theorem vB_vpf_mp : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_mp := by
  intro v c b a r; abreB; intro _ _; vpf_pasoB
theorem vB_vpf_gen : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_gen := by
  intro v c a r; abreB; intro _; vpf_pasoB
theorem vB_vpf_thy : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_thy := by
  intro v c a r; abreB; intro _; vpf_pasoB
theorem vB_vpf_ind : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_ind := by
  intro v c a r; abreB; vpf_pasoB; rfl
theorem vB_vpf_qconf : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_qconf := by
  intro v c a b r; abreB; vpf_pasoB
theorem vB_vpf_listInd : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_vpf_listInd := by
  intro v c a r; abreB; vpf_pasoB; rfl

theorem vB_lineWF_q1 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_lineWF_q1 := by
  intro v x; abreB; intro h
  rw [lineWFN_of_tag h (by decide)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, by rw [substfcB_g h2]; exact h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, by rw [substfcB_g h2] at h4; exact h4⟩

theorem vB_lineWF_q2 : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_lineWF_q2 := by
  intro v x; abreB; intro h
  rw [lineWFN_of_tag h (by decide)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, by simp only [substfcB_g h2]; exact h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, by simp only [substfcB_g h2] at h4; exact h4⟩
theorem vB_lineWF_leibniz : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_lineWF_leibniz := by
  intro v x; abreB; intro h
  rw [lineWFN_of_tag h (by decide)]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, by simp only [substfcB_g h2]; exact h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, by simp only [substfcB_g h2] at h5; exact h5⟩
theorem vB_lineWF_ind : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_lineWF_ind := by
  intro v x; abreB; intro h
  rw [lineWFN_of_tag h (by decide)]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by
      simp only [substfcB_g h2, substfcB_codF (codF_liftfcN (codF_of_hasWitFN h2) 1)]; exact h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by
      simp only [substfcB_g h2, substfcB_codF (codF_liftfcN (codF_of_hasWitFN h2) 1)] at h3; exact h3⟩
theorem vB_lineWF_listInd : ∀ v : Nat → Nat, evalFormula (MNB V) v ax_lineWF_listInd := by
  intro v x; abreB; intro h
  rw [lineWFN_of_tag h (by decide)]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by
      simp only [substfcB_g h2,
        substfcB_codF (codF_liftfcN (codF_liftfcN (codF_of_hasWitFN h2) 1) 2)]; exact h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by
      simp only [substfcB_g h2,
        substfcB_codF (codF_liftfcN (codF_liftfcN (codF_of_hasWitFN h2) 1) 2)] at h3; exact h3⟩

/-! ## §7 · El ancla -/

theorem libre_formCodeM : ∀ φ : Formula, libreT (formCodeM φ) = true
  | .bottom => by
      show libreT (Term.func cons_sym [numeralM 2, Term.func zero_sym []]) = true
      simp only [libreT, libreTs, libre_numeralM]; decide
  | .atom p ts => by
      show libreT (Term.func cons_sym [numeralM 3, Term.func cons_sym [strCodeM p,
        Term.func cons_sym [termsCodeM ts, Term.func zero_sym []]]]) = true
      simp only [libreT, libreTs, libre_numeralM, strCodeM, libre_charsCodeM, libre_termsCodeM]; decide
  | .eq t u => by
      show libreT (Term.func cons_sym [numeralM 4, Term.func cons_sym [termCodeM t,
        Term.func cons_sym [termCodeM u, Term.func zero_sym []]]]) = true
      simp only [libreT, libreTs, libre_numeralM, libre_termCodeM]; decide
  | .impl a b => by
      show libreT (Term.func cons_sym [numeralM 5, Term.func cons_sym [formCodeM a,
        Term.func cons_sym [formCodeM b, Term.func zero_sym []]]]) = true
      simp only [libreT, libreTs, libre_numeralM, libre_formCodeM a, libre_formCodeM b]; decide
  | Formula.forall a => by
      show libreT (Term.func cons_sym [numeralM 6, Term.func cons_sym [formCodeM a, Term.func zero_sym []]]) = true
      simp only [libreT, libreTs, libre_numeralM, libre_formCodeM a]; decide
  | .and a b => by
      show libreT (Term.func cons_sym [numeralM 7, Term.func cons_sym [formCodeM a,
        Term.func cons_sym [formCodeM b, Term.func zero_sym []]]]) = true
      simp only [libreT, libreTs, libre_numeralM, libre_formCodeM a, libre_formCodeM b]; decide
  | .or a b => by
      show libreT (Term.func cons_sym [numeralM 8, Term.func cons_sym [formCodeM a,
        Term.func cons_sym [formCodeM b, Term.func zero_sym []]]]) = true
      simp only [libreT, libreTs, libre_numeralM, libre_formCodeM a, libre_formCodeM b]; decide
  | .ex a => by
      show libreT (Term.func cons_sym [numeralM 9, Term.func cons_sym [formCodeM a, Term.func zero_sym []]]) = true
      simp only [libreT, libreTs, libre_numeralM, libre_formCodeM a]; decide

theorem libre_listFormCodeM : ∀ L : List Formula, libreT (listFormCodeM L) = true
  | [] => rfl
  | f :: fs => by
      show libreT (Term.func cons_sym [formCodeM f, listFormCodeM fs]) = true
      simp only [libreT, libreTs, libre_formCodeM f, libre_listFormCodeM fs]; decide

theorem evB_listFormCodeM (v : Nat → Nat) (L : List Formula) :
    evalTerm (MNB V) v (listFormCodeM L) = codeNatList L :=
  (agreeT v _ (libre_listFormCodeM L)).trans (ev_listFormCodeM v L)

theorem evB_concat (v : Nat → Nat) (a b : Term) :
    evalTerm (MNB V) v (concat a b) = concatN (evalTerm (MNB V) v a) (evalTerm (MNB V) v b) := MB_concat _ _
theorem evB_cons (v : Nat → Nat) (a b : Term) :
    evalTerm (MNB V) v (cons a b) = consN (evalTerm (MNB V) v a) (evalTerm (MNB V) v b) := MB_cons _ _
theorem evB_nil (v : Nat → Nat) : evalTerm (MNB V) v nil = 0 := MB_zero
theorem evB_zero (v : Nat → Nat) : evalTerm (MNB V) v zero = 0 := MB_zero
theorem evB_substfc (v : Nat → Nat) (a b c : Term) :
    evalTerm (MNB V) v (substfc a b c) =
      substfcB (evalTerm (MNB V) v a) (evalTerm (MNB V) v b) (evalTerm (MNB V) v c) := rfl
theorem evB_tcFn (v : Nat → Nat) (a : Term) : evalTerm (MNB V) v (tcFn a) = tcFnN (evalTerm (MNB V) v a) := MB_tcFn _
theorem evB_axiomsCodeT (v : Nat → Nat) : evalTerm (MNB V) v axiomsCodeT = V := MB_axiomsCodeT

theorem vB_ancla : ∀ v : Nat → Nat, evalFormula (MNB V₀) v ax_axiomsCodeT_def := by
  intro v
  rw [ax_axiomsCodeT_def, axD]
  show evalTerm (MNB V₀) v axiomsCodeT =
    evalTerm (MNB V₀) v (concat (listFormCodeM axiomsBase) (cons (deltaD axiomsBase) nil))
  rw [evB_axiomsCodeT, evB_concat, evB_cons, evB_nil, evB_listFormCodeM, deltaD, evB_substfc, evB_zero, evB_tcFn, nD,
    evB_numeralM, substfcB_codF (codF_codeNat _)]
  exact V₀_def

/-! ## §8 · LOS 142 en `MNB V₀`, y `Estandar`

Los 34 de la teoría y los 72 de codificación que no nombran `substfc` ni `validProofFn`, por `lib` sobre su
validación en `MNV V` (`libreF`, por `decide +kernel`); los 35 que sí, por §6; el ancla, por §7. -/

theorem MB_coreAxioms (v : Nat → Nat) : ∀ φ, List.Mem φ coreAxioms → evalFormula (MNB V) v φ := by
  unfold coreAxioms
  exact mem_cons_elim (lib (by decide +kernel) (v_ax2 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax3 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax4 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax5 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax6 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax7 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax8 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax9 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax10 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax11 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax12 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax13 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax14 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax15 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax16 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax17 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax18 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax19 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax21 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax24 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax25 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax26 v)) (mem_cons_elim (lib (by decide +kernel) (v_axL0 v)) (mem_cons_elim (lib (by decide +kernel) (v_axL1 v)) (mem_cons_elim (lib (by decide +kernel) (v_axL2 v)) (mem_cons_elim (lib (by decide +kernel) (v_axC1 v)) (mem_cons_elim (lib (by decide +kernel) (v_axC2 v)) (mem_cons_elim (lib (by decide +kernel) (v_axC3 v)) (mem_cons_elim (lib (by decide +kernel) (v_axL3 v)) (mem_cons_elim (lib (by decide +kernel) (v_ax29 v)) (mem_cons_elim (lib (by decide +kernel) (v_pow_zero v)) (mem_cons_elim (lib (by decide +kernel) (v_pow_succ v)) (mem_cons_elim (lib (by decide +kernel) (v_prodp_nil v)) (mem_cons_elim (lib (by decide +kernel) (v_prodp_cons v)) (mem_nil_elim))))))))))))))))))))))))))))))))))

theorem MB_codingAxioms (v : Nat → Nat) : ∀ φ, List.Mem φ codingAxioms → evalFormula (MNB V) v φ := by
  unfold codingAxioms
  exact mem_cons_elim (lib (by decide +kernel) (v_substtc_var_eq v)) (mem_cons_elim (lib (by decide +kernel) (v_substtc_var_gt v)) (mem_cons_elim (lib (by decide +kernel) (v_substtc_var_lt v)) (mem_cons_elim (lib (by decide +kernel) (v_substtc_func v)) (mem_cons_elim (lib (by decide +kernel) (v_substtsc_nil v)) (mem_cons_elim (lib (by decide +kernel) (v_substtsc_cons v)) (mem_cons_elim (lib (by decide +kernel) (v_liftc_var_lt v)) (mem_cons_elim (lib (by decide +kernel) (v_liftc_var_ge v)) (mem_cons_elim (lib (by decide +kernel) (v_liftc_func v)) (mem_cons_elim (lib (by decide +kernel) (v_liftsc_nil v)) (mem_cons_elim (lib (by decide +kernel) (v_liftsc_cons v)) (mem_cons_elim (vB_substfc_bottom v) (mem_cons_elim (vB_substfc_atom v) (mem_cons_elim (vB_substfc_eq v) (mem_cons_elim (vB_substfc_impl v) (mem_cons_elim (vB_substfc_forall v) (mem_cons_elim (vB_substfc_and v) (mem_cons_elim (vB_substfc_or v) (mem_cons_elim (vB_substfc_ex v) (mem_cons_elim (lib (by decide +kernel) (v_liftfc_bottom v)) (mem_cons_elim (lib (by decide +kernel) (v_liftfc_atom v)) (mem_cons_elim (lib (by decide +kernel) (v_liftfc_eq v)) (mem_cons_elim (lib (by decide +kernel) (v_liftfc_impl v)) (mem_cons_elim (lib (by decide +kernel) (v_liftfc_forall v)) (mem_cons_elim (lib (by decide +kernel) (v_liftfc_and v)) (mem_cons_elim (lib (by decide +kernel) (v_liftfc_or v)) (mem_cons_elim (lib (by decide +kernel) (v_liftfc_ex v)) (mem_cons_elim (lib (by decide +kernel) (v_carc v)) (mem_cons_elim (lib (by decide +kernel) (v_cdrc v)) (mem_cons_elim (vB_vpf_nil v) (mem_cons_elim (vB_vpf_p1 v) (mem_cons_elim (vB_vpf_p2 v) (mem_cons_elim (vB_vpf_c1 v) (mem_cons_elim (vB_vpf_c2 v) (mem_cons_elim (vB_vpf_c3 v) (mem_cons_elim (vB_vpf_j1 v) (mem_cons_elim (vB_vpf_j2 v) (mem_cons_elim (vB_vpf_j3 v) (mem_cons_elim (vB_vpf_efq v) (mem_cons_elim (vB_vpf_q1 v) (mem_cons_elim (vB_vpf_q2 v) (mem_cons_elim (vB_vpf_q3 v) (mem_cons_elim (vB_vpf_eqrefl v) (mem_cons_elim (vB_vpf_leibniz v) (mem_cons_elim (vB_vpf_p3 v) (mem_cons_elim (vB_vpf_mp v) (mem_cons_elim (vB_vpf_gen v) (mem_cons_elim (vB_vpf_thy v) (mem_cons_elim (vB_vpf_ind v) (mem_cons_elim (vB_vpf_qconf v) (mem_cons_elim (vB_vpf_listInd v) (mem_cons_elim (lib (by decide +kernel) (v_tc_zero v)) (mem_cons_elim (lib (by decide +kernel) (v_tc_succ v)) (mem_cons_elim (lib (by decide +kernel) (v_runFn_nil v)) (mem_cons_elim (lib (by decide +kernel) (v_runFn_cons v)) (mem_cons_elim (lib (by decide +kernel) (v_allIn_nil v)) (mem_cons_elim (lib (by decide +kernel) (v_allIn_cons v)) (mem_cons_elim (lib (by decide +kernel) (v_chainOk_nil v)) (mem_cons_elim (lib (by decide +kernel) (v_chainOk_cons v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_mp v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_mp v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_gen v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_gen v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_thy v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_thy v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_p1 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_p1 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_p2 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_p2 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_c1 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_c1 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_c2 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_c2 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_c3 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_c3 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_j1 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_j1 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_j2 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_j2 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_j3 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_j3 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_efq v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_efq v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_eqrefl v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_eqrefl v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_p3 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_p3 v)) (mem_cons_elim (vB_lineWF_q1 v) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_q1 v)) (mem_cons_elim (vB_lineWF_q2 v) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_q2 v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_q3 v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_q3 v)) (mem_cons_elim (vB_lineWF_leibniz v) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_leibniz v)) (mem_cons_elim (vB_lineWF_ind v) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_ind v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_qconf v)) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_qconf v)) (mem_cons_elim (vB_lineWF_listInd v) (mem_cons_elim (lib (by decide +kernel) (v_premsOf_listInd v)) (mem_cons_elim (lib (by decide +kernel) (v_lenc_nil v)) (mem_cons_elim (lib (by decide +kernel) (v_lenc_cons v)) (mem_cons_elim (lib (by decide +kernel) (v_nthc_zero v)) (mem_cons_elim (lib (by decide +kernel) (v_nthc_succ v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_inv v)) (mem_cons_elim (lib (by decide +kernel) (v_lineWF_cons v)) (mem_nil_elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem MB_axioms (v : Nat → Nat) : contextSatisfies (MNB V₀) v axioms := by
  intro φ hφ
  rw [axioms_split] at hφ
  cases List.mem_append.mp hφ with
  | inl h =>
    cases List.mem_append.mp h with
    | inl h1 => exact MB_coreAxioms v φ h1
    | inr h2 => exact MB_codingAxioms v φ h2
  | inr h =>
    have e : φ = ax_axiomsCodeT_def := List.mem_singleton.mp h
    rw [e]; exact vB_ancla v

/-- `MNB V₀` es estándar: `0`, `σ` y `::` los de `MNV`, y los 142. -/
theorem estandar_MB : Estandar (MNB V₀) where
  hzero := MB_zero
  hsucc := MB_succ
  hcons := MB_cons
  haxs := MB_axioms

theorem MNB_ne_MNV : MNB V₀ ≠ MNV V₀ := fun h => MB_ne_MN (by rw [h])

/-- 🏁 **Hay DOS modelos estándar distintos**: `Estandar` no fija el modelo; sobre la basura de `substfc`, `M` es
    libre. -/
theorem segundo_modelo : And (Estandar (MNB V₀)) (MNB V₀ ≠ MNV V₀) := ⟨estandar_MB, MNB_ne_MNV⟩

/-- Y `Prov` es fiel también en él: `modelo_prov_iff_de` (T75e) en una instancia que NO es `MNV V₀`. -/
theorem modelo_prov_iff_MB (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNB V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) ↔ Prf φ :=
  ROBINSON_PlusPlus.Meta.RigidezEstandar.modelo_prov_iff_de estandar_MB φ v

end ROBINSON_PlusPlus.Meta.SegundoModelo

#print axioms ROBINSON_PlusPlus.Meta.SegundoModelo.substfcB_codF
#print axioms ROBINSON_PlusPlus.Meta.SegundoModelo.agreeF
#print axioms ROBINSON_PlusPlus.Meta.SegundoModelo.vB_ancla
#print axioms ROBINSON_PlusPlus.Meta.SegundoModelo.estandar_MB
#print axioms ROBINSON_PlusPlus.Meta.SegundoModelo.segundo_modelo
#print axioms ROBINSON_PlusPlus.Meta.SegundoModelo.modelo_prov_iff_MB
