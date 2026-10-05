/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Consistencia
import ROBINSON_PlusPlus.Meta.Representability

/-!
# `Meta/SolidezVerificador.lean` — 🏁🏁 W1, y Gödel I ENTERO: `⊬ G` y `⊬ ¬G`, sin hipótesis (ADR‑121)

**W1** (`verificador_solido`): si el modelo estándar `MNV V₀` cree que una cadena `p` es una prueba —`chainOkN V₀ 0
p`—, todo lo que esa cadena concluye, DECODIFICADO, es teorema de `Prf`. Con él, **`goedel_I_neg : ¬ Prf ¬G`**: con
`Prf ¬G`, la solidez y el punto fijo harían creer al modelo que `G` es demostrable, W1 daría `Prf G`, y `goedel_I`
lo impide. Es la mitad de Gödel I que faltaba desde ADR‑115, y `godelCN_indecidible` junta las dos. Sale de la
solidez de `Prf` en el modelo estándar (aplicada también a fórmulas que no son Σ₁) y de `goedel_I`: no de la
ω‑consistencia ni de Rosser.

* **§1 · El decodificador TOTAL** (`decS`, `decT`/`decTs`, `dec`): todo número se DECODIFICA a un término y a una
  fórmula —las ramas por defecto (`dflt`, `⊥`) lo hacen total—, y `dec` espeja EXACTAMENTE el análisis de casos de `substtcN`/`substfcN` —la etiqueta `nthN c 0`
  decide, y la forma que no es de nadie va a una constante cerrada (`dflt`) o a `⊥`—. Así no hace falta saber qué
  números son códigos «de verdad»: la basura entra y sale decodificada a algo, y eso basta.
* **§2 · Sobre los códigos de verdad es el inverso**: `dec_codeNat : dec (codeNat φ) = φ`.
* **§3 · La sustitución y el lift CONMUTAN con él, para TODO número** (`dec_substfc`, `dec_liftfc`, y los de
  término), por inducción fuerte sobre el número.
* **§4 · W1**: cada una de las 21 reglas, decodificada, es una instancia de un constructor de `Prf` (`linea_*`); la
  regla `thy` pide `V₀_eq_codigo` (en el modelo, `axiomsCodeT` es el código de los 142), y `mp`/`gen` el invariante
  de la cadena (`Bueno`: todo lo acumulado es teorema).
* **§5 · `⊬ ¬G`**, y `modelo_prov_iff`: `MNV V₀ ⊨ Prov(⌜φ⌝) ↔ Prf φ` —la ida es W1, la vuelta D1 y la solidez—,
  que es también el control de vacuidad de W1.
* **§6 · E10**: `godelCN_verdadera` y `con_verdadera` — `G` y `Con` son VERDADERAS en `MNV V₀` (y no demostrables).

⚠️ Lo que NO dice: nada de Rosser (`⊬R ∧ ⊬¬R` sólo con `ConsistentH`, ⬜): aquí la hipótesis es más fuerte —el
modelo estándar, que es un TEOREMA (ADR‑120)—, y la sentencia es la de Gödel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FOL FOL.Metamath.Semantics ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ModeloCodigo ROBINSON_PlusPlus.Meta.CodeNatInjPrf

namespace ROBINSON_PlusPlus.Meta.SolidezVerificador

/-! ## §1 · El DECODIFICADOR total: todo número es el código de un término o de una fórmula

Espeja EXACTAMENTE el análisis de casos de `substtcN`/`substfcN`: la etiqueta `nthN c 0` decide, y la forma que no
es de nadie va a una constante cerrada (`dflt`) o a `⊥`. Así la sustitución CONMUTA con la decodificación para TODO
número, basura incluida, y no hace falta saber qué números son códigos de verdad. -/

def decS (n : Nat) : List Char := (decodeL n).map Char.ofNat

def dflt : Term := Term.func sym!"" []

mutual
def decT (c : Nat) : Term :=
  if _h : c = 0 then dflt
  else if nthN c 0 = 0 then Term.var (nthN c 1)
  else if nthN c 0 = 1 then Term.func (decS (nthN c 1)) (decTs (nthN c 2))
  else dflt
termination_by c
decreasing_by exact nthN_lt 2 _h

def decTs (l : Nat) : List Term :=
  if _h : l = 0 then [] else decT (carN l) :: decTs (cdrN l)
termination_by l
decreasing_by
  · exact carN_lt _h
  · exact cdrN_lt _h
end

def dec (f : Nat) : Formula :=
  if _h : f = 0 then Formula.bottom
  else if nthN f 0 = 2 then Formula.bottom
  else if nthN f 0 = 3 then Formula.atom (decS (nthN f 1)) (decTs (nthN f 2))
  else if nthN f 0 = 4 then Formula.eq (decT (nthN f 1)) (decT (nthN f 2))
  else if nthN f 0 = 5 then Formula.impl (dec (nthN f 1)) (dec (nthN f 2))
  else if nthN f 0 = 6 then Formula.forall (dec (nthN f 1))
  else if nthN f 0 = 7 then Formula.and (dec (nthN f 1)) (dec (nthN f 2))
  else if nthN f 0 = 8 then Formula.or (dec (nthN f 1)) (dec (nthN f 2))
  else if nthN f 0 = 9 then Formula.ex (dec (nthN f 1))
  else Formula.bottom
termination_by f
decreasing_by all_goals exact nthN_lt _ _h

/-! ### Las ecuaciones, una por forma -/

theorem decT_unfold (c : Nat) : decT c =
    if _h : c = 0 then dflt else if nthN c 0 = 0 then Term.var (nthN c 1)
    else if nthN c 0 = 1 then Term.func (decS (nthN c 1)) (decTs (nthN c 2)) else dflt := by
  rw [decT]

theorem decTs_unfold (l : Nat) : decTs l = if _h : l = 0 then [] else decT (carN l) :: decTs (cdrN l) := by
  rw [decTs]

theorem decT_zero : decT 0 = dflt := by rw [decT_unfold, dif_pos rfl]

theorem decT_var (n r : Nat) : decT (consN 0 (consN n r)) = Term.var n := by
  rw [decT_unfold, dif_neg (consN_ne_zero _ _), nthN_cz, if_pos rfl, nthN_cs, nthN_cz]

theorem decT_func (s ts r : Nat) : decT (consN 1 (consN s (consN ts r))) = Term.func (decS s) (decTs ts) := by
  rw [decT_unfold, dif_neg (consN_ne_zero _ _), nthN_cz, if_neg (by decide), if_pos rfl,
    nthN_cs, nthN_cz, nthN_cs, nthN_cs, nthN_cz]

theorem decTs_zero : decTs 0 = [] := by rw [decTs_unfold, dif_pos rfl]

theorem decTs_consN (a b : Nat) : decTs (consN a b) = decT a :: decTs b := by
  rw [decTs_unfold, dif_neg (consN_ne_zero _ _), carN_consN, cdrN_consN]

theorem dec_unfold (f : Nat) : dec f =
    if _h : f = 0 then Formula.bottom
    else if nthN f 0 = 2 then Formula.bottom
    else if nthN f 0 = 3 then Formula.atom (decS (nthN f 1)) (decTs (nthN f 2))
    else if nthN f 0 = 4 then Formula.eq (decT (nthN f 1)) (decT (nthN f 2))
    else if nthN f 0 = 5 then Formula.impl (dec (nthN f 1)) (dec (nthN f 2))
    else if nthN f 0 = 6 then Formula.forall (dec (nthN f 1))
    else if nthN f 0 = 7 then Formula.and (dec (nthN f 1)) (dec (nthN f 2))
    else if nthN f 0 = 8 then Formula.or (dec (nthN f 1)) (dec (nthN f 2))
    else if nthN f 0 = 9 then Formula.ex (dec (nthN f 1))
    else Formula.bottom := by
  rw [dec]

theorem dec_zero : dec 0 = Formula.bottom := by rw [dec_unfold, dif_pos rfl]

theorem dec_bot (r : Nat) : dec (consN 2 r) = Formula.bottom := by
  rw [dec_unfold]; simp only [consN_ne_zero, nthN_cz, dite_false]; rfl

theorem dec_atom (p ts r : Nat) : dec (consN 3 (consN p (consN ts r))) = Formula.atom (decS p) (decTs ts) := by
  rw [dec_unfold]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem dec_eq (a b r : Nat) : dec (consN 4 (consN a (consN b r))) = Formula.eq (decT a) (decT b) := by
  rw [dec_unfold]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem dec_impl (a b r : Nat) : dec (consN 5 (consN a (consN b r))) = Formula.impl (dec a) (dec b) := by
  rw [dec_unfold]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem dec_forall (a r : Nat) : dec (consN 6 (consN a r)) = Formula.forall (dec a) := by
  rw [dec_unfold]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem dec_and (a b r : Nat) : dec (consN 7 (consN a (consN b r))) = Formula.and (dec a) (dec b) := by
  rw [dec_unfold]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem dec_or (a b r : Nat) : dec (consN 8 (consN a (consN b r))) = Formula.or (dec a) (dec b) := by
  rw [dec_unfold]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

theorem dec_ex (a r : Nat) : dec (consN 9 (consN a r)) = Formula.ex (dec a) := by
  rw [dec_unfold]; simp only [consN_ne_zero, nthN_cz, nthN_cs, dite_false]; rfl

/-! ## §2 · Sobre los códigos de VERDAD, el decodificador es el inverso -/

theorem decodeL_codeNatChars : ∀ cs : List Char, decodeL (codeNatChars cs) = cs.map Char.toNat
  | [] => decodeL_zero
  | c :: cs => by rw [codeNatChars, decodeL_consN, decodeL_codeNatChars cs]; rfl

theorem decS_codeNatStr (s : List Char) : decS (codeNatStr s) = s := by
  rw [decS, codeNatStr, decodeL_codeNatChars, List.map_map]
  have e : (Char.ofNat ∘ Char.toNat) = id := funext (fun c => Char.ofNat_toNat c)
  rw [e, List.map_id]

mutual
theorem decT_codeNatTerm (t : Term) : decT (codeNatTerm t) = t := by
  match t with
  | .var n =>
    show decT (consN 0 (consN n 0)) = Term.var n
    rw [decT_var]
  | .func s ts =>
    show decT (consN 1 (consN (codeNatStr s) (consN (codeNatTerms ts) 0))) = Term.func s ts
    rw [decT_func, decS_codeNatStr, decTs_codeNatTerms ts]
theorem decTs_codeNatTerms (ts : List Term) : decTs (codeNatTerms ts) = ts := by
  match ts with
  | [] => exact decTs_zero
  | t :: ts' =>
    show decTs (consN (codeNatTerm t) (codeNatTerms ts')) = t :: ts'
    rw [decTs_consN, decT_codeNatTerm t, decTs_codeNatTerms ts']
end

theorem dec_codeNat : ∀ φ : Formula, dec (codeNat φ) = φ
  | .bottom => dec_bot 0
  | .atom p ts => by
      show dec (consN 3 (consN (codeNatStr p) (consN (codeNatTerms ts) 0))) = _
      rw [dec_atom, decS_codeNatStr, decTs_codeNatTerms]
  | .eq t u => by
      show dec (consN 4 (consN (codeNatTerm t) (consN (codeNatTerm u) 0))) = _
      rw [dec_eq, decT_codeNatTerm, decT_codeNatTerm]
  | .impl a b => by
      show dec (consN 5 (consN (codeNat a) (consN (codeNat b) 0))) = _
      rw [dec_impl, dec_codeNat a, dec_codeNat b]
  | Formula.forall a => by
      show dec (consN 6 (consN (codeNat a) 0)) = _
      rw [dec_forall, dec_codeNat a]
  | .and a b => by
      show dec (consN 7 (consN (codeNat a) (consN (codeNat b) 0))) = _
      rw [dec_and, dec_codeNat a, dec_codeNat b]
  | .or a b => by
      show dec (consN 8 (consN (codeNat a) (consN (codeNat b) 0))) = _
      rw [dec_or, dec_codeNat a, dec_codeNat b]
  | .ex a => by
      show dec (consN 9 (consN (codeNat a) 0)) = _
      rw [dec_ex, dec_codeNat a]

/-! ## §3 · La sustitución y el lift CONMUTAN con la decodificación, para TODO número -/

theorem dflt_subst (k : Nat) (s : Term) : substTerm k s dflt = dflt := rfl
theorem dflt_lift (c : Nat) : liftTerm c dflt = dflt := rfl

theorem substtcN_unfold (k s c : Nat) : substtcN k s c =
    if _h : c = 0 then 0
    else if nthN c 0 = 0 then
      (if k = nthN c 1 then s
       else if k < nthN c 1 then consN 0 (consN (nthN c 1 - 1) 0)
       else consN 0 (consN (nthN c 1) 0))
    else if nthN c 0 = 1 then consN 1 (consN (nthN c 1) (consN (substtscN k s (nthN c 2)) 0))
    else 0 := by
  rw [substtcN]

theorem substtscN_unfold (k s l : Nat) : substtscN k s l =
    if _h : l = 0 then 0 else consN (substtcN k s (carN l)) (substtscN k s (cdrN l)) := by
  rw [substtscN]

theorem liftcN_unfold (c t : Nat) : liftcN c t =
    if _h : t = 0 then 0
    else if nthN t 0 = 0 then
      (if nthN t 1 < c then consN 0 (consN (nthN t 1) 0) else consN 0 (consN (nthN t 1 + 1) 0))
    else if nthN t 0 = 1 then consN 1 (consN (nthN t 1) (consN (liftscN c (nthN t 2)) 0))
    else 0 := by
  rw [liftcN]

theorem liftscN_unfold (c l : Nat) : liftscN c l =
    if _h : l = 0 then 0 else consN (liftcN c (carN l)) (liftscN c (cdrN l)) := by
  rw [liftscN]

theorem decT_substVar (k s n : Nat) :
    decT (if k = n then s else if k < n then consN 0 (consN (n - 1) 0) else consN 0 (consN n 0)) =
      substTerm k (decT s) (Term.var n) := by
  show _ = (if n = k then decT s else if n > k then Term.var (n - 1) else Term.var n)
  by_cases e : k = n
  · rw [if_pos e, if_pos (show n = k from e.symm)]
  · rw [if_neg e, if_neg (show ¬ (n = k) from fun h => e h.symm)]
    by_cases l : k < n
    · rw [if_pos l, if_pos (show n > k from l), decT_var]
    · rw [if_neg l, if_neg (show ¬ (n > k) from l), decT_var]

theorem decT_substtc (k s : Nat) : ∀ c : Nat,
    And (decT (substtcN k s c) = substTerm k (decT s) (decT c))
      (decTs (substtscN k s c) = substTerms k (decT s) (decTs c)) := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases h0 : c = 0
    · subst h0
      refine ⟨?_, ?_⟩
      · rw [substtcN_unfold, dif_pos rfl, decT_zero]; rfl
      · rw [substtscN_unfold, dif_pos rfl, decTs_zero]; rfl
    · refine ⟨?_, ?_⟩
      · rw [substtcN_unfold, dif_neg h0, decT_unfold c, dif_neg h0]
        by_cases t0 : nthN c 0 = 0
        · rw [if_pos t0, if_pos t0]; exact decT_substVar k s (nthN c 1)
        · rw [if_neg t0, if_neg t0]
          by_cases t1 : nthN c 0 = 1
          · rw [if_pos t1, if_pos t1, decT_func, (ih (nthN c 2) (nthN_lt 2 h0)).2]; rfl
          · rw [if_neg t1, if_neg t1, decT_zero]; rfl
      · rw [substtscN_unfold, dif_neg h0, decTs_unfold c, dif_neg h0, decTs_consN,
          (ih (carN c) (carN_lt h0)).1, (ih (cdrN c) (cdrN_lt h0)).2]; rfl

theorem decT_liftVar (c n : Nat) :
    decT (if n < c then consN 0 (consN n 0) else consN 0 (consN (n + 1) 0)) = liftTerm c (Term.var n) := by
  show _ = (if n < c then Term.var n else Term.var (n + 1))
  by_cases l : n < c
  · rw [if_pos l, if_pos l, decT_var]
  · rw [if_neg l, if_neg l, decT_var]

theorem decT_liftc (c : Nat) : ∀ t : Nat,
    And (decT (liftcN c t) = liftTerm c (decT t)) (decTs (liftscN c t) = liftTerms c (decTs t)) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases h0 : t = 0
    · subst h0
      refine ⟨?_, ?_⟩
      · rw [liftcN_unfold, dif_pos rfl, decT_zero]; rfl
      · rw [liftscN_unfold, dif_pos rfl, decTs_zero]; rfl
    · refine ⟨?_, ?_⟩
      · rw [liftcN_unfold, dif_neg h0, decT_unfold t, dif_neg h0]
        by_cases t0 : nthN t 0 = 0
        · rw [if_pos t0, if_pos t0]; exact decT_liftVar c (nthN t 1)
        · rw [if_neg t0, if_neg t0]
          by_cases t1 : nthN t 0 = 1
          · rw [if_pos t1, if_pos t1, decT_func, (ih (nthN t 2) (nthN_lt 2 h0)).2]; rfl
          · rw [if_neg t1, if_neg t1, decT_zero]; rfl
      · rw [liftscN_unfold, dif_neg h0, decTs_unfold t, dif_neg h0, decTs_consN,
          (ih (carN t) (carN_lt h0)).1, (ih (cdrN t) (cdrN_lt h0)).2]; rfl

theorem substfcN_unfold (v t f : Nat) : substfcN v t f =
    if _h : f = 0 then 0
    else if nthN f 0 = 2 then consN 2 0
    else if nthN f 0 = 3 then consN 3 (consN (nthN f 1) (consN (substtscN v t (nthN f 2)) 0))
    else if nthN f 0 = 4 then consN 4 (consN (substtcN v t (nthN f 1)) (consN (substtcN v t (nthN f 2)) 0))
    else if nthN f 0 = 5 then consN 5 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
    else if nthN f 0 = 6 then consN 6 (consN (substfcN (v + 1) (liftcN 0 t) (nthN f 1)) 0)
    else if nthN f 0 = 7 then consN 7 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
    else if nthN f 0 = 8 then consN 8 (consN (substfcN v t (nthN f 1)) (consN (substfcN v t (nthN f 2)) 0))
    else if nthN f 0 = 9 then consN 9 (consN (substfcN (v + 1) (liftcN 0 t) (nthN f 1)) 0)
    else 0 := by
  rw [substfcN]

theorem dec_substfc : ∀ f : Nat, ∀ v t : Nat, dec (substfcN v t f) = substFormula v (decT t) (dec f) := by
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
    intro v t
    by_cases h0 : f = 0
    · subst h0; rw [substfcN_unfold, dif_pos rfl, dec_zero]; rfl
    rw [substfcN_unfold, dif_neg h0, dec_unfold f, dif_neg h0]
    have i1 := ih (nthN f 1) (nthN_lt 1 h0)
    have i2 := ih (nthN f 2) (nthN_lt 2 h0)
    by_cases t2 : nthN f 0 = 2
    · rw [if_pos t2, if_pos t2, dec_bot]; rfl
    rw [if_neg t2, if_neg t2]
    by_cases t3 : nthN f 0 = 3
    · rw [if_pos t3, if_pos t3, dec_atom, (decT_substtc v t (nthN f 2)).2]; rfl
    rw [if_neg t3, if_neg t3]
    by_cases t4 : nthN f 0 = 4
    · rw [if_pos t4, if_pos t4, dec_eq, (decT_substtc v t (nthN f 1)).1, (decT_substtc v t (nthN f 2)).1]; rfl
    rw [if_neg t4, if_neg t4]
    by_cases t5 : nthN f 0 = 5
    · rw [if_pos t5, if_pos t5, dec_impl, i1, i2]; rfl
    rw [if_neg t5, if_neg t5]
    by_cases t6 : nthN f 0 = 6
    · rw [if_pos t6, if_pos t6, dec_forall, i1, (decT_liftc 0 t).1]; rfl
    rw [if_neg t6, if_neg t6]
    by_cases t7 : nthN f 0 = 7
    · rw [if_pos t7, if_pos t7, dec_and, i1, i2]; rfl
    rw [if_neg t7, if_neg t7]
    by_cases t8 : nthN f 0 = 8
    · rw [if_pos t8, if_pos t8, dec_or, i1, i2]; rfl
    rw [if_neg t8, if_neg t8]
    by_cases t9 : nthN f 0 = 9
    · rw [if_pos t9, if_pos t9, dec_ex, i1, (decT_liftc 0 t).1]; rfl
    rw [if_neg t9, if_neg t9, dec_zero]; rfl

theorem liftfcN_unfold (c f : Nat) : liftfcN c f =
    if _h : f = 0 then 0
    else if nthN f 0 = 2 then consN 2 0
    else if nthN f 0 = 3 then consN 3 (consN (nthN f 1) (consN (liftscN c (nthN f 2)) 0))
    else if nthN f 0 = 4 then consN 4 (consN (liftcN c (nthN f 1)) (consN (liftcN c (nthN f 2)) 0))
    else if nthN f 0 = 5 then consN 5 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
    else if nthN f 0 = 6 then consN 6 (consN (liftfcN (c + 1) (nthN f 1)) 0)
    else if nthN f 0 = 7 then consN 7 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
    else if nthN f 0 = 8 then consN 8 (consN (liftfcN c (nthN f 1)) (consN (liftfcN c (nthN f 2)) 0))
    else if nthN f 0 = 9 then consN 9 (consN (liftfcN (c + 1) (nthN f 1)) 0)
    else 0 := by
  rw [liftfcN]

theorem dec_liftfc : ∀ f : Nat, ∀ c : Nat, dec (liftfcN c f) = liftFormula c (dec f) := by
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
    intro c
    by_cases h0 : f = 0
    · subst h0; rw [liftfcN_unfold, dif_pos rfl, dec_zero]; rfl
    rw [liftfcN_unfold, dif_neg h0, dec_unfold f, dif_neg h0]
    have i1 := ih (nthN f 1) (nthN_lt 1 h0)
    have i2 := ih (nthN f 2) (nthN_lt 2 h0)
    by_cases t2 : nthN f 0 = 2
    · rw [if_pos t2, if_pos t2, dec_bot]; rfl
    rw [if_neg t2, if_neg t2]
    by_cases t3 : nthN f 0 = 3
    · rw [if_pos t3, if_pos t3, dec_atom, (decT_liftc c (nthN f 2)).2]; rfl
    rw [if_neg t3, if_neg t3]
    by_cases t4 : nthN f 0 = 4
    · rw [if_pos t4, if_pos t4, dec_eq, (decT_liftc c (nthN f 1)).1, (decT_liftc c (nthN f 2)).1]; rfl
    rw [if_neg t4, if_neg t4]
    by_cases t5 : nthN f 0 = 5
    · rw [if_pos t5, if_pos t5, dec_impl, i1, i2]; rfl
    rw [if_neg t5, if_neg t5]
    by_cases t6 : nthN f 0 = 6
    · rw [if_pos t6, if_pos t6, dec_forall, i1]; rfl
    rw [if_neg t6, if_neg t6]
    by_cases t7 : nthN f 0 = 7
    · rw [if_pos t7, if_pos t7, dec_and, i1, i2]; rfl
    rw [if_neg t7, if_neg t7]
    by_cases t8 : nthN f 0 = 8
    · rw [if_pos t8, if_pos t8, dec_or, i1, i2]; rfl
    rw [if_neg t8, if_neg t8]
    by_cases t9 : nthN f 0 = 9
    · rw [if_pos t9, if_pos t9, dec_ex, i1]; rfl
    rw [if_neg t9, if_neg t9, dec_zero]; rfl


/-! ## §4 · W1: lo que el verificador ACEPTA en el modelo, decodificado, es teorema de `Prf` -/

open ROBINSON_PlusPlus.Meta.ModeloEstandar ROBINSON_PlusPlus.Meta.ModeloCodificacion

theorem memN_codeNatList : ∀ (L : List Formula) (y : Nat), memN y (codeNatList L) →
    ∃ a, And (List.Mem a L) (y = codeNat a)
  | [], y, h => absurd h (memN_zero y)
  | f :: fs, y, h => by
      cases (memN_consN y (codeNat f) (codeNatList fs)).mp h with
      | inl e => exact ⟨f, List.Mem.head _, e⟩
      | inr h' =>
        obtain ⟨a, ha, e⟩ := memN_codeNatList fs y h'
        exact ⟨a, List.Mem.tail _ ha, e⟩

def Bueno (c : Nat) : Prop := ∀ y, memN y c → Prf (dec y)

theorem bueno_zero : Bueno 0 := fun y h => absurd h (memN_zero y)

theorem bueno_snoc {c x : Nat} (hc : Bueno c) (hx : Prf (dec x)) : Bueno (concatN c (consN x 0)) := by
  intro y hy
  cases (memN_concatN y c (consN x 0)).mp hy with
  | inl h => exact hc y h
  | inr h =>
    cases (memN_consN y x 0).mp h with
    | inl e => rw [e]; exact hx
    | inr h' => exact absurd h' (memN_zero y)

theorem decT_TC0 : decT TC0 = zero := decT_codeNatTerm zero
theorem decT_TCS : decT TCS = succ (Term.var 0) := decT_codeNatTerm (succ (Term.var 0))
theorem decT_TNIL : decT TNIL = nil := decT_codeNatTerm nil
theorem decT_TCONS : decT TCONS = cons (Term.var 1) (Term.var 0) := decT_codeNatTerm (cons (Term.var 1) (Term.var 0))

/-- El `simp` que decodifica una conclusión: los constructores, la sustitución y el lift. -/
local macro "decodifica" : tactic => `(tactic| simp only [dec_impl, dec_and, dec_or, dec_bot, dec_eq,
    dec_forall, dec_ex, dec_substfc, dec_liftfc, decT_TC0, decT_TCS, decT_TNIL, decT_TCONS])

variable {x : Nat}

theorem linea_p1 (hT : lineWFT V₀ 0 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.p1 _ _)
theorem linea_p2 (hT : lineWFT V₀ 1 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.p2 _ _ _)
theorem linea_c1 (hT : lineWFT V₀ 2 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.c1 _ _)
theorem linea_c2 (hT : lineWFT V₀ 3 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.c2 _ _)
theorem linea_c3 (hT : lineWFT V₀ 4 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.c3 _ _)
theorem linea_j1 (hT : lineWFT V₀ 5 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.j1 _ _)
theorem linea_j2 (hT : lineWFT V₀ 6 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.j2 _ _)
theorem linea_j3 (hT : lineWFT V₀ 7 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.j3 _ _ _)
theorem linea_efq (hT : lineWFT V₀ 8 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.efq _)
theorem linea_q1 (hT : lineWFT V₀ 9 x) : Prf (dec (carN x)) := by
  rw [hT.2.2.2]; decodifica; exact Prf.incl (Prfᵢ.q1 _ _)
theorem linea_q2 (hT : lineWFT V₀ 10 x) : Prf (dec (carN x)) := by
  rw [hT.2.2.2]; decodifica; exact Prf.incl (Prfᵢ.q2 _ _)
theorem linea_q3 (hT : lineWFT V₀ 11 x) : Prf (dec (carN x)) := by
  rw [hT.2.2]; decodifica; exact Prf.incl (Prfᵢ.q3 _ _)
theorem linea_eqrefl (hT : lineWFT V₀ 12 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.incl (Prfᵢ.eqrefl _)
theorem linea_leibniz (hT : lineWFT V₀ 13 x) : Prf (dec (carN x)) := by
  rw [hT.2.2.2.2]; decodifica; exact Prf.incl (Prfᵢ.leibniz _ _ _)
theorem linea_p3 (hT : lineWFT V₀ 14 x) : Prf (dec (carN x)) := by
  rw [hT.2]; decodifica; exact Prf.p3 _
theorem linea_thy (hT : lineWFT V₀ 15 x) : Prf (dec (carN x)) := by
  have hm : memN (carN x) V₀ := hT.2
  rw [ROBINSON_PlusPlus.Meta.Consistencia.V₀_eq_codigo] at hm
  obtain ⟨a, ha, e⟩ := memN_codeNatList axioms (carN x) hm
  rw [e, dec_codeNat]
  exact Prf.incl (Prfᵢ.thy a ha)
theorem linea_ind (hT : lineWFT V₀ 18 x) : Prf (dec (carN x)) := by
  rw [hT.2.2]; decodifica; exact Prf.ind _
theorem linea_qconf (hT : lineWFT V₀ 19 x) : Prf (dec (carN x)) := by
  rw [hT.2.2]; decodifica; exact Prf.qconf _ _
theorem linea_listInd (hT : lineWFT V₀ 20 x) : Prf (dec (carN x)) := by
  rw [hT.2.2]; decodifica; exact Prf.listInd _

theorem linea_mp {c : Nat} (hc : Bueno c) (hp : allInN c (premsOfN x)) (hk : nthN x 1 = 16) :
    Prf (dec (carN x)) := by
  have e : premsOfN x = consN (consN 5 (consN (nthN x 2) (consN (carN x) 0))) (consN (nthN x 2) 0) := by
    rw [premsOfN, if_pos hk]; rfl
  rw [e] at hp
  have h1 := (allInN_consN c _ _).mp hp
  have h2 := (allInN_consN c _ _).mp h1.2
  have hAB := hc _ h1.1
  have hA := hc _ h2.1
  rw [dec_impl] at hAB
  exact Prf.mp _ _ hAB hA

theorem linea_gen {c : Nat} (hc : Bueno c) (hp : allInN c (premsOfN x)) (hk : nthN x 1 = 17)
    (hT : lineWFT V₀ 17 x) : Prf (dec (carN x)) := by
  have e : premsOfN x = consN (nthN x 2) 0 := by
    rw [premsOfN, if_neg (by rw [hk]; decide), if_pos hk]
  rw [e] at hp
  have hA := hc _ ((allInN_consN c _ _).mp hp).1
  rw [hT.2, dec_forall]
  exact Prf.gen _ hA

theorem linea_buena (c : Nat) (hc : Bueno c) (hp : allInN c (premsOfN x)) :
    ∀ K, nthN x 1 = K → K < 21 → lineWFT V₀ K x → Prf (dec (carN x))
  | 0, _, _, hT => linea_p1 hT
  | 1, _, _, hT => linea_p2 hT
  | 2, _, _, hT => linea_c1 hT
  | 3, _, _, hT => linea_c2 hT
  | 4, _, _, hT => linea_c3 hT
  | 5, _, _, hT => linea_j1 hT
  | 6, _, _, hT => linea_j2 hT
  | 7, _, _, hT => linea_j3 hT
  | 8, _, _, hT => linea_efq hT
  | 9, _, _, hT => linea_q1 hT
  | 10, _, _, hT => linea_q2 hT
  | 11, _, _, hT => linea_q3 hT
  | 12, _, _, hT => linea_eqrefl hT
  | 13, _, _, hT => linea_leibniz hT
  | 14, _, _, hT => linea_p3 hT
  | 15, _, _, hT => linea_thy hT
  | 16, hk, _, _ => linea_mp hc hp hk
  | 17, hk, _, hT => linea_gen hc hp hk hT
  | 18, _, _, hT => linea_ind hT
  | 19, _, _, hT => linea_qconf hT
  | 20, _, _, hT => linea_listInd hT
  | n + 21, _, hlt, _ => absurd hlt (by omega)

theorem cadena_buena : ∀ (l : List Nat) (c : Nat), Bueno c → chainOkL V₀ c l → Bueno (runFnL c l)
  | [], _, hc, _ => hc
  | x :: r, c, hc, h =>
    cadena_buena r _ (bueno_snoc hc (linea_buena c hc h.1.2 (nthN x 1) rfl h.1.1.1 h.1.1.2)) h.2

/-- 🏁 **W1**: si `MNV V₀` cree que la cadena `p` es una prueba, todo lo que concluye, decodificado, es teorema
    de `Prf`. -/
theorem verificador_solido {p y : Nat} (h : chainOkN V₀ 0 p) (hy : memN y (runFnN 0 p)) : Prf (dec y) :=
  cadena_buena (decodeL p) 0 bueno_zero h y hy

/-! ## §5 · ⊬ ¬G: Gödel I, la otra mitad, por la solidez del verificador en el modelo -/

theorem ev_provCodeC' (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNV V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) →
      ∃ p, And (chainOkN V₀ 0 p) (memN (codeNat φ) (runFnN 0 p)) := by
  intro h
  rw [ROBINSON_PlusPlus.Meta.ProofChain.provCodeC', eval_substFormula_zero,
    ← ROBINSON_PlusPlus.Meta.Representability.formCodeM_eq, ev_formCodeM] at h
  simp only [ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC', land, chainOk, In, runFn, nil, zero,
    in_sym, zero_sym, evalFormula, evalTerm, evalTerms, shiftEnv, MN_chainOk, MN_mem, MN_runFn, MN_zero] at h
  exact h

/-- Lo que el modelo cree demostrable, lo es: `ev_provCodeC'`, W1 y `dec_codeNat`. -/
theorem prf_of_prov (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNV V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) → Prf φ := by
  intro hp
  obtain ⟨p, hc, hm⟩ := ev_provCodeC' _ _ hp
  have h := verificador_solido hc hm
  rw [dec_codeNat] at h
  exact h

/-- 🏁 **`Prov` es FIEL en el modelo estándar**: `MNV V₀ ⊨ Prov(⌜φ⌝)` exactamente cuando `φ` es teorema. La ida es
    W1; la vuelta, D1 (`repr_pos'_prf`) y la solidez. Es también el control de vacuidad de W1: su hipótesis se
    cumple para cada teorema. -/
theorem modelo_prov_iff (φ : Formula) (v : Nat → Nat) :
    evalFormula (MNV V₀) v (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' φ) ↔ Prf φ :=
  ⟨prf_of_prov φ v, fun h => ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    (ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf h) v⟩

/-- 🏁🏁 **GÖDEL I, la mitad `⊬ ¬G`**, sin hipótesis: con `Prf ¬G`, el modelo creería demostrable `G` (por el
    punto fijo), y lo que cree demostrable lo es (`prf_of_prov`); `goedel_I` lo impide. -/
theorem goedel_I_neg : ¬ Prf (neg ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) := by
  intro hn
  have hfp := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint (fun _ => 0)
  have hng := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    hn (fun _ => 0)
  have hprov : evalFormula (MNV V₀) (fun _ => 0)
      (ROBINSON_PlusPlus.Meta.ProofChain.provCodeC' ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN) := by
    apply Classical.byContradiction
    intro hnp
    exact hng (hfp.2 hnp)
  exact ROBINSON_PlusPlus.Meta.Consistencia.goedel_I (prf_of_prov _ _ hprov)

/-- 🏁🏁 **`G` es INDECIDIBLE en `Prf`**: ni `G` (`goedel_I`) ni `¬G` (`goedel_I_neg`). -/
theorem godelCN_indecidible : And (¬ Prf ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)
    (¬ Prf (neg ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN)) :=
  ⟨ROBINSON_PlusPlus.Meta.Consistencia.goedel_I, goedel_I_neg⟩

/-! ## §6 · E10: `G` y `Con` son VERDADERAS en el modelo estándar

Lo que dicen —«no soy demostrable», «`⊥` no es demostrable»— es cierto en `MNV V₀`: si el modelo creyera lo
contrario, `prf_of_prov` daría `Prf G` o `Prf ⊥`, y `goedel_I`/`consistencia` lo impiden. -/

/-- 🏁 **`G` es VERDADERA en `MNV V₀`** (y no demostrable: `goedel_I`). -/
theorem godelCN_verdadera (v : Nat → Nat) :
    evalFormula (MNV V₀) v ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN := by
  have hfp := ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound ROBINSON_PlusPlus.Meta.Consistencia.estandar_MN
    ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint v
  apply hfp.2
  intro hp
  exact ROBINSON_PlusPlus.Meta.Consistencia.goedel_I (prf_of_prov _ _ hp)

/-- 🏁 **`Con` es VERDADERA en `MNV V₀`** (y no demostrable: `goedel_II`). -/
theorem con_verdadera (v : Nat → Nat) :
    evalFormula (MNV V₀) v ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula' :=
  fun hp => ROBINSON_PlusPlus.Meta.Consistencia.consistencia (prf_of_prov _ _ hp)

end ROBINSON_PlusPlus.Meta.SolidezVerificador


#print axioms ROBINSON_PlusPlus.Meta.SolidezVerificador.verificador_solido
#print axioms ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg
#print axioms ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_indecidible
#print axioms ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_verdadera
#print axioms ROBINSON_PlusPlus.Meta.SolidezVerificador.con_verdadera
#print axioms ROBINSON_PlusPlus.Meta.SolidezVerificador.modelo_prov_iff
