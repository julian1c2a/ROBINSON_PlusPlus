import FOL

namespace ProbeVac

open FOL.Sequent0
open FOL.Craig0
open FOL.Herbrand0

-- ══════════════════════════════════════════════════════════════════════════
-- ⛔⛔ EL CONTRAEJEMPLO: la condición de lenguaje relativizada a `E` es VACUA
--
-- ADR-067. Este fichero es la EVIDENCIA de que el `maehara_eq` anunciado en ADR-066 §2
-- no debe aterrizar. Compila con salida vacía; si algún día deja de compilar porque
-- `EqInstance.atom` se estrechó (frescura, pertenencia al secuente), entonces la ruta
-- descartada vuelve a estar viva y hay que reabrir ADR-067.
--
-- `EqInstance.atom` toma `p : String` **completamente libre** — sin frescura, sin
-- pertenencia al secuente, sin relación con `pre/post/a/b`. Y `eqAtomAx p …` contiene
-- `Formula.atom p …`. Como `E` es una salida EXISTENCIAL SIN COTA, para CUALQUIER
-- interpolante se puede fabricar un `E` que satisfaga las DOS condiciones a la vez sin
-- mirar el secuente.
-- ══════════════════════════════════════════════════════════════════════════

private def t : Term := Term.var 0
private def P : Formula := Formula.atom "P" []
private def C : Formula := Formula.impl P P
private def Ebad : List Formula := [eqAtomAx "P" [] [] t t]

/-- (i) `Ebad` son instancias de igualdad legítimas. -/
theorem vac_eqInstance : ∀ g, g ∈ Ebad → EqInstance g := by
  intro g hg
  cases hg with
  | head => exact EqInstance.atom "P" [] [] t t
  | tail _ hm => exact absurd hm List.not_mem_nil

/-- (ii)/(iii) las dos derivaciones existen. -/
theorem vac_der1 : LK₀ [] (C :: []) :=
  LK₀.implR [] [] P P (LK₀.ax [P] [P] P (List.Mem.head _) (List.Mem.head _))

theorem vac_der2 : LK₀ (C :: []) [Formula.eq t t] :=
  LK₀.eqAx [C] [Formula.eq t t] (eqReflAx t) (EqInstance.refl t)
    (LK₀.ax _ _ (Formula.eq t t) (List.Mem.head _) (List.Mem.head _))

/-- ⛔ (iv)/(v) **Y LAS DOS CONDICIONES DE LENGUAJE SE CUMPLEN** — con un interpolante cuyo
predicado `P` **no aparece en ninguno de los dos lados del secuente**. -/
theorem vac_cond1 : PredSub C ([] ++ [] ++ Ebad) := by
  intro p hp
  refine ⟨eqAtomAx "P" [] [] t t, List.mem_append.mpr (Or.inr (List.Mem.head _)), ?_⟩
  exact Or.inr (Or.inl (hp.elim (fun h => h) (fun h => h)))

theorem vac_cond2 : PredSub C ([] ++ [Formula.eq t t] ++ Ebad) := by
  intro p hp
  refine ⟨eqAtomAx "P" [] [] t t, List.mem_append.mpr (Or.inr (List.Mem.head _)), ?_⟩
  exact Or.inr (Or.inl (hp.elim (fun h => h) (fun h => h)))

-- ══════════════════════════════════════════════════════════════════════════
-- LA TABLA QUE EXPLICA POR QUÉ: cuatro de las cinco son transparentes, y la quinta
-- toma un predicado ARBITRARIO
-- ══════════════════════════════════════════════════════════════════════════

theorem predF_eqReflAx (p : String) (u : Term) : Not (predF p (eqReflAx u)) := id

theorem predF_eqSymmAx (p : String) (u v : Term) : Not (predF p (eqSymmAx u v)) :=
  fun h => h.elim id id

theorem predF_eqTransAx (p : String) (u v w : Term) : Not (predF p (eqTransAx u v w)) :=
  fun h => h.elim id (fun h2 => h2.elim id id)

theorem predF_eqFuncAx (p f : String) (pre post : List Term) (a b : Term) :
    Not (predF p (eqFuncAx f pre post a b)) := fun h => h.elim id id

/-- ⛔⛔ **LA QUINTA, Y ES LA QUE LO ROMPE TODO.** `EqInstance.atom` toma `q : String`
**libre** —sin frescura, sin pertenencia al secuente— y el axioma MENCIONA `q`. ⇒ para
cualquier `p` existe una instancia de igualdad legítima que lo aporta. -/
theorem predF_eqAtomAx (p q : String) (pre post : List Term) (a b : Term) :
    Iff (predF p (eqAtomAx q pre post a b)) (q = p) := by
  constructor
  · intro h
    exact h.elim (fun hc => hc.elim) (fun h2 => h2.elim id id)
  · intro h
    exact Or.inr (Or.inl h)

/-- ⛔ **Y de ahí sale la vacuidad en general**: para todo `p` hay una `EqInstance` que lo
aporta, luego un `E` sin cota satisface cualquier condición de lenguaje. -/
theorem eqInstance_aporta_cualquier_predicado (p : String) :
    ∃ g, And (EqInstance g) (predF p g) :=
  ⟨eqAtomAx p [] [] t t, EqInstance.atom p [] [] t t, Or.inr (Or.inl rfl)⟩

end ProbeVac
