/-
# PRELUDE del hito (i) — el TESTIGO DE PARSEO `subCodes`

Fichero AUTOCONTENIDO (`import ROBINSON_PlusPlus.Meta` y nada más). Contiene el SUELO sobre el
que se hace la inducción principal `nodeOk_of_mem_subCodes`. NO contiene esa inducción.

    lake env lean Probe/SubCodesPrelude.lean

Contenido, por orden:
 §1  las definiciones OBJETO (`nulOk` … `isFCB`), copia LITERAL de `sondeos/A3IsFCBTracked.lean`
     (con la enmienda R‑A3‑1: `consOk` caso a caso, y el disyunto 10 `X = nil` DESNUDO).
 §2  `prf_cdrc_cons` — gemelo de `prf_carc_cons`, re‑derivado desde `ax_cdrc`.
 §3  `prf_consOk_cons` — la obligación nueva, descargada de una vez para los 11 disyuntos.
 §4  `subCodes` / `subCodesT` / `subCodesTs` (la forma propuesta VERIFICADA; ver §4 abajo).
 §5  la CLAUSURA de `objList (subCodes φ)` (lo que pide `prf_wfAll_objList`).
 §6  el puente `objList` ⇄ meta (`prf_lenc_objList`, `prf_nthc_objList`, `prf_In_objList`).
 §7  `prf_bdAll_numeral`.
 §8  `PrfH_congr_nodeOk` y `prf_wfAll_objList` REPROBADOS para el `nodeOk` NUEVO (con `consOk`).
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

namespace SubCodesPrelude

/-! ## 1 · EL OBJETO — copia LITERAL de `sondeos/A3IsFCBTracked.lean` §1

    ⚠️ El disyunto 10 (`Formula.eq X nil`) va DESNUDO, SIN `cOk`. Ponerle `consOk` encima deja
    el predicado SIN TESTIGOS: `termsCodeM [] = nil` y la cola de toda lista de argumentos
    termina ahí (`nil_ne_cons`, `Meta/CodeDistinct.lean:67`). -/

def nulOk (X : Term) (k : Nat) : Formula :=
  land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 1))

def unOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 2)))
       (In (nthc X (numeralM 1)) w)

def binOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (land (In (nthc X (numeralM 1)) w) (In (nthc X (numeralM 2)) w))

def strBinOk (w X : Term) (k : Nat) : Formula :=
  land (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) w)

def varOk (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

/-- Disyunción asociada a la derecha de una lista NO vacía. -/
def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

/-- El nodo es un `cons` (enmienda R‑A3‑1). -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

/-- Envoltorio: «además de `F`, el nodo es un `cons`». -/
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def nodeOk (w X : Term) : Formula :=
  lorAll (cOk X (nulOk X 2))                        -- ⊥                       (tag 2)
    [ cOk X (strBinOk w X 3)                        -- atom p ts               (tag 3)
    , cOk X (binOk w X 4)                           -- eq t u                  (tag 4)
    , cOk X (binOk w X 5)                           -- impl a b                (tag 5)
    , cOk X (unOk  w X 6)                           -- ∀ a                     (tag 6)
    , cOk X (binOk w X 7)                           -- ∧ a b                   (tag 7)
    , cOk X (binOk w X 8)                           -- ∨ a b                   (tag 8)
    , cOk X (unOk  w X 9)                           -- ∃ a                     (tag 9)
    , cOk X (varOk X)                               -- var n                   (tag 0)
    , cOk X (strBinOk w X 1)                        -- func s ts               (tag 1)
    , Formula.eq X nil                              -- termsCodeM []   ⚠️ DESNUDO
    , cOk X (land (In (carc X) w) (In (cdrc X) w)) ]-- termsCodeM (t :: ts)

def wfAll (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOk (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

def isFCB (w c : Term) : Formula := land (wfAll w) (In c w)

/-! ## 2 · `prf_cdrc_cons` — el gemelo de `prf_carc_cons`, que NO está en producción -/

/-- `cdrc (cons h t) = t` en `Prf`, desde `ax_cdrc`. -/
theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

/-! ## 3 · `consOk` sobre un `cons` LITERAL — la obligación nueva del hito (i) -/

/-- `⊢ consOk (cons a b)`. En la construcción de `subCodes` **todo** nodo de los 11 disyuntos
    con `cOk` es un `cons` literal, así que este lema los cubre los 11. -/
theorem prf_consOk_cons (a b : Term) : Prf (consOk (cons a b)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons a b)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons a b)))

/-! ## 4 · EL TESTIGO `subCodes` — la forma propuesta, VERIFICADA disyunto a disyunto

    Cada línea está dictada por el disyunto que le toca al nodo y por las casillas que ese
    disyunto exige «`In … w`»:

    | nodo | disyunto | casillas exigidas | qué las aporta |
    |---|---|---|---|
    | `formCodeM ⊥ = cons 2̄ nil` | `nulOk 2` | — | — |
    | `formCodeM (atom p ts)` | `strBinOk 3` | `nthc X 2 = termsCodeM ts` | `subCodesTs ts` (cabeza) |
    | `formCodeM (eq t u)` | `binOk 4` | `termCodeM t`, `termCodeM u` | `subCodesT t`, `subCodesT u` |
    | `formCodeM (impl a b)` | `binOk 5` | `formCodeM a`, `formCodeM b` | `subCodes a`, `subCodes b` |
    | `formCodeM (∀ a)` | `unOk 6` | `formCodeM a` | `subCodes a` |
    | `formCodeM (∧ a b)` | `binOk 7` | `formCodeM a`, `formCodeM b` | ídem |
    | `formCodeM (∨ a b)` | `binOk 8` | `formCodeM a`, `formCodeM b` | ídem |
    | `formCodeM (∃ a)` | `unOk 9` | `formCodeM a` | `subCodes a` |
    | `termCodeM (var n)` | `varOk` | — (la casilla 1 es un NUMERAL) | — |
    | `termCodeM (func s ts)` | `strBinOk 1` | `nthc X 2 = termsCodeM ts` | `subCodesTs ts` |
    | `termsCodeM [] = nil` | `X = nil` (⚠️ desnudo) | — | — |
    | `termsCodeM (t::ts)` | el 12 (`cons`) | `carc X = termCodeM t`, `cdrc X = termsCodeM ts` | `subCodesT t`, `subCodesTs ts` |

    **Veredicto: la forma propuesta es CORRECTA, no hay nada que corregir.** Las dos
    propiedades que la hacen funcionar (y que hay que preservar si alguien la toca):
    1. la **CABEZA** de `subCodes φ` / `subCodesT t` / `subCodesTs ts` es exactamente
       `formCodeM φ` / `termCodeM t` / `termsCodeM ts` (⇒ `mem_self_*` de abajo);
    2. `subCodesTs [] = [nil]` es **IMPRESCINDIBLE**: sin él la cadena de argumentos se queda
       sin su último eslabón y el disyunto 12 de `termsCodeM [t]` no se puede descargar. -/

mutual
def subCodesT : Term → List Term
  | .var n     => [termCodeM (.var n)]
  | .func s ts => termCodeM (.func s ts) :: subCodesTs ts
def subCodesTs : List Term → List Term
  | []      => [nil]
  | t :: ts => termsCodeM (t :: ts) :: (subCodesT t ++ subCodesTs ts)
end

def subCodes : Formula → List Term
  | .bottom          => [formCodeM Formula.bottom]
  | .atom p ts       => formCodeM (.atom p ts) :: subCodesTs ts
  | .eq t u          => formCodeM (.eq t u) :: (subCodesT t ++ subCodesT u)
  | .impl a b        => formCodeM (.impl a b) :: (subCodes a ++ subCodes b)
  | Formula.forall a => formCodeM (Formula.forall a) :: subCodes a
  | .and a b         => formCodeM (.and a b) :: (subCodes a ++ subCodes b)
  | .or a b          => formCodeM (.or a b) :: (subCodes a ++ subCodes b)
  | .ex a            => formCodeM (.ex a) :: subCodes a

/-! ### La CABEZA: el propio código está siempre en su testigo (da el `In c w` de `isFCB`) -/

theorem mem_self_subCodesT (t : Term) : List.Mem (termCodeM t) (subCodesT t) := by
  cases t with
  | var n     => simp only [subCodesT]; exact List.Mem.head _
  | func s ts => simp only [subCodesT]; exact List.Mem.head _

theorem mem_self_subCodesTs : ∀ ts : List Term, List.Mem (termsCodeM ts) (subCodesTs ts)
  | []      => by simp only [subCodesTs, termsCodeM]; exact List.Mem.head _
  | _ :: _  => by simp only [subCodesTs]; exact List.Mem.head _

theorem mem_self_subCodes (φ : Formula) : List.Mem (formCodeM φ) (subCodes φ) := by
  cases φ <;> (simp only [subCodes]; exact List.Mem.head _)

/-! ## 5 · CLAUSURA: `objList (subCodes φ)` es CERRADO

    Es lo que exige `prf_wfAll_objList` (`hcl`, `hlift`). Todos los lemas de clausura de los
    códigos YA ESTÁN EN PRODUCCIÓN (`Minimal/Axioms.lean:604‑718`): `liftTerm_formCodeM`,
    `liftTerm_termCodeM`, `liftTerm_termsCodeM`, `liftTerm_nil` y sus gemelos `substTerm_*`.
    Aquí sólo se propagan a la lista. -/

/-- «`x` es un código CERRADO»: `liftTerm` y `substTerm` lo dejan igual. -/
def CodeClosed (x : Term) : Prop :=
  (∀ c : Nat, liftTerm c x = x) ∧ (∀ (v : Nat) (s : Term), substTerm v s x = x)

theorem closed_formCodeM (φ : Formula) : CodeClosed (formCodeM φ) :=
  ⟨fun c => liftTerm_formCodeM c φ, fun v s => substTerm_formCodeM v s φ⟩

theorem closed_termCodeM (t : Term) : CodeClosed (termCodeM t) :=
  ⟨fun c => liftTerm_termCodeM c t, fun v s => substTerm_termCodeM v s t⟩

theorem closed_termsCodeM (ts : List Term) : CodeClosed (termsCodeM ts) :=
  ⟨fun c => liftTerm_termsCodeM c ts, fun v s => substTerm_termsCodeM v s ts⟩

theorem closed_nil : CodeClosed nil :=
  ⟨fun c => liftTerm_nil c, fun v s => substTerm_nil v s⟩

mutual
theorem closed_mem_subCodesT : ∀ (t x : Term), List.Mem x (subCodesT t) → CodeClosed x
  | .var n, x, h => by
      simp only [subCodesT] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.var n)
      · cases h'
  | .func s ts, x, h => by
      simp only [subCodesT] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termCodeM (.func s ts)
      · exact closed_mem_subCodesTs ts x h'
theorem closed_mem_subCodesTs : ∀ (ts : List Term) (x : Term),
    List.Mem x (subCodesTs ts) → CodeClosed x
  | [], x, h => by
      simp only [subCodesTs] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_nil
      · cases h'
  | t :: ts, x, h => by
      simp only [subCodesTs] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_termsCodeM (t :: ts)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodesT t x hA
        · exact closed_mem_subCodesTs ts x hB
end

theorem closed_mem_subCodes : ∀ (φ : Formula) (x : Term), List.Mem x (subCodes φ) → CodeClosed x
  | .bottom, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM Formula.bottom
      · cases h'
  | .atom p ts, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.atom p ts)
      · exact closed_mem_subCodesTs ts x h'
  | .eq t u, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.eq t u)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodesT t x hA
        · exact closed_mem_subCodesT u x hB
  | .impl a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.impl a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodes a x hA
        · exact closed_mem_subCodes b x hB
  | Formula.forall a, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (Formula.forall a)
      · exact closed_mem_subCodes a x h'
  | .and a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.and a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodes a x hA
        · exact closed_mem_subCodes b x hB
  | .or a b, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.or a b)
      · rcases List.mem_append.mp h' with hA | hB
        · exact closed_mem_subCodes a x hA
        · exact closed_mem_subCodes b x hB
  | .ex a, x, h => by
      simp only [subCodes] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact closed_formCodeM (.ex a)
      · exact closed_mem_subCodes a x h'

/-! ### Propagación a `objList` -/

theorem liftTerm_objList (c : Nat) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → liftTerm c x = x) → liftTerm c (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, liftTerm, liftTerms, h e (List.Mem.head _),
        liftTerm_objList c es (fun x hx => h x (List.Mem.tail _ hx))]

theorem substTerm_objList (v : Nat) (s : Term) : ∀ (L : List Term),
    (∀ x : Term, List.Mem x L → substTerm v s x = x) → substTerm v s (objList L) = objList L
  | [],      _ => rfl
  | e :: es, h => by
      simp only [objList, cons, substTerm, substTerms, h e (List.Mem.head _),
        substTerm_objList v s es (fun x hx => h x (List.Mem.tail _ hx))]

/-- **`hlift`** para `prf_wfAll_objList`. -/
theorem liftTerm_objList_subCodes (c : Nat) (φ : Formula) :
    liftTerm c (objList (subCodes φ)) = objList (subCodes φ) :=
  liftTerm_objList c (subCodes φ) (fun x hx => (closed_mem_subCodes φ x hx).1 c)

/-- **`hcl`** para `prf_wfAll_objList`. -/
theorem substTerm_objList_subCodes (v : Nat) (s : Term) (φ : Formula) :
    substTerm v s (objList (subCodes φ)) = objList (subCodes φ) :=
  substTerm_objList v s (subCodes φ) (fun x hx => (closed_mem_subCodes φ x hx).2 v s)

theorem liftTerm_objList_subCodesT (c : Nat) (t : Term) :
    liftTerm c (objList (subCodesT t)) = objList (subCodesT t) :=
  liftTerm_objList c (subCodesT t) (fun x hx => (closed_mem_subCodesT t x hx).1 c)

theorem substTerm_objList_subCodesT (v : Nat) (s t : Term) :
    substTerm v s (objList (subCodesT t)) = objList (subCodesT t) :=
  substTerm_objList v s (subCodesT t) (fun x hx => (closed_mem_subCodesT t x hx).2 v s)

theorem liftTerm_objList_subCodesTs (c : Nat) (ts : List Term) :
    liftTerm c (objList (subCodesTs ts)) = objList (subCodesTs ts) :=
  liftTerm_objList c (subCodesTs ts) (fun x hx => (closed_mem_subCodesTs ts x hx).1 c)

theorem substTerm_objList_subCodesTs (v : Nat) (s : Term) (ts : List Term) :
    substTerm v s (objList (subCodesTs ts)) = objList (subCodesTs ts) :=
  substTerm_objList v s (subCodesTs ts) (fun x hx => (closed_mem_subCodesTs ts x hx).2 v s)

/-! ## 6 · El puente `objList` ⇄ meta (copia de `sondeos/ParseWitness.lean` §3) -/

theorem prf_lenc_objList : ∀ L : List Term,
    Prf (Formula.eq (lenc (objList L)) (numeralM L.length))
  | []      => prf_lenc_nil
  | e :: es =>
      prf_eq_trans (prf_lenc_cons e (objList es)) (prf_eq_congr_succ (prf_lenc_objList es))

theorem prf_nthc_objList : ∀ (L : List Term) (k : Nat) (x : Term), L[k]? = some x →
    Prf (Formula.eq (nthc (objList L) (numeralM k)) x)
  | [],      k,     x, h => by simp at h
  | e :: es, 0,     x, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact prf_nthc_zero e (objList es)
  | e :: es, k + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      exact prf_eq_trans (prf_nthc_succ e (objList es) (numeralM k))
        (prf_nthc_objList es k x h)

-- ⚠️ `x ∈ L` NO se puede escribir: con `Minimal.Axioms` abierto, `∈` es el `In` OBJETO
-- (`scoped notation:50 x " ∈ " l => In x l`). Hay que escribir `List.Mem x L`.
theorem prf_In_objList : ∀ (L : List Term) (x : Term), List.Mem x L → Prf (In x (objList L))
  | [],      x, h => by cases h
  | e :: es, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact prf_in_cons_head x (objList es)
      · exact prf_in_cons_tail e (prf_In_objList es x h')

/-! ## 7 · `prf_bdAll_numeral` (copia de `sondeos/ParseWitness.lean` §2)

    Con la cota CONCRETA el paso es legítimo (no es la ω-regla): `i < σⁿ0` se descompone en
    `i = 0 ∨ … ∨ i = n-1` iterando `prf_lt_succ_split`. -/

theorem prf_bdAll_numeral (Φ : Formula) (hΦ : substFormula 0 (.var 0) Φ = Φ) : ∀ (n : Nat),
    (∀ k : Nat, k < n → Prf (substFormula 0 (numeralM k) Φ)) →
      Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM n)) Φ))
  | 0, _ => by
      refine Prf.gen _ (prf_deduction ?_)
      exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prfᵢ.efq Φ))
        (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _)))
  | n + 1, h => by
      have ih := prf_bdAll_numeral Φ hΦ n (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM n)) Φ)
          = Formula.impl (lt (.var 0) (numeralM n)) Φ := by
        simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
      refine Prf.gen _ (prf_deduction ?_)
      have hsplit : PrfH [lt (.var 0) (numeralM (n + 1))]
          (lor (lt (.var 0) (numeralM n)) (Formula.eq (.var 0) (numeralM n))) :=
        PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) (numeralM n)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      refine PrfH_or_elim hsplit ?brA ?brB
      case brA =>
        exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec ih (.var 0)) _)
          (PrfH.hyp _ _ (List.Mem.head _))
      case brB =>
        have hinst : Prf (substFormula 0 (numeralM n) Φ) := h n (Nat.lt_succ_self n)
        have heq : PrfH (Formula.eq (.var 0) (numeralM n) :: [lt (.var 0) (numeralM (n + 1))])
            (Formula.eq (numeralM n) (.var 0)) :=
          PrfH_eq_symm (PrfH.hyp _ _ (List.Mem.head _))
        have := PrfH_leibniz_subst (A := Φ) heq (prf_to_prfH hinst _)
        rwa [hΦ] at this

/-! ## 8 · `PrfH_congr_nodeOk` y `prf_wfAll_objList` PARA EL `nodeOk` NUEVO

    Respecto de `sondeos/ParseWitness.lean` la única diferencia son las dos entradas nuevas
    del simp set (`cOk`, `consOk`) y `cons` (que `consOk` introduce). -/

/-- Congruencia de `nthc` en el ÍNDICE. -/
theorem PrfH_congr_nthc_idx {Γ : List Formula} {w i₁ i₂ : Term} (h : PrfH Γ (i₁ =eq i₂)) :
    PrfH Γ (nthc w i₁ =eq nthc w i₂) := by
  let f : Formula :=
    Formula.eq (nthc (liftTerm 0 w) (liftTerm 0 i₁)) (nthc (liftTerm 0 w) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w i₁) (nthc w s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS i₂) ▸ PrfH_leibniz_subst (A := f) h ((hS i₁) ▸ prf_to_prfH (prf_refl (nthc w i₁)) Γ)

/-- **Leibniz sobre el nodo — UNA sola aplicación, no 12** (con `consOk` dentro). -/
theorem PrfH_congr_nodeOk {Γ : List Formula} {w X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (hN : PrfH Γ (nodeOk w X₁)) : PrfH Γ (nodeOk w X₂) := by
  let f : Formula := nodeOk (liftTerm 0 w) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = nodeOk w s := by
    intro s
    simp only [f, nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

theorem prf_congr_nodeOk {w X₁ X₂ : Term} (h : Prf (X₁ =eq X₂)) (hN : Prf (nodeOk w X₁)) :
    Prf (nodeOk w X₂) :=
  prfH_nil_to_prf (PrfH_congr_nodeOk (prf_to_prfH h []) (prf_to_prfH hN [])) rfl

/-- **El ensamblaje**: de «cada elemento es un nodo válido» a `wfAll`. -/
theorem prf_wfAll_objList (L : List Term)
    (hcl : ∀ s : Term, substTerm 0 s (objList L) = objList L)
    (hlift : liftTerm 0 (objList L) = objList L)
    (h : ∀ (k : Nat) (x : Term), L[k]? = some x → Prf (nodeOk (objList L) x)) :
    Prf (wfAll (objList L)) := by
  let w : Term := objList L
  let Φ : Formula := nodeOk w (nthc w (.var 0))
  have hsub : ∀ s : Term, substFormula 0 s Φ = nodeOk w (nthc w s) := by
    intro s
    simp only [Φ, w, nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor,
      In, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      substTerm_numeralM, hcl, if_true]
  have hΦ : substFormula 0 (.var 0) Φ = Φ := hsub (.var 0)
  have hinst : ∀ k : Nat, k < L.length → Prf (substFormula 0 (numeralM k) Φ) := by
    intro k hk
    rw [hsub]
    obtain ⟨x, hx⟩ : ∃ x, L[k]? = some x := ⟨L[k], getElem?_pos L k hk⟩
    exact prf_congr_nodeOk (prf_eq_symm (prf_nthc_objList L k x hx)) (h k x hx)
  have key : Prf (Formula.forall (Formula.impl (lt (.var 0) (numeralM L.length)) Φ)) :=
    prf_bdAll_numeral Φ hΦ L.length hinst
  have hself : substFormula 0 (.var 0) (Formula.impl (lt (.var 0) (numeralM L.length)) Φ)
      = Formula.impl (lt (.var 0) (numeralM L.length)) Φ := by
    simp only [substFormula, lt, substTerm, substTerms, substTerm_numeralM, hΦ, if_true]
  have hlift2 : liftTerm 0 (lenc (objList L)) = lenc (objList L) := by
    simp only [lenc, liftTerm, liftTerms, hlift]
  refine Prf.gen _ (prf_deduction ?_)
  rw [hlift2, hlift]
  exact PrfH.mp _ _ _ (prf_to_prfH (hself ▸ prf_spec key (.var 0)) _)
    (ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (prf_to_prfH (prf_lenc_objList L) _) (PrfH.hyp _ _ (List.Mem.head _)))

/-- Especialización lista para el hito (i): las dos clausuras salen solas. -/
theorem prf_wfAll_subCodes (φ : Formula)
    (h : ∀ (k : Nat) (x : Term), (subCodes φ)[k]? = some x →
      Prf (nodeOk (objList (subCodes φ)) x)) :
    Prf (wfAll (objList (subCodes φ))) :=
  prf_wfAll_objList (subCodes φ)
    (fun s => substTerm_objList_subCodes 0 s φ) (liftTerm_objList_subCodes 0 φ) h

/-- Y de ahí a `isFCB`, usando que la CABEZA del testigo es el propio código. -/
theorem prf_isFCB_of_wfAll (φ : Formula) (hwf : Prf (wfAll (objList (subCodes φ)))) :
    Prf (isFCB (objList (subCodes φ)) (formCodeM φ)) :=
  prf_and_intro hwf (prf_In_objList _ _ (mem_self_subCodes φ))

/-! ## 9 · SMOKE TEST — el prelude COMPONE de verdad (caso `⊥`, extremo a extremo)

    No es la inducción principal (eso es de otro): es la comprobación de que los seis
    interfaces de arriba encajan sin fricción, y de que la enmienda `consOk` se descarga
    sola sobre un nodo real (`prf_consOk_cons`). -/

/-- El nodo `formCodeM ⊥ = cons 2̄ nil` cae en el disyunto 1 (`cOk X (nulOk X 2)`). -/
theorem prf_nodeOk_bot (w : Term) : Prf (nodeOk w (formCodeM Formula.bottom)) := by
  have htag : Prf (Formula.eq (carc (formCodeM Formula.bottom)) (numeralM 2)) :=
    prf_carc_cons (numeralM 2) nil
  have hlen : Prf (Formula.eq (lenc (formCodeM Formula.bottom)) (numeralM 1)) :=
    prf_eq_trans (prf_lenc_cons (numeralM 2) nil) (prf_eq_congr_succ prf_lenc_nil)
  have hnul : Prf (cOk (formCodeM Formula.bottom) (nulOk (formCodeM Formula.bottom) 2)) :=
    prf_and_intro (prf_consOk_cons (numeralM 2) nil) (prf_and_intro htag hlen)
  unfold nodeOk lorAll
  exact prf_mp (Prf.incl (Prfᵢ.j1 _ _)) hnul

theorem prf_isFCB_subCodes_bottom :
    Prf (isFCB (objList (subCodes Formula.bottom)) (formCodeM Formula.bottom)) := by
  refine prf_isFCB_of_wfAll _ (prf_wfAll_subCodes _ ?_)
  intro k x hk
  cases k with
  | zero =>
      simp only [subCodes, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact prf_nodeOk_bot _
  | succ n => simp [subCodes] at hk

end SubCodesPrelude

#print axioms SubCodesPrelude.prf_cdrc_cons
#print axioms SubCodesPrelude.prf_consOk_cons
#print axioms SubCodesPrelude.closed_mem_subCodes
#print axioms SubCodesPrelude.liftTerm_objList_subCodes
#print axioms SubCodesPrelude.substTerm_objList_subCodes
#print axioms SubCodesPrelude.prf_lenc_objList
#print axioms SubCodesPrelude.prf_nthc_objList
#print axioms SubCodesPrelude.prf_In_objList
#print axioms SubCodesPrelude.prf_bdAll_numeral
#print axioms SubCodesPrelude.PrfH_congr_nodeOk
#print axioms SubCodesPrelude.prf_wfAll_objList
#print axioms SubCodesPrelude.prf_wfAll_subCodes
#print axioms SubCodesPrelude.prf_isFCB_of_wfAll
#print axioms SubCodesPrelude.prf_nodeOk_bot
#print axioms SubCodesPrelude.prf_isFCB_subCodes_bottom
