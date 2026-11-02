/-
# CRITICA ADVERSARIAL de Probe/SubC_porforma.lean

Objetivo: refutar, si se puede, la afirmacion de que el hito (i) esta cerrado.
Se re-declaran las definiciones (copia literal) para poder razonar sobre ellas
sin importar el fichero auditado.

    lake env lean Probe\CritSubC_porforma.lean
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf

namespace CritPF

/-! ## 1 · Re-declaracion literal de las definiciones auditadas -/

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

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

/-! ## 2 · ⚠️ LA TRAMPA ES REAL: la teoria objeto REFUTA `consOk nil`.

    Si el disyunto 10 llevara `cOk`, el nodo `nil` seria IMPOSIBLE, y como `nil` es
    obligatorio en todo testigo con lista de argumentos (`termsCodeM [] = nil`),
    `wfAll` se quedaria sin testigos. Confirma que la forma DESNUDA es obligatoria. -/

theorem consOk_nil_refutable : axioms ⊢ neg (consOk nil) :=
  nil_ne_cons (carc nil) (cdrc nil)

/-! ## 3 · El caso concreto que pide el encargo: φ = atom "P" [func "f" [var 0]] -/

def phi : Formula := Formula.atom "P" [Term.func "f" [Term.var 0]]

/-- La lista de sub-codigos, calculada. Se comprueba por `rfl`: si `subCodes`
    olvidara cualquier casilla, esta igualdad fallaria. -/
theorem subCodes_phi_explicit :
    subCodes phi =
      [ formCodeM phi                                    -- 0 : atom  (tag 3)
      , termsCodeM [Term.func "f" [Term.var 0]]          -- 1 : lista (cons)
      , termCodeM (Term.func "f" [Term.var 0])           -- 2 : func  (tag 1)
      , termsCodeM [Term.var 0]                          -- 3 : lista (cons)
      , termCodeM (Term.var 0)                           -- 4 : var   (tag 0)
      , nil                                              -- 5 : nil   (DESNUDO)
      , nil ] := rfl                                     -- 6 : nil   (duplicado, inocuo)

/-! ### 3.1 · CADA pertenencia que un disyunto exige ESTA en la lista.

    Se lee el tag de `formCodeM`/`termCodeM`/`termsCodeM` y se comprueba que la
    casilla que el disyunto correspondiente pide bajo `In … w` es miembro. -/

/-- Nodo 0 = `cons 3̄ (cons ⌜"P"⌝ (cons (termsCodeM ts) nil))` ⇒ `strBinOk` pide
    la casilla 2, que es `termsCodeM ts`. Esta en la lista. -/
theorem demand_0 : List.Mem (termsCodeM [Term.func "f" [Term.var 0]]) (subCodes phi) := by
  rw [subCodes_phi_explicit]; exact List.Mem.tail _ (List.Mem.head _)

/-- Nodo 1 = `cons (termCodeM f[v0]) nil` ⇒ el disyunto `cons` pide `carc` y `cdrc`,
    o sea `termCodeM f[v0]` y `nil`. Ambos estan. -/
theorem demand_1a : List.Mem (termCodeM (Term.func "f" [Term.var 0])) (subCodes phi) := by
  rw [subCodes_phi_explicit]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem demand_1b : List.Mem nil (subCodes phi) := by
  rw [subCodes_phi_explicit]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

/-- Nodo 2 = `cons 1̄ (cons ⌜"f"⌝ (cons (termsCodeM [v0]) nil))` ⇒ `strBinOk` pide
    la casilla 2 = `termsCodeM [v0]`. Esta. -/
theorem demand_2 : List.Mem (termsCodeM [Term.var 0]) (subCodes phi) := by
  rw [subCodes_phi_explicit]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Nodo 3 = `cons (termCodeM v0) nil` ⇒ pide `termCodeM v0` y `nil`. Ambos estan. -/
theorem demand_3a : List.Mem (termCodeM (Term.var 0)) (subCodes phi) := by
  rw [subCodes_phi_explicit]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- Nodo 4 = `termCodeM (var 0) = cons 0̄ (cons 0̄ nil)` ⇒ `varOk`, NO pide pertenencias. -/
theorem node_4_shape : termCodeM (Term.var 0) = cons (numeralM 0) (cons (numeralM 0) nil) := rfl

/-- Nodo 5 = `nil` ⇒ disyunto 10, DESNUDO, se cierra con `prf_refl nil`. -/
theorem node_5_ok : Prf (Formula.eq nil nil) := prf_refl nil

/-! ### 3.2 · Los tags son los que el inyector supone (si no, §D estaria mal enchufado) -/

theorem tag_atom : formCodeM phi
    = cons (numeralM 3) (cons (strCodeM "P") (cons (termsCodeM [Term.func "f" [Term.var 0]]) nil)) := rfl
theorem tag_func : termCodeM (Term.func "f" [Term.var 0])
    = cons (numeralM 1) (cons (strCodeM "f") (cons (termsCodeM [Term.var 0]) nil)) := rfl
theorem tag_termsCons : termsCodeM [Term.func "f" [Term.var 0]]
    = cons (termCodeM (Term.func "f" [Term.var 0])) nil := rfl
theorem tag_termsNil : termsCodeM ([] : List Term) = nil := rfl

/-! ## 4 · La lista es CERRADA por sub-codigos: no falta nada.

    Formulacion general: todo `x ∈ subCodes φ` que sea un `cons` tiene sus
    sub-codigos exigidos tambien en la lista. Se comprueba aqui el caso φ concreto
    de forma exhaustiva enumerando las 7 casillas. -/

theorem closure_phi : ∀ x : Term, List.Mem x (subCodes phi) →
    List.Mem x [ formCodeM phi
               , termsCodeM [Term.func "f" [Term.var 0]]
               , termCodeM (Term.func "f" [Term.var 0])
               , termsCodeM [Term.var 0]
               , termCodeM (Term.var 0)
               , nil, nil ] := by
  intro x hx; rw [subCodes_phi_explicit] at hx; exact hx

/-! ## 5 · `nil` es nodo VALIDO y NO necesita ser `cons` (contraste con §2) -/

/-- El disyunto desnudo se satisface para `nil`. -/
theorem nil_is_node : Prf (Formula.eq nil nil) := prf_refl nil

end CritPF

#print axioms CritPF.consOk_nil_refutable
#print axioms CritPF.subCodes_phi_explicit
#print axioms CritPF.demand_0
#print axioms CritPF.demand_1a
#print axioms CritPF.demand_1b
#print axioms CritPF.demand_2
#print axioms CritPF.demand_3a
#print axioms CritPF.tag_atom
#print axioms CritPF.tag_func
#print axioms CritPF.closure_phi
#print axioms CritPF.nil_is_node
