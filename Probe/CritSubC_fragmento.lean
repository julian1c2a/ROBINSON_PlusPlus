/-
VERIFICACION ADVERSARIAL de Probe/SubC_fragmento.lean.

Tres pruebas independientes:
 (A) Las defs OBJETO elaboradas bajo el open-set de A3IsFCBTracked y bajo el open-set del
     Probe son el MISMO termino (rfl). Texto identico NO implica termino identico: los
     open-set difieren, y `In`/`land`/`lor` son notacion scoped.
 (B) subCodes de un phi con ATOMO y FUNCION contiene EXACTAMENTE lo que las pertenencias
     exigen, y `nil` esta dentro.
 (C) El disyunto 10 va DESNUDO: `Formula.eq X nil`, sin consOk.
-/
import ROBINSON_PlusPlus.Meta

/-! ## Lado A3 — open-set LITERAL de sondeos/A3IsFCBTracked.lean -/
section A3side
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.EvalListPrf ROBINSON_PlusPlus.Meta.EvalNthcPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.InAxiomsCodePrf ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.D3InDotPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.MpCodePrf

namespace A3ns

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

def lorAll : Formula → List Formula → Formula
  | a, []      => a
  | a, b :: bs => lor a (lorAll b bs)

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def nodeOk (w X : Term) : Formula :=
  lorAll (cOk X (nulOk X 2))
    [ cOk X (strBinOk w X 3)
    , cOk X (binOk w X 4)
    , cOk X (binOk w X 5)
    , cOk X (unOk  w X 6)
    , cOk X (binOk w X 7)
    , cOk X (binOk w X 8)
    , cOk X (unOk  w X 9)
    , cOk X (varOk X)
    , cOk X (strBinOk w X 1)
    , Formula.eq X nil
    , cOk X (land (In (carc X) w) (In (cdrc X) w)) ]

def wfAll (w : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (lenc w)))
    (nodeOk (liftTerm 0 w) (nthc (liftTerm 0 w) (.var 0))))

def isFCB (w c : Term) : Formula := land (wfAll w) (In c w)

end A3ns
end A3side

/-! ## Lado PROBE — open-set LITERAL de Probe/SubC_fragmento.lean -/
section Pside
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.NumListPrf ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf

namespace Pns

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

end Pns
end Pside

/-! ## (A) LAS DEFS SON EL MISMO TERMINO pese a los open-set distintos -/
section Comparacion
open ROBINSON_PlusPlus.Minimal.Axioms

example : A3ns.nulOk    = Pns.nulOk    := rfl
example : A3ns.unOk     = Pns.unOk     := rfl
example : A3ns.binOk    = Pns.binOk    := rfl
example : A3ns.strBinOk = Pns.strBinOk := rfl
example : A3ns.varOk    = Pns.varOk    := rfl
example : A3ns.consOk   = Pns.consOk   := rfl
example : A3ns.cOk      = Pns.cOk      := rfl
-- `lorAll` es recursiva: dos compilaciones separadas no son defeq COMO FUNCION, pero sí
-- punto a punto sobre listas literales, que es el uso real. La prueba que importa es la
-- de `nodeOk` APLICADO: ahí la disyunción ya está desplegada.
example (a b : Formula) (l : List Formula) :
    A3ns.lorAll a (b :: l) = lor a (A3ns.lorAll b l) := rfl
example (a b : Formula) (l : List Formula) :
    Pns.lorAll a (b :: l) = lor a (Pns.lorAll b l) := rfl
example (w X : Term) : A3ns.nodeOk w X = Pns.nodeOk w X := rfl
example (w : Term)    : A3ns.wfAll w   = Pns.wfAll w   := rfl
example (w c : Term)  : A3ns.isFCB w c = Pns.isFCB w c := rfl

/-! ## (C) El disyunto 10 va DESNUDO -/
example (w X : Term) :
    A3ns.nodeOk w X
      = lor (A3ns.cOk X (A3ns.nulOk X 2))
        (lor (A3ns.cOk X (A3ns.strBinOk w X 3))
        (lor (A3ns.cOk X (A3ns.binOk w X 4))
        (lor (A3ns.cOk X (A3ns.binOk w X 5))
        (lor (A3ns.cOk X (A3ns.unOk w X 6))
        (lor (A3ns.cOk X (A3ns.binOk w X 7))
        (lor (A3ns.cOk X (A3ns.binOk w X 8))
        (lor (A3ns.cOk X (A3ns.unOk w X 9))
        (lor (A3ns.cOk X (A3ns.varOk X))
        (lor (A3ns.cOk X (A3ns.strBinOk w X 1))
        (lor (Formula.eq X nil)                      -- ← DESNUDO, sin cOk
             (A3ns.cOk X (land (In (carc X) w) (In (cdrc X) w))))))))))))) := rfl

end Comparacion

/-! ## (B) EL TESTIGO CONCRETO para `phi = P(f(x0))` -/
section Concreto
open ROBINSON_PlusPlus.Minimal.Axioms

/-- `x0`, `f(x0)`, `P(f(x0))`. -/
def tv : Term := Term.var 0
def tf : Term := Term.func "f" [tv]
def phi : Formula := Formula.atom "P" [tf]

/-- El testigo tiene EXACTAMENTE 7 casillas, y son estas. -/
example : Pns.subCodes phi =
  [ formCodeM phi              -- 0
  , termsCodeM [tf]            -- 1
  , termCodeM tf               -- 2
  , termsCodeM [tv]            -- 3
  , termCodeM tv               -- 4
  , nil                        -- 5
  , nil ] := rfl               -- 6

/-! Ahora, casilla a casilla, la FORMA del codigo y lo que el disyunto EXIGE. -/

-- casilla 0: tag 3, lenc 3 ⇒ strBinOk 3 exige `In (nthc X 2) w`.
example : formCodeM phi = cons (numeralM 3) (cons (strCodeM "P") (cons (termsCodeM [tf]) nil)) :=
  rfl
-- ⇒ lo exigido es `termsCodeM [tf]`, que es la casilla 1:
example : List.Mem (termsCodeM [tf]) (Pns.subCodes phi) := by
  simp only [show Pns.subCodes phi = [formCodeM phi, termsCodeM [tf], termCodeM tf,
    termsCodeM [tv], termCodeM tv, nil, nil] from rfl]
  exact List.Mem.tail _ (List.Mem.head _)

-- casilla 1: es un `cons` ⇒ disyunto 12 exige `In (carc X) w` y `In (cdrc X) w`.
example : termsCodeM [tf] = cons (termCodeM tf) nil := rfl
-- ⇒ exige `termCodeM tf` (casilla 2) y `nil` (casillas 5,6):
example : List.Mem (termCodeM tf) (Pns.subCodes phi) := by
  simp only [show Pns.subCodes phi = [formCodeM phi, termsCodeM [tf], termCodeM tf,
    termsCodeM [tv], termCodeM tv, nil, nil] from rfl]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
example : List.Mem nil (Pns.subCodes phi) := by
  simp only [show Pns.subCodes phi = [formCodeM phi, termsCodeM [tf], termCodeM tf,
    termsCodeM [tv], termCodeM tv, nil, nil] from rfl]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.head _)))))

-- casilla 2: tag 1, lenc 3 ⇒ strBinOk 1 exige `In (nthc X 2) w` = `termsCodeM [tv]`.
example : termCodeM tf = cons (numeralM 1) (cons (strCodeM "f") (cons (termsCodeM [tv]) nil)) :=
  rfl
example : List.Mem (termsCodeM [tv]) (Pns.subCodes phi) := by
  simp only [show Pns.subCodes phi = [formCodeM phi, termsCodeM [tf], termCodeM tf,
    termsCodeM [tv], termCodeM tv, nil, nil] from rfl]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

-- casilla 3: `cons` ⇒ disyunto 12 exige `termCodeM tv` (casilla 4) y `nil`.
example : termsCodeM [tv] = cons (termCodeM tv) nil := rfl
example : List.Mem (termCodeM tv) (Pns.subCodes phi) := by
  simp only [show Pns.subCodes phi = [formCodeM phi, termsCodeM [tf], termCodeM tf,
    termsCodeM [tv], termCodeM tv, nil, nil] from rfl]
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

-- casilla 4: tag 0, lenc 2 ⇒ varOk NO exige ninguna pertenencia (la casilla 1 es un NUMERAL).
example : termCodeM tv = cons (numeralM 0) (cons (numeralM 0) nil) := rfl

-- casillas 5,6: `nil` ⇒ SOLO el disyunto 10 (DESNUDO) lo cubre.
-- Que `consOk nil` es REFUTABLE lo prueba la teoria objeto: nil ≠ cons a b.
example : Pns.consOk nil = Formula.eq nil (cons (carc nil) (cdrc nil)) := rfl

end Concreto
