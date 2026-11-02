/-
# CRITICA ADVERSARIAL de Probe/SubC_mutua.lean
Verificador independiente. NO modifica SubC_mutua.lean.
Contesta la pregunta 5 (SATISFACIBILIDAD) con el COMPILADOR, no con prosa.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf

namespace CritSubC

/-! ## 1 · Copias LITERALES (mismas que el fichero auditado) -/

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

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

/-! ## 2 · ⚠️ LA TRAMPA DE A3 ES REAL Y ESTA EVITADA

El caso `subCodesTs [] = [nil]` produce el nodo `nil`. Si el disyunto 10 llevara
`cOk` (o sea `consOk`), ese caso pediria probar `consOk nil`. Demostramos que la
teoria objeto lo REFUTA, y que asumirlo COLAPSA la teoria. -/

theorem crit_refuta_consOk_nil : axioms ⊢ neg (consOk nil) :=
  ROBINSON_PlusPlus.Meta.CodeDistinct.nil_ne_cons (carc nil) (cdrc nil)

/-- Si alguien "reforzara" el disyunto 10 con `consOk`, la teoria probaria ⊥.
    Esto es EXACTAMENTE lo que mato a los dos intentos previos de A3. -/
theorem crit_trampa_colapsa (h : Prf (consOk nil)) : axioms ⊢ Formula.bottom :=
  mp crit_refuta_consOk_nil (prf_to_derives h)

/-! ## 3 · El testigo, DESPLEGADO, para el phi que pide el encargo -/

def phi : Formula := Formula.atom "P" [Term.func "f" [Term.var 0]]

/-- Las 7 casillas, en orden. `rfl` = cierto por computo. -/
theorem crit_testigo_desplegado : subCodes phi =
    [ formCodeM phi                                   -- 0 : codigo de phi
    , termsCodeM [Term.func "f" [Term.var 0]]         -- 1 : lista de args
    , termCodeM (Term.func "f" [Term.var 0])          -- 2 : f(#0)
    , termsCodeM [Term.var 0]                         -- 3 : lista [#0]
    , termCodeM (Term.var 0)                          -- 4 : #0
    , nil                                             -- 5 : cola de [#0]
    , nil ] := rfl                                    -- 6 : cola de los args

/-! ## 4 · CADA casilla que un disyunto exige `In _ w` ESTA en el testigo.

* nodo 0 (`formCodeM phi`, tag 3 = strBinOk) exige `In (nthc X 2) w` = lista de args.
* nodo 1 (`termsCodeM [f #0]`, disyunto 12)  exige `In (carc X) w` y `In (cdrc X) w`.
* nodo 2 (`termCodeM (f #0)`, tag 1 = strBinOk) exige `In (nthc X 2) w` = `termsCodeM [#0]`.
* nodo 3 (`termsCodeM [#0]`, disyunto 12)    exige `In (carc X) w` y `In (cdrc X) w`.
* nodo 4 (`termCodeM #0`, tag 0 = varOk)     no exige nada.
* nodos 5,6 (`nil`, disyunto 10 DESNUDO)     no exige nada.  <-- CLAVE -/

def W : List Term := subCodes phi

-- lista de args (la exige el nodo 0 via nthc X 2)
theorem crit_mem_args : List.Mem (termsCodeM [Term.func "f" [Term.var 0]]) W :=
  List.Mem.tail _ (List.Mem.head _)

-- carc del nodo 1  (= termCodeM (f #0))
theorem crit_mem_carc1 : List.Mem (termCodeM (Term.func "f" [Term.var 0])) W :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

-- cdrc del nodo 1  (= termsCodeM [] = nil), y tambien el nodo nil mismo
theorem crit_mem_nil : List.Mem nil W :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.head _)))))

-- lista [#0] (la exige el nodo 2 via nthc X 2)
theorem crit_mem_args2 : List.Mem (termsCodeM [Term.var 0]) W :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

-- carc del nodo 3 (= termCodeM #0)
theorem crit_mem_var : List.Mem (termCodeM (Term.var 0)) W :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-! ## 5 · `nil` ES el cdrc de las colas: el disyunto 10 es OBLIGATORIO. -/

theorem crit_cola_es_nil : termsCodeM ([] : List Term) = nil := rfl

theorem crit_cdrc_nodo1 :
    cdrc (termsCodeM [Term.func "f" [Term.var 0]])
  = cdrc (cons (termCodeM (Term.func "f" [Term.var 0])) nil) := rfl

end CritSubC

#print axioms CritSubC.crit_refuta_consOk_nil
#print axioms CritSubC.crit_trampa_colapsa
#print axioms CritSubC.crit_testigo_desplegado
#print axioms CritSubC.crit_mem_nil

-- longitudes que el fichero auditado declara: 1, 3, 7
#eval (CritSubC.subCodes Formula.bottom).length
#eval (CritSubC.subCodes (Formula.eq (.var 0) (.var 1))).length
#eval (CritSubC.subCodes CritSubC.phi).length
