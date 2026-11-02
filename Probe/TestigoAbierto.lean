/- (c) — ¿hace falta de verdad que el TESTIGO sea CERRADO?

   Hipótesis a refutar: los teoremas de `ParticionDiscrimina` piden
       hpl : ∀ m, liftTerm m p = p      hps : ∀ v s, substTerm v s p = p
   y un testigo salido de un `∃` OBJETO es `#0`, que NO las cumple
   (`liftTerm 0 #0 = #1`). De ahí la propuesta de meterlo en una CASILLA — que
   colisiona con `lenc = 3` de `ind`/`listInd`.

   OBSERVACIÓN QUE MOTIVA ESTE PROBE: la DEFINICIÓN ya lleva el lift explícito

       wfAllT p := ∀. (#0 < ↑(bndT p)) ⇒ isTermCodeB ↑(carc p) ↑(cdrc p) (nthc ↑(carc p) #0)

   La clausura NO la pide la definición: sólo la usa `wfAllT_closed`, que es una
   NORMALIZACIÓN de conveniencia para que disparen los `simp`. Y al instanciar,
   `substTerm 0 k (liftTerm 0 x) = x` es `FOL.substTerm_liftTerm`, que vale para
   CUALQUIER `x`, cerrado o no.

   ⇒ mido si el lado CONSUMO sale con `p` ABSTRACTO y CERO hipótesis.

   ## ✅ RESULTADO: SÍ. Los cuatro teoremas de abajo son **net‑0**, con `p` y `k` ABSTRACTOS y
   **cero hipótesis** — incluidos el caso `p := #0` (el testigo real del `∃`‑elim, que NO es
   cerrado) y la versión `PrfH`, que es donde vive tras el `∃`‑elim.

   ⇒ **la clausura NO es un requisito del enunciado: es un artefacto de la RUTA DE PRUEBA.**
   `wfAllT_closed` existe sólo para quitar los lifts y que disparen los `simp`; si en vez de
   quitarlos se LLEVAN, `FOL.substTerm_liftTerm` hace el trabajo para cualquier `p`.

   ## ⚠️ ALCANCE — lo que esto NO demuestra
   Mide el **primer** paso del consumo (la instanciación), que es donde se creía que estaba la
   obstrucción. La cadena entera de `crit_In_rejects_of_pairOk`
   (`sondeos/ParticionDiscrimina.lean:2847`) usa la clausura en **otros dos sitios**, y son
   del MISMO tipo (normalizar el lift interno de `boundedIn`, y `hAs`/`hBs` para `crit_spec_body`)
   — o sea la misma maniobra repetida, **pero no está compilada**. -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.ChainPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace TestigoAbierto

/-! ## 1 · Las definiciones, copiadas LITERALES de `sondeos/ParticionDiscrimina.lean` -/

def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))
def cOk (X : Term) (F : Formula) : Formula := land (consOk X) F

def varOkT (X : Term) : Formula :=
  land (Formula.eq (carc X) (numeralM 0)) (Formula.eq (lenc X) (numeralM 2))

def funcOkT (wTs X : Term) : Formula :=
  land (land (Formula.eq (carc X) (numeralM 1)) (Formula.eq (lenc X) (numeralM 3)))
       (In (nthc X (numeralM 2)) wTs)

def isTermCodeB (wT wTs X : Term) : Formula :=
  lor (cOk X (varOkT X)) (cOk X (funcOkT wTs X))

def isTermsCodeB (wT wTs X : Term) : Formula :=
  lor (Formula.eq X nil)
      (cOk X (land (In (carc X) wT) (In (cdrc X) wTs)))

def bndT  (p : Term) : Term := lenc (carc p)
def bndTs (p : Term) : Term := lenc (cdrc p)

def wfAllT (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndT p)))
    (isTermCodeB (liftTerm 0 (carc p)) (liftTerm 0 (cdrc p))
      (nthc (liftTerm 0 (carc p)) (.var 0))))

def wfAllTs (p : Term) : Formula :=
  Formula.forall (Formula.impl (lt (.var 0) (liftTerm 0 (bndTs p)))
    (isTermsCodeB (liftTerm 0 (carc p)) (liftTerm 0 (cdrc p))
      (nthc (liftTerm 0 (cdrc p)) (.var 0))))

def pairOk (p : Term) : Formula := land (wfAllT p) (wfAllTs p)

/-! ## 2 · EL EXPERIMENTO — instanciar con `p` y `k` ABSTRACTOS, SIN hipótesis

    Si esto compila, el lado CONSUMO **nunca necesitó** la clausura: le basta
    `FOL.substTerm_liftTerm`. -/

/-- **(c) — instanciación del testigo ABIERTO.** `p` y `k` abstractos, **cero hipótesis**. -/
theorem inst_wfAllT_open (p k : Term) (h : Prf (wfAllT p)) :
    Prf (Formula.impl (lt k (bndT p))
      (isTermCodeB (carc p) (cdrc p) (nthc (carc p) k))) := by
  have hi := prf_spec h k
  simpa only [wfAllT, bndT, isTermCodeB, cOk, consOk, varOkT, funcOkT, lt, lenc, carc, cdrc,
    nthc, land, lor, In, cons, nil, zero, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, substTerm_numeralM, if_true] using hi

/-- Gemela para la mitad de LISTAS. -/
theorem inst_wfAllTs_open (p k : Term) (h : Prf (wfAllTs p)) :
    Prf (Formula.impl (lt k (bndTs p))
      (isTermsCodeB (carc p) (cdrc p) (nthc (cdrc p) k))) := by
  have hi := prf_spec h k
  simpa only [wfAllTs, bndTs, isTermsCodeB, cOk, consOk, lt, lenc, carc, cdrc,
    nthc, land, lor, In, cons, nil, zero, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, substTerm_numeralM, if_true] using hi

/-- **El caso de uso REAL**: el testigo salido de un `∃` objeto es `#0`, que NO es cerrado
    (`liftTerm 0 #0 = #1`). Aquí se instancia igualmente. -/
theorem inst_wfAllT_var0 (k : Term) (h : Prf (wfAllT (.var 0))) :
    Prf (Formula.impl (lt k (bndT (.var 0)))
      (isTermCodeB (carc (.var 0)) (cdrc (.var 0)) (nthc (carc (.var 0)) k))) :=
  inst_wfAllT_open (.var 0) k h

/-- Y en `PrfH`, que es donde vive tras el `∃`-elim. -/
theorem PrfH_inst_wfAllT_open {Γ : List Formula} (p k : Term) (h : PrfH Γ (wfAllT p)) :
    PrfH Γ (Formula.impl (lt k (bndT p))
      (isTermCodeB (carc p) (cdrc p) (nthc (carc p) k))) := by
  have hi := PrfH_spec h k
  simpa only [wfAllT, bndT, isTermCodeB, cOk, consOk, varOkT, funcOkT, lt, lenc, carc, cdrc,
    nthc, land, lor, In, cons, nil, zero, substFormula, substTerm, substTerms,
    FOL.substTerm_liftTerm, substTerm_numeralM, if_true] using hi

/-- ⚠️ CONTRASTE: `#0` NO es cerrado. Esto documenta que el probe de arriba
    **no** está esquivando el problema por la puerta de atrás. -/
example : liftTerm 0 (Term.var 0) ≠ Term.var 0 := by decide

end TestigoAbierto

#print axioms TestigoAbierto.inst_wfAllT_open
#print axioms TestigoAbierto.inst_wfAllTs_open
#print axioms TestigoAbierto.inst_wfAllT_var0
#print axioms TestigoAbierto.PrfH_inst_wfAllT_open
