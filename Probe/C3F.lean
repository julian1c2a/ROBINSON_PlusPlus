import ROBINSON_PlusPlus.Meta.HasWitTrackedPrf
/-!
# SONDA C3-F — ¿es ésta la imagen que `formCode`/`substCodeF` producen?

La regla de §3.44: **casar la imagen con el destino por `rfl` ANTES de construir sobre ella**.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf ROBINSON_PlusPlus.Meta.Sigma1CorePrf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.TrackedAtomsPrf
open ROBINSON_PlusPlus.Meta.ChainPrf ROBINSON_PlusPlus.Meta.BdAllIntroPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.EvalNthcPrf ROBINSON_PlusPlus.Meta.EvalListPrf
open ROBINSON_PlusPlus.Meta.EvalLtPrf ROBINSON_PlusPlus.Meta.EvalBoundedPrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.HasWitTrackedPrf

namespace ProbeC3F

/-! ## §0 · La forma NULARIA, que C3-T no necesitó -/

noncomputable def shapeFCnul (ND : Term) (k : Nat) : Term := eqCodeFn ND (nulT k)

example (X : Term) (k : Nat) : formCode (shapeNul X k) = shapeFCnul (termCode X) k := rfl

/-! ## §1 · Las OCHO cláusulas, como imágenes -/

noncomputable def clBotFC (NY : Term) : Term := shapeFCnul NY 2

/-- Sirve para `clBin` (k = 5,7,8) **y para `clEq`** (k = 4, con `W := wT`): son la misma forma. -/
noncomputable def clBinFC (NY W : Term) (k : Nat) : Term :=
  andc (shapeFCbin NY k)
       (andc (inFormCodeFn (nthcT NY (termCode (numeralM 1))) W)
             (inFormCodeFn (nthcT NY (termCode (numeralM 2))) W))

noncomputable def clUnFC (NY W : Term) (k : Nat) : Term :=
  andc (shapeFCun NY k) (inFormCodeFn (nthcT NY (termCode (numeralM 1))) W)

noncomputable def clAtomFC (NY A WT' : Term) : Term :=
  andc (shapeFCbin NY 3) (argsInDotC A WT')

/-- El cuerpo del `∀` acotado de `wfAllF`, con **cuatro** ranuras de testigo (`wF` y `wT`, cada
    uno a su nivel dentro y fuera del `argsIn` de `clAtom`) y **dos** del índice. -/
noncomputable def isFCE2PsiAtC (WF WT WF' WT' s s' : Term) : Term :=
  orc (clBotFC (nthcT WF s))
   (orc (clAtomFC (nthcT WF s) (nthcT (nthcT WF' s') (termCode (numeralM 2))) WT')
    (orc (clBinFC (nthcT WF s) WT 4)
     (orc (clBinFC (nthcT WF s) WF 5)
      (orc (clUnFC (nthcT WF s) WF 6)
       (orc (clBinFC (nthcT WF s) WF 7)
        (orc (clBinFC (nthcT WF s) WF 8) (clUnFC (nthcT WF s) WF 9)))))))

noncomputable def wfAllFDotAtC (WF WT WF' WT' : Term) : Term :=
  bdAllCode (lencT WF)
    (isFCE2PsiAtC WF WT WF' WT' (varc (numeral 0)) (varc (numeral 1)))

/-- El cuerpo del `∃∃`: `wF` es `⌜v₁⌝` y `wT` es `⌜v₀⌝`. -/
noncomputable def hasWitFAc (T I : Term) : Term :=
  andc (andc (wfAll1DotAtC (varc (numeral 1)) (varc (numeral 2)))
             (wfAllFDotAtC (varc (numeral 2)) (varc (numeral 1))
                           (varc (numeral 3)) (varc (numeral 2))))
       (inFormCodeFn (nthcT T I) (varc (numeral 1)))

/-! ## §2 · ⭐ LA COMPROBACIÓN QUE DECIDE: ¿es ésta la imagen de `substCodeF`? -/

example (t I : Term) :
    substCodeF 0 (tcFn t) (hasWitF (nthc (.var 0) I))
      = exc (exc (hasWitFAc (liftc zero (liftc zero (tcFn t)))
                    (substCodeT 2 (liftc zero (liftc zero (tcFn t)))
                      (liftTerm 0 (liftTerm 0 I))))) := rfl

/-! ## §3 · Y las piezas sueltas, también casadas -/

example (wF wT X : Term) :
    formCode (clEq wT X) = clBinFC (termCode X) (termCode wT) 4 := rfl

example (wF X : Term) (k : Nat) :
    formCode (clBin wF X k) = clBinFC (termCode X) (termCode wF) k := rfl

example (wF X : Term) (k : Nat) :
    formCode (clUn wF X k) = clUnFC (termCode X) (termCode wF) k := rfl

example (X : Term) : formCode (clBot X) = clBotFC (termCode X) := rfl

end ProbeC3F
