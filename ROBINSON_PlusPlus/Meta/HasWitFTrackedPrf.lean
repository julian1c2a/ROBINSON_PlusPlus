import ROBINSON_PlusPlus.Meta.HasWitTrackedPrf
/-!
# `Meta/HasWitFTrackedPrf.lean` — C3‑F: `DEUDA_hGuardF`, la mitad grande de ADR‑020

`Meta/HasWitTrackedPrf.lean` cerró `DEUDA_hGuardT` (§3.44). Queda la otra mitad de la cascada
de ADR‑020: el reflector Σ₁ de **`hasWitF`**, que es estrictamente peor que el de `hasWit`:

| | `hasWit` (C3‑T) | `hasWitF` (C3‑F) |
|---|---|---|
| existenciales | uno | **dos** (`∃wF ∃wT`) |
| listas testigo | una | **dos**, y la de fórmulas se valida **contra** la de términos |
| cláusulas del nodo | 2 (`isTermCodeE1`) | **8** (`isFormCodeE2`) |
| formas posicionales | `shapeUn`, `shapeBin` | `shapeNul`, `shapeUn`, `shapeBin` |
| `∀` acotados | 1 (+1 anidado en `argsIn`) | **2** (`wfAll1` y `wfAllF`) + el anidado |

⭐ **Pero casi todo lo genérico ya está hecho.** De C3‑T se reusan sin tocar:
`pcc_shape_tree` (genérica en el `CTree`), `shapeFCun`/`shapeFCbin` y sus transportes,
`pcc_argsIn_trackedC`, `pcc_wfAll1_trackedC`, `wfAll1DotAtC` con su keystone
`prf_substfc_wfAll1DotAtC` —que aquí encaja **literalmente**, con los mismos `⌜v₁⌝`/`⌜v₂⌝`—,
`pcc_exIntro_code_open` y el gesto `rfl` de la alineación con `condD`.

## ⭐ La regla de §3.44, aplicada ANTES de construir

`condD` **no admite elegir imagen**. Así que lo primero de este módulo (§1) es la comprobación
`rfl` de que la imagen propuesta **es** la que `substCodeF` produce — incluida la estructura del
`∃∃` y las **cuatro** ranuras de testigo (`wF` a nivel `⌜v₁⌝`/`⌜v₂⌝`/`⌜v₃⌝` y `wT` a
`⌜v₀⌝`/`⌜v₁⌝`/`⌜v₂⌝`, según la profundidad de binder). Si `Minimal/Axioms.lean` cambiara
`isFormCodeE2`, esos `example` dejan de compilar.
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
open ROBINSON_PlusPlus.Meta.CodeTreeReflect ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
open ROBINSON_PlusPlus.Meta.HasWitTrackedPrf ROBINSON_PlusPlus.Meta.LineWFGuardPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.LineWFSchemaPrf

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf

/-! ## §0 · LA TERCERA FORMA: `shapeNul`

C3‑T necesitó `shapeUn` y `shapeBin`; `clBot` trae la nularia. Es la misma receta:
`pcc_shape_tree` con el árbol `CTree.nul k`, cuyo `maxLeaf` es 0 (no tiene hojas), así que la
cota de índices es trivial. -/

/-- La imagen `formCode` de `shapeNul`, con el nodo como CÓDIGO. -/
noncomputable def shapeFCnul (ND : Term) (k : Nat) : Term := eqCodeFn ND (nulT k)

/-- El árbol nulario, y la comprobación de que **es** la forma. -/
def treeNul1 (k : Nat) : CTree := .nul k

example (X : Term) (k : Nat) : shapeNul X k = (X =eq (treeNul1 k).objAt X) := rfl
example (X : Term) (k : Nat) : formCode (shapeNul X k) = shapeFCnul (termCode X) k := rfl
example (X : Term) (k : Nat) : (treeNul1 k).dotN X = nulT k := rfl

/-- La forma NULARIA, reflejada a su código `formCode`. -/
theorem pcc_shapeNul_fc (X : Term) (k : Nat) :
    Prf (shapeNul X k ⇒ provFromCode (shapeFCnul (tcFn X) k)) :=
  pcc_shape_tree X (treeNul1 k) (Nat.zero_le 1) _
    (prf_deduction (prfH_hyp_self _))
    (prf_deduction (PrfH_and_elim_right (PrfH_and_elim_right
      (PrfH.mp _ _ _ (prf_to_prfH (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.prf_shapeNul_str X k) _) (prfH_hyp_self _)))))

/-- El contexto de Leibniz con el hueco del nodo a nivel `⌜v₀⌝`. -/
noncomputable def shapeNulCtx (k : Nat) : Term := eqCodeFn (varc (numeral 0)) (nulT k)

theorem prf_substfc_shapeNulCtx (k : Nat) (U : Term) :
    Prf (substfc zero U (shapeNulCtx k) =eq shapeFCnul U k) := by
  unfold shapeNulCtx shapeFCnul
  exact prf_eq_trans (prf_substfc_eq zero U _ _)
    (prf_congr_eqCodeFn (prf_substtc_varc0 U) (prf_substtc_nulT k U))

theorem PrfH_shapeFCnul_transport {Γ : List Formula} (k : Nat) (U U' : Term)
    (hU : PrfH Γ (provFromCode (eqCodeFn U U')))
    (h : PrfH Γ (provFromCode (shapeFCnul U k)))
    (hwC : Prf (hasWitF (shapeNulCtx k)) := by hw_auto)
    (hwU : Prf (hasWit U) := by hw_auto) (hwU' : Prf (hasWit U') := by hw_auto) :
    PrfH Γ (provFromCode (shapeFCnul U' k)) := by
  have h0 : PrfH Γ (provFromCode (substfc zero U (shapeNulCtx k))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
      (prf_eq_symm (prf_substfc_shapeNulCtx k U))) _) h
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_substfc_shapeNulCtx k U')) _)
    (PrfH_leibniz_apply _ U U' hU h0 hwC hwU hwU')

/-- `substfc` sobre la forma NULARIA, a nivel ARBITRARIO (el `nulT` es cerrado). -/
theorem prf_substfc_shapeFCnul_at (v : Nat) (s X X' : Term) (k : Nat)
    (hX : Prf (substtc (numeral v) s X =eq X')) :
    Prf (substfc (numeral v) s (shapeFCnul X k) =eq shapeFCnul X' k) := by
  unfold shapeFCnul nulT consT
  refine prf_eq_trans (prf_substfc_eq _ s _ _) (prf_congr_eqCodeFn hX ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) (prf_congr_funcc2 ?_)
  refine prf_eq_trans (prf_congr_cons_head (prf_substtc_termCode_numeralM v k s)) ?_
  exact prf_congr_cons_tail (prf_congr_cons_head (prf_substtc_termCode_zero v s))

/-! ## §1 · LAS OCHO CLÁUSULAS COMO IMÁGENES — y la comprobación `rfl` contra `formCode` -/

noncomputable def clBotFC (NY : Term) : Term := shapeFCnul NY 2

/-- Sirve para `clBin` (tags 5/7/8) **y para `clEq`** (tag 4, con `W := ẇT`): son la misma
    forma con distinta lista testigo. -/
noncomputable def clBinFC (NY W : Term) (k : Nat) : Term :=
  andc (shapeFCbin NY k)
       (andc (inFormCodeFn (nthcT NY (termCode (numeralM 1))) W)
             (inFormCodeFn (nthcT NY (termCode (numeralM 2))) W))

noncomputable def clUnFC (NY W : Term) (k : Nat) : Term :=
  andc (shapeFCun NY k) (inFormCodeFn (nthcT NY (termCode (numeralM 1))) W)

noncomputable def clAtomFC (NY A WT : Term) : Term :=
  andc (shapeFCbin NY 3) (argsInDotC A WT)

example (X : Term) : formCode (clBot X) = clBotFC (termCode X) := rfl
example (wT X : Term) : formCode (clEq wT X) = clBinFC (termCode X) (termCode wT) 4 := rfl
example (wF X : Term) (k : Nat) :
    formCode (clBin wF X k) = clBinFC (termCode X) (termCode wF) k := rfl
example (wF X : Term) (k : Nat) :
    formCode (clUn wF X k) = clUnFC (termCode X) (termCode wF) k := rfl

/-- ⭐ **La imagen de `isFormCodeE2` sobre CÓDIGOS**: el nodo entra como `ND`, y las dos listas
    testigo como `WF`/`WT`. Es la forma que consume el `hbody` del `pcc_bdAll_intro` de
    `wfAllF`, ya con el hueco del índice relleno. -/
noncomputable def isFCE2DotC (ND WF WT : Term) : Term :=
  orc (clBotFC ND)
   (orc (clAtomFC ND (nthcT ND (termCode (numeralM 2))) WT)
    (orc (clBinFC ND WT 4)
     (orc (clBinFC ND WF 5)
      (orc (clUnFC ND WF 6)
       (orc (clBinFC ND WF 7)
        (orc (clBinFC ND WF 8) (clUnFC ND WF 9)))))))

/-! ## §2 · EL ÁTOMO `In (nthc X j) w`, REFLEJADO Y TRANSPORTADO — factorizado

Aparece **diez** veces en las ocho cláusulas (dos por `clEq`/`clBin`, una por `clUn`), siempre
con la misma forma: reflejar el átomo con `pcc_In_atom_tracked` y transportar
`(nthc X ȷ̇)˙ → nthcT ND ȷ̄`, que es `pcc_eval_nthc` **y por eso pide la cota** `ȷ̇ < lenc X`.
La cota sale, en cada cláusula, de su propia forma posicional. -/

theorem PrfH_clIn {Γ : List Formula} (X ND w : Term) (j : Nat)
    (hNDinv : ∀ W, Prf (substtc zero W ND =eq ND))
    (hND : PrfH Γ (provFromCode (eqCodeFn ND (tcFn X))))
    (hlt : PrfH Γ (lt (numeralM j) (lenc X)))
    (hin : PrfH Γ (In (nthc X (numeralM j)) w))
    (hwND : Prf (hasWit ND) := by hw_auto) :
    PrfH Γ (provFromCode (inFormCodeFn (nthcT ND (termCode (numeralM j))) (tcFn w))) := by
  have h0 : PrfH Γ (provFromCode (inFormCodeFn (tcFn (nthc X (numeralM j))) (tcFn w))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc X (numeralM j)) w) _) hin
  have hev : PrfH Γ (provFromCode (eqCodeFn (nthcT (tcFn X) (termCode (numeralM j)))
      (tcFn (nthc X (numeralM j))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_nthcT (prf_refl _) (prf_tc_numeralM j)) (prf_refl _))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM j)) _) hlt)
  have hcg : PrfH Γ (provFromCode (eqCodeFn (nthcT ND (termCode (numeralM j)))
      (nthcT (tcFn X) (termCode (numeralM j))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_nthcT_arg1_code (termCode (numeralM j)) ND (tcFn X)
      (prf_substtc_termCode_numeralM 0 j) hNDinv) _) hND
  have hfwd : PrfH Γ (provFromCode (eqCodeFn (nthcT ND (termCode (numeralM j)))
      (tcFn (nthc X (numeralM j))))) :=
    PrfH_eq_trans_code _ _ _
      (substtc_inv_nthcT hNDinv (prf_substtc_termCode_numeralM 0 j))
      hcg hev (by hw_auto) (by hw_auto) (by hw_auto)
  have hchain : PrfH Γ (provFromCode (eqCodeFn (tcFn (nthc X (numeralM j)))
      (nthcT ND (termCode (numeralM j))))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_nthcT hNDinv (prf_substtc_termCode_numeralM 0 j))
      hfwd (by hw_auto) (by hw_auto)
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn w) hchain h0

/-! ## §3 · LA DISYUNCIÓN, CON LA ECUACIÓN DEL NODO ARRASTRADA

⚠️ Igual que en C3‑T: la ecuación `ND = Ẋ` entra como **antecedente OBJETO**, porque el
proyecto no tiene debilitamiento de contexto para `PrfH` (deuda B6b) y el `or`‑elim tiene que
conservarla en cada rama. Con `lorAll` de ocho ramas, hacerlo a mano ocho veces sería ilegible;
este combinador lo hace una vez. -/

/-- `pcc_reflect_or` **arrastrando un antecedente** `E`. Siete aplicaciones cierran `lorAll`. -/
theorem prf_or_imp_of (E φ ψ : Formula) (Ac Bc : Term)
    (hφ : Prf (E ⇒ (φ ⇒ provFromCode Ac))) (hψ : Prf (E ⇒ (ψ ⇒ provFromCode Bc))) :
    Prf (E ⇒ (lor φ ψ ⇒ provFromCode (orc Ac Bc))) := by
  refine prf_deduction (deduction_aux ?_ (lor φ ψ) [E] rfl)
  have hor : PrfH [lor φ ψ, E] (lor φ ψ) := PrfH.hyp _ _ (List.Mem.head _)
  refine PrfH_or_elim hor ?_ ?_
  · have hE : PrfH [φ, lor φ ψ, E] E :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact PrfH_orL_code _ _ (PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH hφ _) hE) (PrfH.hyp _ _ (List.Mem.head _)))
  · have hE : PrfH [ψ, lor φ ψ, E] E :=
      PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact PrfH_orR_code _ _ (PrfH.mp _ _ _
      (PrfH.mp _ _ _ (prf_to_prfH hψ _) hE) (PrfH.hyp _ _ (List.Mem.head _)))


/-! ## §4 · LAS OCHO CLÁUSULAS, REFLEJADAS

⭐ **Son cuatro lemas, no ocho**: `clEq` **es** `clBin` con la otra lista testigo (por `rfl`), y
`clBin`/`clUn` son genéricos en el tag `k`. -/

/-- ⭐ `clEq` no necesita lema propio: **es** `clBin` con `W := wT` y `k := 4`. -/
example (wT X : Term) : clEq wT X = clBin wT X 4 := rfl

/-- `clBot`: sólo la forma nularia, y ningún `In` que transportar. -/
theorem pcc_clBot_fc (X ND : Term)
    (hNDinv : ∀ W, Prf (substtc zero W ND =eq ND))
    (hwND : Prf (hasWit ND) := by hw_auto) :
    Prf (provFromCode (eqCodeFn ND (tcFn X)) ⇒ (clBot X ⇒ provFromCode (clBotFC ND))) := by
  refine prf_deduction (deduction_aux ?_ (clBot X) [provFromCode (eqCodeFn ND (tcFn X))] rfl)
  have hND : PrfH [clBot X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn ND (tcFn X))) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hsym : PrfH [clBot X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn (tcFn X) ND)) :=
    PrfH_eq_symm_code _ _ hNDinv hND (by hw_auto) (by hw_auto)
  have h0 : PrfH [clBot X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (shapeFCnul (tcFn X) 2)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_shapeNul_fc X 2) _) (PrfH.hyp _ _ (List.Mem.head _))
  exact PrfH_shapeFCnul_transport 2 (tcFn X) ND hsym h0

/-- `clUn` (tags 6 y 9): forma unaria + **un** `In`. La cota `1̇ < lenc X` sale de la propia
    forma (`lenc X = 2̇`). -/
theorem pcc_clUn_fc (w X ND : Term) (k : Nat)
    (hNDinv : ∀ W, Prf (substtc zero W ND =eq ND))
    (hwND : Prf (hasWit ND) := by hw_auto) :
    Prf (provFromCode (eqCodeFn ND (tcFn X)) ⇒
      (clUn w X k ⇒ provFromCode (clUnFC ND (tcFn w) k))) := by
  refine prf_deduction (deduction_aux ?_ (clUn w X k)
    [provFromCode (eqCodeFn ND (tcFn X))] rfl)
  have hND : PrfH [clUn w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn ND (tcFn X))) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hcl : PrfH [clUn w X k, provFromCode (eqCodeFn ND (tcFn X))] (clUn w X k) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hsh : PrfH [clUn w X k, provFromCode (eqCodeFn ND (tcFn X))] (shapeUn X k) :=
    PrfH_and_elim_left hcl
  have hin : PrfH [clUn w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (In (nthc X (numeralM 1)) w) := PrfH_and_elim_right hcl
  have hstr : PrfH [clUn w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
        (Formula.eq (lenc X) (numeralM 2)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_shapeUn_str X k) _) hsh
  have hlt1 : PrfH [clUn w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (lt (numeralM 1) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (PrfH_eq_symm (PrfH_and_elim_right (PrfH_and_elim_right hstr)))
      (prf_to_prfH (prf_lt_numeralM (by omega : 1 < 2)) _)
  have hsym : PrfH [clUn w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn (tcFn X) ND)) :=
    PrfH_eq_symm_code _ _ hNDinv hND (by hw_auto) (by hw_auto)
  have h0 : PrfH [clUn w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (shapeFCun (tcFn X) k)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_shapeUn_fc X k) _) hsh
  exact PrfH_and_intro_code _ _
    (PrfH_shapeFCun_transport k (tcFn X) ND hsym h0)
    (PrfH_clIn X ND w 1 hNDinv hND hlt1 hin)

/-- `clBin` (tags 5/7/8) **y `clEq`** (tag 4): forma binaria + **dos** `In`. Las dos cotas
    (`1̇` y `2̇`) las domina la longitud que da la forma (`lenc X = 3̇`). -/
theorem pcc_clBin_fc (w X ND : Term) (k : Nat)
    (hNDinv : ∀ W, Prf (substtc zero W ND =eq ND))
    (hwND : Prf (hasWit ND) := by hw_auto) :
    Prf (provFromCode (eqCodeFn ND (tcFn X)) ⇒
      (clBin w X k ⇒ provFromCode (clBinFC ND (tcFn w) k))) := by
  refine prf_deduction (deduction_aux ?_ (clBin w X k)
    [provFromCode (eqCodeFn ND (tcFn X))] rfl)
  have hND : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn ND (tcFn X))) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hcl : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))] (clBin w X k) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hsh : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))] (shapeBin X k) :=
    PrfH_and_elim_left hcl
  have hins : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (land (In (nthc X (numeralM 1)) w) (In (nthc X (numeralM 2)) w)) :=
    PrfH_and_elim_right hcl
  have hstr : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (land (consOk X) (land (Formula.eq (carc X) (numeralM k))
        (Formula.eq (lenc X) (numeralM 3)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_shapeBin_str X k) _) hsh
  have hlt1 : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (lt (numeralM 1) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (PrfH_eq_symm (PrfH_and_elim_right (PrfH_and_elim_right hstr)))
      (prf_to_prfH (prf_lt_numeralM (by omega : 1 < 3)) _)
  have hlt2 : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (lt (numeralM 2) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (PrfH_eq_symm (PrfH_and_elim_right (PrfH_and_elim_right hstr)))
      (prf_to_prfH (prf_lt_numeralM (by omega : 2 < 3)) _)
  have hsym : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn (tcFn X) ND)) :=
    PrfH_eq_symm_code _ _ hNDinv hND (by hw_auto) (by hw_auto)
  have h0 : PrfH [clBin w X k, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (shapeFCbin (tcFn X) k)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_shapeBin_fc X k) _) hsh
  exact PrfH_and_intro_code _ _
    (PrfH_shapeFCbin_transport k (tcFn X) ND hsym h0)
    (PrfH_and_intro_code _ _
      (PrfH_clIn X ND w 1 hNDinv hND hlt1 (PrfH_and_elim_left hins))
      (PrfH_clIn X ND w 2 hNDinv hND hlt2 (PrfH_and_elim_right hins)))

/-- `clAtom` (tag 3): forma binaria + el `∀` acotado **anidado** de `argsIn`. Es literalmente
    la rama binaria de `pcc_isTermCodeE1_trackedC` con el tag 3 en vez del 1. -/
theorem pcc_clAtom_fc (wT X ND : Term)
    (hNDinv : ∀ W, Prf (substtc zero W ND =eq ND))
    (hNDlift : Prf (liftc zero ND =eq ND))
    (hwND : Prf (hasWit ND) := by hw_auto) :
    Prf (provFromCode (eqCodeFn ND (tcFn X)) ⇒
      (clAtom wT X ⇒
        provFromCode (clAtomFC ND (nthcT ND (termCode (numeralM 2))) (tcFn wT)))) := by
  refine prf_deduction (deduction_aux ?_ (clAtom wT X)
    [provFromCode (eqCodeFn ND (tcFn X))] rfl)
  have hND : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn ND (tcFn X))) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hcl : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))] (clAtom wT X) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hsh : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))] (shapeBin X 3) :=
    PrfH_and_elim_left hcl
  have hargs : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (argsIn wT (nthc X (numeralM 2))) := PrfH_and_elim_right hcl
  have hstr : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (land (consOk X) (land (Formula.eq (carc X) (numeralM 3))
        (Formula.eq (lenc X) (numeralM 3)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_shapeBin_str X 3) _) hsh
  have hlt2 : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (lt (numeralM 2) (lenc X)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2
      (PrfH_eq_symm (PrfH_and_elim_right (PrfH_and_elim_right hstr)))
      (prf_to_prfH (prf_lt_numeralM (by omega : 2 < 3)) _)
  have hsym : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn (tcFn X) ND)) :=
    PrfH_eq_symm_code _ _ hNDinv hND (by hw_auto) (by hw_auto)
  have h0 : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (shapeFCbin (tcFn X) 3)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_shapeBin_fc X 3) _) hsh
  have hA0 : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (argsInDotC (tcFn (nthc X (numeralM 2))) (tcFn wT))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_argsIn_trackedC wT (nthc X (numeralM 2))) _) hargs
  have hev : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn (nthcT (tcFn X) (termCode (numeralM 2)))
        (tcFn (nthc X (numeralM 2))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_nthcT (prf_refl _) (prf_tc_numeralM 2)) (prf_refl _))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM 2)) _) hlt2)
  have hcg : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn (nthcT ND (termCode (numeralM 2)))
        (nthcT (tcFn X) (termCode (numeralM 2))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_congr_nthcT_arg1_code (termCode (numeralM 2)) ND (tcFn X)
      (prf_substtc_termCode_numeralM 0 2) hNDinv) _) hND
  have hfwd : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn (nthcT ND (termCode (numeralM 2)))
        (tcFn (nthc X (numeralM 2))))) :=
    PrfH_eq_trans_code _ _ _
      (substtc_inv_nthcT hNDinv (prf_substtc_termCode_numeralM 0 2))
      hcg hev (by hw_auto) (by hw_auto) (by hw_auto)
  have hchain : PrfH [clAtom wT X, provFromCode (eqCodeFn ND (tcFn X))]
      (provFromCode (eqCodeFn (tcFn (nthc X (numeralM 2)))
        (nthcT ND (termCode (numeralM 2))))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_nthcT hNDinv (prf_substtc_termCode_numeralM 0 2))
      hfwd (by hw_auto) (by hw_auto)
  exact PrfH_and_intro_code _ _
    (PrfH_shapeFCbin_transport 3 (tcFn X) ND hsym h0)
    (PrfH_argsInDotC_transport wT _ _ hchain hA0
      (prf_liftc_tcFn (nthc X (numeralM 2)))
      (prf_eq_trans (prf_liftc_nthcT zero ND (termCode (numeralM 2)))
        (prf_congr_nthcT hNDlift (prf_liftc_termCode_numeralM 2))))

/-- ⭐⭐ **EL RECORRIDO DE LAS OCHO CLÁUSULAS**, con `wF`, `wT` y `X` abstractos y el nodo como
    código `ND`. Siete `prf_or_imp_of` y cuatro lemas de cláusula. -/
theorem pcc_isFormCodeE2_trackedC (wF wT X ND : Term)
    (hNDinv : ∀ W, Prf (substtc zero W ND =eq ND))
    (hNDlift : Prf (liftc zero ND =eq ND))
    (hwND : Prf (hasWit ND) := by hw_auto) :
    Prf (provFromCode (eqCodeFn ND (tcFn X)) ⇒
      (isFormCodeE2 wF wT X ⇒ provFromCode (isFCE2DotC ND (tcFn wF) (tcFn wT)))) :=
  prf_or_imp_of _ _ _ _ _ (pcc_clBot_fc X ND hNDinv)
    (prf_or_imp_of _ _ _ _ _ (pcc_clAtom_fc wT X ND hNDinv hNDlift)
      (prf_or_imp_of _ _ _ _ _ (pcc_clBin_fc wT X ND 4 hNDinv)
        (prf_or_imp_of _ _ _ _ _ (pcc_clBin_fc wF X ND 5 hNDinv)
          (prf_or_imp_of _ _ _ _ _ (pcc_clUn_fc wF X ND 6 hNDinv)
            (prf_or_imp_of _ _ _ _ _ (pcc_clBin_fc wF X ND 7 hNDinv)
              (prf_or_imp_of _ _ _ _ _ (pcc_clBin_fc wF X ND 8 hNDinv)
                (pcc_clUn_fc wF X ND 9 hNDinv)))))))


/-! ## §5 · EL DESCENSO DE `substfc` POR LAS OCHO CLÁUSULAS, a nivel ARBITRARIO

Cada cláusula necesita su lema de descenso, y son cuatro (no ocho) por la misma razón que
antes. El de `clAtom` entra en el binder del `argsIn` y por eso pide las hipótesis al nivel
`σv` con el sustituyendo ya `liftc`‑ado. -/

theorem prf_substfc_clBotFC_at (v : Nat) (s NY NY' : Term)
    (hN : Prf (substtc (numeral v) s NY =eq NY')) :
    Prf (substfc (numeral v) s (clBotFC NY) =eq clBotFC NY') :=
  prf_substfc_shapeFCnul_at v s NY NY' 2 hN

theorem prf_substfc_clUnFC_at (v : Nat) (s NY NY' W W' : Term) (k : Nat)
    (hN : Prf (substtc (numeral v) s NY =eq NY'))
    (hW : Prf (substtc (numeral v) s W =eq W')) :
    Prf (substfc (numeral v) s (clUnFC NY W k) =eq clUnFC NY' W' k) := by
  unfold clUnFC
  refine prf_eq_trans (prf_substfc_and _ s _ _)
    (prf_congr_andc (prf_substfc_shapeFCun_at v s _ _ k hN) ?_)
  refine prf_eq_trans (prf_substfc_atom2CodeFn _ s in_sym _ _) ?_
  exact prf_congr_atom2CodeFn
    (prf_eq_trans (prf_substtc_nthcT _ s _ _)
      (prf_congr_nthcT hN (prf_substtc_termCode_numeralM v 1 s))) hW

theorem prf_substfc_clBinFC_at (v : Nat) (s NY NY' W W' : Term) (k : Nat)
    (hN : Prf (substtc (numeral v) s NY =eq NY'))
    (hW : Prf (substtc (numeral v) s W =eq W')) :
    Prf (substfc (numeral v) s (clBinFC NY W k) =eq clBinFC NY' W' k) := by
  unfold clBinFC
  refine prf_eq_trans (prf_substfc_and _ s _ _)
    (prf_congr_andc (prf_substfc_shapeFCbin_at v s _ _ k hN) ?_)
  refine prf_eq_trans (prf_substfc_and _ s _ _) (prf_congr_andc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_atom2CodeFn _ s in_sym _ _) ?_
    exact prf_congr_atom2CodeFn
      (prf_eq_trans (prf_substtc_nthcT _ s _ _)
        (prf_congr_nthcT hN (prf_substtc_termCode_numeralM v 1 s))) hW
  · refine prf_eq_trans (prf_substfc_atom2CodeFn _ s in_sym _ _) ?_
    exact prf_congr_atom2CodeFn
      (prf_eq_trans (prf_substtc_nthcT _ s _ _)
        (prf_congr_nthcT hN (prf_substtc_termCode_numeralM v 2 s))) hW

/-- El `∀` acotado ANIDADO: al entrar en el binder el nivel sube a `σv` y el sustituyendo se
    `liftc`‑a, así que las dos hipótesis se piden ya a ese nivel. -/
theorem prf_substfc_argsInDotC_at (v : Nat) (s A A' W W' : Term)
    (hA : Prf (substtc (numeral (v + 1)) (liftc zero s) A =eq A'))
    (hW : Prf (substtc (numeral (v + 1)) (liftc zero s) W =eq W')) :
    Prf (substfc (numeral v) s (argsInDotC A W) =eq argsInDotC A' W') := by
  unfold argsInDotC bdAllCode
  refine prf_eq_trans (prf_substfc_forall _ s _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl _ (liftc zero s) _ _) (prf_congr_implc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_atom2CodeFn _ (liftc zero s) lt_sym _ _) ?_
    exact prf_congr_atom2CodeFn
      (prf_mp (prf_substtc_var_lt _ (liftc zero s) (numeral 0)) (prf_zero_lt_succ (numeral v)))
      (prf_eq_trans (prf_substtc_lencT _ _ _) (prf_congr_lencT hA))
  · refine prf_eq_trans (prf_substfc_atom2CodeFn _ (liftc zero s) in_sym _ _) ?_
    exact prf_congr_atom2CodeFn
      (prf_eq_trans (prf_substtc_nthcT _ _ _ _)
        (prf_congr_nthcT hA
          (prf_mp (prf_substtc_var_lt _ (liftc zero s) (numeral 0))
            (prf_zero_lt_succ (numeral v))))) hW

theorem prf_substfc_clAtomFC_at (v : Nat) (s NY NY' A A' W W' : Term)
    (hN : Prf (substtc (numeral v) s NY =eq NY'))
    (hA : Prf (substtc (numeral (v + 1)) (liftc zero s) A =eq A'))
    (hW : Prf (substtc (numeral (v + 1)) (liftc zero s) W =eq W')) :
    Prf (substfc (numeral v) s (clAtomFC NY A W) =eq clAtomFC NY' A' W') := by
  unfold clAtomFC
  exact prf_eq_trans (prf_substfc_and _ s _ _)
    (prf_congr_andc (prf_substfc_shapeFCbin_at v s _ _ 3 hN)
      (prf_substfc_argsInDotC_at v s A A' W W' hA hW))

/-! ## §6 · EL `PsiF` DE `wfAllF`, Y SU KEYSTONE

`wfAllF wF wT` es natural en **dos** parámetros, así que —igual que `argsIn` en §4 de C3‑T— se
empaquetan con `cons` y se leen con `carc`/`cdrc`. -/

/-- El cuerpo del `∀` acotado de `wfAllF`, con las **cuatro** ranuras de testigo (cada uno a su
    nivel dentro y fuera del `argsIn` de `clAtom`) y las **dos** del índice. -/
noncomputable def isFCE2PsiAtC (WF WT WF' WT' s s' : Term) : Term :=
  orc (clBotFC (nthcT WF s))
   (orc (clAtomFC (nthcT WF s) (nthcT (nthcT WF' s') (termCode (numeralM 2))) WT')
    (orc (clBinFC (nthcT WF s) WT 4)
     (orc (clBinFC (nthcT WF s) WF 5)
      (orc (clUnFC (nthcT WF s) WF 6)
       (orc (clBinFC (nthcT WF s) WF 7)
        (orc (clBinFC (nthcT WF s) WF 8) (clUnFC (nthcT WF s) WF 9)))))))

/-- Con el hueco relleno por un código CERRADO, las ranuras desplazadas coinciden. -/
example (WF WT s : Term) :
    isFCE2PsiAtC WF WT WF WT s s = isFCE2DotC (nthcT WF s) WF WT := rfl

noncomputable def wfAllFPsiC (WF WT : Term) : Term :=
  isFCE2PsiAtC WF WT WF WT (varc (numeral 0)) (varc (numeral 1))

/-- El `PsiF` que consume `pcc_bdAll_intro`, con los dos testigos EMPAQUETADOS en `p`. -/
noncomputable def wfAllFPsi (p : Term) : Term := wfAllFPsiC (tcFn (carc p)) (tcFn (cdrc p))

/-- `wfAllF` con sus **dos** argumentos empaquetados en UN parámetro (`p = cons wF wT`). -/
noncomputable def wfAllFPair (p : Term) : Formula := wfAllF (carc p) (cdrc p)

/-! ### Las obligaciones ADMINISTRATIVAS -/

theorem liftF_wfAllFPair (k : Nat) (q : Term) :
    liftFormula k (wfAllFPair q) = wfAllFPair (liftTerm k q) := by
  simp only [wfAllFPair, ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_wfAllF, carc, cdrc, liftTerm, liftTerms]

theorem substF_wfAllFPair (v : Nat) (s q : Term) :
    substFormula v s (wfAllFPair q) = wfAllFPair (substTerm v s q) := by
  simp only [wfAllFPair, substF_wfAllF, carc, cdrc, substTerm, substTerms]

theorem liftT_wfAllFBnd (k : Nat) (q : Term) :
    liftTerm k (lenc (carc q)) = lenc (carc (liftTerm k q)) := by
  simp only [lenc, carc, liftTerm, liftTerms]

theorem substT_wfAllFBnd (v : Nat) (s q : Term) :
    substTerm v s (lenc (carc q)) = lenc (carc (substTerm v s q)) := by
  simp only [lenc, carc, substTerm, substTerms]

theorem liftT_wfAllFPsi (k : Nat) (q : Term) :
    liftTerm k (wfAllFPsi q) = wfAllFPsi (liftTerm k q) := by
  simp only [wfAllFPsi, wfAllFPsiC, isFCE2PsiAtC, clBotFC, clAtomFC, clBinFC, clUnFC,
    shapeFCnul, shapeFCbin, shapeFCun, argsInDotC, nulT, unT, binT, consT,
    bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn, eqCodeFn, andc, orc, implc, forallc,
    lencT, nthcT, varc, funcc, tcFn, carc, cdrc, cons, nil, zero, succ, numeralM,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode, liftTerm_termCode]

theorem substT_wfAllFPsi (v : Nat) (s q : Term) :
    substTerm v s (wfAllFPsi q) = wfAllFPsi (substTerm v s q) := by
  simp only [wfAllFPsi, wfAllFPsiC, isFCE2PsiAtC, clBotFC, clAtomFC, clBinFC, clUnFC,
    shapeFCnul, shapeFCbin, shapeFCun, argsInDotC, nulT, unT, binT, consT,
    bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn, eqCodeFn, andc, orc, implc, forallc,
    lencT, nthcT, varc, funcc, tcFn, carc, cdrc, cons, nil, zero, succ, numeralM,
    substTerm, substTerms, substTerm_numeral, substTerm_strCode, substTerm_termCode]

/-! ### ⭐ LA KEYSTONE de `wfAllF`: cómo baja `substfc` por las ocho cláusulas -/

theorem prf_substfc_wfAllFPsi (p s s' : Term) (hs : Prf (liftc zero s =eq s')) :
    Prf (substfc zero s (wfAllFPsi p)
      =eq isFCE2PsiAtC (tcFn (carc p)) (tcFn (cdrc p))
            (tcFn (carc p)) (tcFn (cdrc p)) s s') := by
  have hWF0 : Prf (substtc (numeral 0) s (tcFn (carc p)) =eq tcFn (carc p)) :=
    prf_substtc_tcFn_at 0 s (carc p)
  have hWT0 : Prf (substtc (numeral 0) s (tcFn (cdrc p)) =eq tcFn (cdrc p)) :=
    prf_substtc_tcFn_at 0 s (cdrc p)
  have hWT1 : Prf (substtc (numeral 1) (liftc zero s) (tcFn (cdrc p)) =eq tcFn (cdrc p)) :=
    prf_substtc_tcFn_at 1 (liftc zero s) (cdrc p)
  have hnode : Prf (substtc (numeral 0) s (nthcT (tcFn (carc p)) (varc (numeral 0)))
      =eq nthcT (tcFn (carc p)) s) :=
    prf_eq_trans (prf_substtc_nthcT _ s _ _)
      (prf_congr_nthcT hWF0 (prf_substtc_varc0 s))
  have hargs : Prf (substtc (numeral 1) (liftc zero s)
      (nthcT (nthcT (tcFn (carc p)) (varc (numeral 1))) (termCode (numeralM 2)))
      =eq nthcT (nthcT (tcFn (carc p)) s') (termCode (numeralM 2))) := by
    refine prf_eq_trans (prf_substtc_nthcT _ _ _ _) ?_
    refine prf_congr_nthcT ?_ (prf_substtc_termCode_numeralM 1 2 _)
    refine prf_eq_trans (prf_substtc_nthcT _ _ _ _) ?_
    exact prf_congr_nthcT (prf_substtc_tcFn_at 1 _ (carc p))
      (prf_eq_trans
        (prf_mp (prf_substtc_var_eq (numeral 1) (liftc zero s) (numeral 1)) (prf_refl _)) hs)
  unfold wfAllFPsi wfAllFPsiC isFCE2PsiAtC
  refine prf_eq_trans (prf_substfc_or _ s _ _)
    (prf_congr_orc (prf_substfc_clBotFC_at 0 s _ _ hnode) ?_)
  refine prf_eq_trans (prf_substfc_or _ s _ _)
    (prf_congr_orc (prf_substfc_clAtomFC_at 0 s _ _ _ _ _ _ hnode hargs hWT1) ?_)
  refine prf_eq_trans (prf_substfc_or _ s _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at 0 s _ _ _ _ 4 hnode hWT0) ?_)
  refine prf_eq_trans (prf_substfc_or _ s _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at 0 s _ _ _ _ 5 hnode hWF0) ?_)
  refine prf_eq_trans (prf_substfc_or _ s _ _)
    (prf_congr_orc (prf_substfc_clUnFC_at 0 s _ _ _ _ 6 hnode hWF0) ?_)
  refine prf_eq_trans (prf_substfc_or _ s _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at 0 s _ _ _ _ 7 hnode hWF0) ?_)
  exact prf_eq_trans (prf_substfc_or _ s _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at 0 s _ _ _ _ 8 hnode hWF0)
      (prf_substfc_clUnFC_at 0 s _ _ _ _ 9 hnode hWF0))

/-- La obligación `hPsiId`: sale de la keystone con `s := ⌜v₀⌝`, cuyo lift es `⌜v₁⌝`. -/
theorem prf_wfAllFPsi_id (p : Term) :
    Prf (substfc zero (varc (numeral 0)) (wfAllFPsi p) =eq wfAllFPsi p) :=
  prf_substfc_wfAllFPsi p (varc (numeral 0)) (varc (succ (numeral 0))) prf_liftc_varc0

/-! ### `hbody`, y el `pcc_bdAll_intro` de `wfAllF` -/

theorem prf_wfAllF_body (q i : Term) :
    Prf (wfAllFPair q ⇒ (lt i (lenc (carc q)) ⇒
      provFromCode (substfc zero (tcFn i) (wfAllFPsi q)))) := by
  refine prf_deduction (deduction_aux ?_ (lt i (lenc (carc q))) [wfAllFPair q] rfl)
  have hlt : PrfH [lt i (lenc (carc q)), wfAllFPair q] (lt i (lenc (carc q))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hall : PrfH [lt i (lenc (carc q)), wfAllFPair q] (wfAllFPair q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hND : PrfH [lt i (lenc (carc q)), wfAllFPair q]
      (provFromCode (eqCodeFn (nthcT (tcFn (carc q)) (tcFn i))
        (tcFn (nthc (carc q) i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc (carc q) i) _) hlt
  have hspec := PrfH_spec hall i
  have heq : substFormula 0 i (wfAllFBody (carc q) (cdrc q))
      = Formula.impl (lt i (lenc (carc q)))
          (isFormCodeE2 (carc q) (cdrc q) (nthc (carc q) i)) := by
    simp only [wfAllFBody, substFormula, substTerm, substTerms, lt, lenc, nthc,
      substF_isFormCodeE2, FOL.substTerm_liftTerm, if_true]
  rw [wfAllFPair, wfAllF, heq] at hspec
  have hE2 : PrfH [lt i (lenc (carc q)), wfAllFPair q]
      (isFormCodeE2 (carc q) (cdrc q) (nthc (carc q) i)) := PrfH.mp _ _ _ hspec hlt
  have hNDinv : ∀ W, Prf (substtc zero W (nthcT (tcFn (carc q)) (tcFn i))
      =eq nthcT (tcFn (carc q)) (tcFn i)) :=
    substtc_inv_nthcT (substtc_inv_tcFn (carc q)) (substtc_inv_tcFn i)
  have hNDlift : Prf (liftc zero (nthcT (tcFn (carc q)) (tcFn i))
      =eq nthcT (tcFn (carc q)) (tcFn i)) :=
    prf_eq_trans (prf_liftc_nthcT zero (tcFn (carc q)) (tcFn i))
      (prf_congr_nthcT (prf_liftc_tcFn (carc q)) (prf_liftc_tcFn i))
  have hC : PrfH [lt i (lenc (carc q)), wfAllFPair q]
      (provFromCode (isFCE2DotC (nthcT (tcFn (carc q)) (tcFn i))
        (tcFn (carc q)) (tcFn (cdrc q)))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH
      (pcc_isFormCodeE2_trackedC (carc q) (cdrc q) (nthc (carc q) i)
        (nthcT (tcFn (carc q)) (tcFn i)) hNDinv hNDlift) _) hND) hE2
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm
    (prf_substfc_wfAllFPsi q (tcFn i) (tcFn i) (prf_liftc_tcFn i)))) _) hC

/-- ⭐⭐ **`wfAllF` REFLEJADO**, con los dos testigos abstractos (empaquetados). -/
theorem pcc_wfAllF_pair_tracked (p : Term) :
    Prf (wfAllFPair p ⇒
      provFromCode (bdAllCode (tcFn (lenc (carc p))) (wfAllFPsi p))) :=
  pcc_bdAll_intro wfAllFPair (fun q => lenc (carc q)) wfAllFPsi p
    liftF_wfAllFPair substF_wfAllFPair liftT_wfAllFBnd substT_wfAllFBnd
    liftT_wfAllFPsi substT_wfAllFPsi prf_wfAllFPsi_id (fun _ => by hw_auto) prf_wfAllF_body


/-! ## §7 · DESEMPAQUETAR EL PAR Y DOTAR LA COTA

Dos transportes, exactamente los de `pcc_argsIn_trackedC` (§8 de C3‑T):
* los `carc`/`cdrc` del `cons` son igualdad **objeto** y se mueven con `prf_provCode_congr`;
* el paso de `(lenc wF)˙` a `lencT ẇF` **sólo vale dentro de `Prov`** (`pcc_eval_lenc`) y va
  por `PrfH_bdAllCode_congr_bnd`, con el hueco bajo el binder. -/

/-! ### Congruencias de las imágenes (META, sobre `Prf (_ =eq _)`) -/

theorem prf_congr_shapeFCnul {ND ND' : Term} {k : Nat} (h : Prf (ND =eq ND')) :
    Prf (shapeFCnul ND k =eq shapeFCnul ND' k) :=
  prf_congr_eqCodeFn h (prf_refl _)

theorem prf_congr_shapeFCun {ND ND' : Term} {k : Nat} (h : Prf (ND =eq ND')) :
    Prf (shapeFCun ND k =eq shapeFCun ND' k) :=
  prf_congr_eqCodeFn h (prf_congr_unT (prf_congr_nthcT h (prf_refl _)))

theorem prf_congr_shapeFCbin {ND ND' : Term} {k : Nat} (h : Prf (ND =eq ND')) :
    Prf (shapeFCbin ND k =eq shapeFCbin ND' k) :=
  prf_congr_eqCodeFn h
    (prf_congr_binT (prf_congr_nthcT h (prf_refl _)) (prf_congr_nthcT h (prf_refl _)))

theorem prf_congr_argsInDotC {A A' W W' : Term} (hA : Prf (A =eq A')) (hW : Prf (W =eq W')) :
    Prf (argsInDotC A W =eq argsInDotC A' W') :=
  prf_congr_bdAllCode (prf_congr_lencT hA)
    (prf_congr_atom2CodeFn (prf_congr_nthcT hA (prf_refl _)) hW)

theorem prf_congr_clBotFC {ND ND' : Term} (h : Prf (ND =eq ND')) :
    Prf (clBotFC ND =eq clBotFC ND') := prf_congr_shapeFCnul h

theorem prf_congr_clUnFC {ND ND' W W' : Term} {k : Nat}
    (h : Prf (ND =eq ND')) (hW : Prf (W =eq W')) :
    Prf (clUnFC ND W k =eq clUnFC ND' W' k) :=
  prf_congr_andc (prf_congr_shapeFCun h)
    (prf_congr_atom2CodeFn (prf_congr_nthcT h (prf_refl _)) hW)

theorem prf_congr_clBinFC {ND ND' W W' : Term} {k : Nat}
    (h : Prf (ND =eq ND')) (hW : Prf (W =eq W')) :
    Prf (clBinFC ND W k =eq clBinFC ND' W' k) :=
  prf_congr_andc (prf_congr_shapeFCbin h)
    (prf_congr_andc (prf_congr_atom2CodeFn (prf_congr_nthcT h (prf_refl _)) hW)
      (prf_congr_atom2CodeFn (prf_congr_nthcT h (prf_refl _)) hW))

theorem prf_congr_clAtomFC {ND ND' A A' W W' : Term}
    (h : Prf (ND =eq ND')) (hA : Prf (A =eq A')) (hW : Prf (W =eq W')) :
    Prf (clAtomFC ND A W =eq clAtomFC ND' A' W') :=
  prf_congr_andc (prf_congr_shapeFCbin h) (prf_congr_argsInDotC hA hW)

theorem prf_congr_isFCE2PsiAtC {WF WF' WT WT' WFb WFb' WTb WTb' : Term} (s s' : Term)
    (hF : Prf (WF =eq WF')) (hT : Prf (WT =eq WT'))
    (hFb : Prf (WFb =eq WFb')) (hTb : Prf (WTb =eq WTb')) :
    Prf (isFCE2PsiAtC WF WT WFb WTb s s' =eq isFCE2PsiAtC WF' WT' WFb' WTb' s s') := by
  have hN : Prf (nthcT WF s =eq nthcT WF' s) := prf_congr_nthcT hF (prf_refl _)
  have hA : Prf (nthcT (nthcT WFb s') (termCode (numeralM 2))
      =eq nthcT (nthcT WFb' s') (termCode (numeralM 2))) :=
    prf_congr_nthcT (prf_congr_nthcT hFb (prf_refl _)) (prf_refl _)
  unfold isFCE2PsiAtC
  exact prf_congr_orc (prf_congr_clBotFC hN)
    (prf_congr_orc (prf_congr_clAtomFC hN hA hTb)
      (prf_congr_orc (prf_congr_clBinFC hN hT)
        (prf_congr_orc (prf_congr_clBinFC hN hF)
          (prf_congr_orc (prf_congr_clUnFC hN hF)
            (prf_congr_orc (prf_congr_clBinFC hN hF)
              (prf_congr_orc (prf_congr_clBinFC hN hF) (prf_congr_clUnFC hN hF)))))))

theorem prf_congr_wfAllFPsiC {WF WF' WT WT' : Term}
    (hF : Prf (WF =eq WF')) (hT : Prf (WT =eq WT')) :
    Prf (wfAllFPsiC WF WT =eq wfAllFPsiC WF' WT') :=
  prf_congr_isFCE2PsiAtC _ _ hF hT hF hT

/-! ### Congruencias de `wfAllF` en cada argumento (nivel objeto) -/

theorem PrfH_congr_wfAllF_1 {Γ : List Formula} {wF₁ wF₂ wT : Term}
    (h : PrfH Γ (wF₁ =eq wF₂)) (ha : PrfH Γ (wfAllF wF₁ wT)) : PrfH Γ (wfAllF wF₂ wT) := by
  have hS : ∀ s : Term, substFormula 0 s (wfAllF (.var 0) (liftTerm 0 wT)) = wfAllF s wT := by
    intro s
    simp only [substF_wfAllF, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS wF₂) ▸ PrfH_leibniz_subst (A := wfAllF (.var 0) (liftTerm 0 wT)) h ((hS wF₁) ▸ ha)

theorem PrfH_congr_wfAllF_2 {Γ : List Formula} {wF wT₁ wT₂ : Term}
    (h : PrfH Γ (wT₁ =eq wT₂)) (ha : PrfH Γ (wfAllF wF wT₁)) : PrfH Γ (wfAllF wF wT₂) := by
  have hS : ∀ s : Term, substFormula 0 s (wfAllF (liftTerm 0 wF) (.var 0)) = wfAllF wF s := by
    intro s
    simp only [substF_wfAllF, substTerm, FOL.substTerm_liftTerm, if_true]
  exact (hS wT₂) ▸ PrfH_leibniz_subst (A := wfAllF (liftTerm 0 wF) (.var 0)) h ((hS wT₁) ▸ ha)

/-- El puente al par: `wfAllF wF wT` es `wfAllFPair (cons wF wT)` módulo las dos ecuaciones
    objeto `carc (cons a b) = a` y `cdrc (cons a b) = b`. -/
theorem prf_wfAllF_to_pair (wF wT : Term) :
    Prf (wfAllF wF wT ⇒ wfAllFPair (cons wF wT)) := by
  refine prf_deduction ?_
  have h : PrfH [wfAllF wF wT] (wfAllF wF wT) := prfH_hyp_self _
  have h1 : PrfH [wfAllF wF wT] (wfAllF (carc (cons wF wT)) wT) :=
    PrfH_congr_wfAllF_1 (prf_to_prfH (prf_eq_symm (prf_carc_cons wF wT)) _) h
  exact PrfH_congr_wfAllF_2 (prf_to_prfH (prf_eq_symm (prf_cdrc_cons wF wT)) _) h1

/-! ### La invariancia de nivel 1 del cuerpo, y la cota dotada -/

/-- La imagen de `wfAllF` con la cota ya en forma de accesor dotado. -/
noncomputable def wfAllFDotC (WF WT : Term) : Term :=
  bdAllCode (lencT WF) (wfAllFPsiC WF WT)

/-- El cuerpo de `wfAllF` es invariante bajo `substfc` de NIVEL 1: sus variables de código son
    `⌜v₀⌝` fuera del `argsIn` y `⌜v₀⌝`/`⌜v₁⌝` dentro, todas por debajo del nivel. -/
theorem hPinv_wfAllFPsiC (wF wT : Term) : ∀ u : Term,
    Prf (substfc (succ zero) u (wfAllFPsiC (tcFn wF) (tcFn wT))
      =eq wfAllFPsiC (tcFn wF) (tcFn wT)) := by
  intro u
  have hWF1 : Prf (substtc (numeral 1) u (tcFn wF) =eq tcFn wF) :=
    prf_substtc_tcFn_at 1 u wF
  have hWT1 : Prf (substtc (numeral 1) u (tcFn wT) =eq tcFn wT) :=
    prf_substtc_tcFn_at 1 u wT
  have hWT2 : Prf (substtc (numeral 2) (liftc zero u) (tcFn wT) =eq tcFn wT) :=
    prf_substtc_tcFn_at 2 (liftc zero u) wT
  have hnode : Prf (substtc (numeral 1) u (nthcT (tcFn wF) (varc (numeral 0)))
      =eq nthcT (tcFn wF) (varc (numeral 0))) :=
    prf_eq_trans (prf_substtc_nthcT _ u _ _)
      (prf_congr_nthcT hWF1
        (prf_mp (prf_substtc_var_lt (numeral 1) u (numeral 0)) (prf_zero_lt_succ zero)))
  have hargs : Prf (substtc (numeral 2) (liftc zero u)
      (nthcT (nthcT (tcFn wF) (varc (numeral 1))) (termCode (numeralM 2)))
      =eq nthcT (nthcT (tcFn wF) (varc (numeral 1))) (termCode (numeralM 2))) := by
    refine prf_eq_trans (prf_substtc_nthcT _ _ _ _) ?_
    refine prf_congr_nthcT ?_ (prf_substtc_termCode_numeralM 2 2 _)
    refine prf_eq_trans (prf_substtc_nthcT _ _ _ _) ?_
    exact prf_congr_nthcT (prf_substtc_tcFn_at 2 _ wF)
      (prf_mp (prf_substtc_var_lt (numeral 2) (liftc zero u) (numeral 1))
        (prf_lt_succ_self (numeral 1)))
  unfold wfAllFPsiC isFCE2PsiAtC
  refine prf_eq_trans (prf_substfc_or _ u _ _)
    (prf_congr_orc (prf_substfc_clBotFC_at 1 u _ _ hnode) ?_)
  refine prf_eq_trans (prf_substfc_or _ u _ _)
    (prf_congr_orc (prf_substfc_clAtomFC_at 1 u _ _ _ _ _ _ hnode hargs hWT2) ?_)
  refine prf_eq_trans (prf_substfc_or _ u _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at 1 u _ _ _ _ 4 hnode hWT1) ?_)
  refine prf_eq_trans (prf_substfc_or _ u _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at 1 u _ _ _ _ 5 hnode hWF1) ?_)
  refine prf_eq_trans (prf_substfc_or _ u _ _)
    (prf_congr_orc (prf_substfc_clUnFC_at 1 u _ _ _ _ 6 hnode hWF1) ?_)
  refine prf_eq_trans (prf_substfc_or _ u _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at 1 u _ _ _ _ 7 hnode hWF1) ?_)
  exact prf_eq_trans (prf_substfc_or _ u _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at 1 u _ _ _ _ 8 hnode hWF1)
      (prf_substfc_clUnFC_at 1 u _ _ _ _ 9 hnode hWF1))

/-- ⭐⭐ **`wfAllF` REFLEJADO, con los dos testigos SEPARADOS y la cota ya DOTADA.** -/
theorem pcc_wfAllF_trackedC (wF wT : Term) :
    Prf (wfAllF wF wT ⇒ provFromCode (wfAllFDotC (tcFn wF) (tcFn wT))) := by
  refine prf_deduction ?_
  have h0 : PrfH [wfAllF wF wT]
      (provFromCode (bdAllCode (tcFn (lenc (carc (cons wF wT))))
        (wfAllFPsi (cons wF wT)))) :=
    PrfH.mp _ _ _ (prf_to_prfH
      (impT (prf_wfAllF_to_pair wF wT) (pcc_wfAllF_pair_tracked (cons wF wT))) _)
      (prfH_hyp_self _)
  have hc : Prf (tcFn (carc (cons wF wT)) =eq tcFn wF) := prf_congr_tcFn (prf_carc_cons wF wT)
  have hd : Prf (tcFn (cdrc (cons wF wT)) =eq tcFn wT) := prf_congr_tcFn (prf_cdrc_cons wF wT)
  have hl : Prf (tcFn (lenc (carc (cons wF wT))) =eq tcFn (lenc wF)) :=
    prf_congr_tcFn (prf_congr_lenc (prf_carc_cons wF wT))
  have hmeta : Prf (bdAllCode (tcFn (lenc (carc (cons wF wT)))) (wfAllFPsi (cons wF wT))
      =eq bdAllCode (tcFn (lenc wF)) (wfAllFPsiC (tcFn wF) (tcFn wT))) := by
    unfold wfAllFPsi
    exact prf_congr_bdAllCode hl (prf_congr_wfAllFPsiC hc hd)
  have h1 : PrfH [wfAllF wF wT]
      (provFromCode (bdAllCode (tcFn (lenc wF)) (wfAllFPsiC (tcFn wF) (tcFn wT)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hmeta) _) h0
  have hbnd : PrfH [wfAllF wF wT]
      (provFromCode (eqCodeFn (tcFn (lenc wF)) (lencT (tcFn wF)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_lencT (substtc_inv_tcFn wF))
      (prf_to_prfH (pcc_eval_lenc wF) _) (by hw_auto) (by hw_auto)
  exact PrfH_bdAllCode_congr_bnd _ _ _ (hPinv_wfAllFPsiC wF wT)
    (prf_liftc_tcFn (lenc wF))
    (prf_eq_trans (prf_liftc_lencT zero (tcFn wF)) (prf_congr_lencT (prf_liftc_tcFn wF)))
    hbnd h1


/-! ## §8 · [0.] EL CUERPO DEL `∃∃`, Y LA COMPROBACIÓN CONTRA `substCodeF`

⚠️ Bajo el `∃∃`, el `∃` **EXTERIOR** liga `wF` (que es `⌜v₁⌝`) y el **interior** liga `wT`
(`⌜v₀⌝`) — se lee de `hasWitF c = ex (ex (isFC1 #1 #0 …))`. Y como en C3‑T, cada testigo es una
**variable de código que se desplaza**: `wF` es `⌜v₁⌝`/`⌜v₂⌝`/`⌜v₃⌝` y `wT` es
`⌜v₀⌝`/`⌜v₁⌝`/`⌜v₂⌝`, según se esté fuera del `∀` de `wfAllF`, dentro, o dentro del `argsIn`
anidado de `clAtom`. -/

/-- La imagen de `wfAllF` con las **cuatro** ranuras de testigo separadas. -/
noncomputable def wfAllFDotAtC (WF WT WF' WT' : Term) : Term :=
  bdAllCode (lencT WF)
    (isFCE2PsiAtC WF WT WF' WT' (varc (numeral 0)) (varc (numeral 1)))

example (WF WT : Term) : wfAllFDotC WF WT = wfAllFDotAtC WF WT WF WT := rfl

/-- ⭐ **EL CUERPO DEL `∃∃`**: `wF` en `⌜v₁⌝`, `wT` en `⌜v₀⌝`, y la casilla `I` del testigo de
    línea `T` ya en forma de accesor dotado. -/
noncomputable def hasWitFAc (T I : Term) : Term :=
  andc (andc (wfAll1DotAtC (varc (numeral 1)) (varc (numeral 2)))
             (wfAllFDotAtC (varc (numeral 2)) (varc (numeral 1))
                           (varc (numeral 3)) (varc (numeral 2))))
       (inFormCodeFn (nthcT T I) (varc (numeral 1)))

/-- ⭐⭐ **LA COMPROBACIÓN QUE DECIDE TODO EL FRENTE**: la imagen de arriba **es** la que
    `substCodeF` produce, con el `∃∃` y las cuatro ranuras incluidas. -/
example (t I : Term) :
    substCodeF 0 (tcFn t) (hasWitF (nthc (.var 0) I))
      = exc (exc (hasWitFAc (liftc zero (liftc zero (tcFn t)))
                    (substCodeT 2 (liftc zero (liftc zero (tcFn t)))
                      (liftTerm 0 (liftTerm 0 I))))) := rfl

/-- El cuerpo con `wF` YA relleno y `wT` todavía como hueco (el paso intermedio del `∃∃`). -/
noncomputable def hasWitFAcT (UF T I : Term) : Term :=
  andc (andc (wfAll1DotAtC (varc (numeral 1)) (varc (numeral 2)))
             (wfAllFDotAtC UF (varc (numeral 1)) UF (varc (numeral 2))))
       (inFormCodeFn (nthcT T I) UF)

/-- La imagen de `isFC1` con todo relleno. -/
noncomputable def isFC1DotC (WF WT ND : Term) : Term :=
  andc (andc (wfAll1DotC WT) (wfAllFDotC WF WT)) (inFormCodeFn ND WF)

theorem liftTerm_hasWitFAc (c : Nat) (T I : Term) :
    liftTerm c (hasWitFAc T I) = hasWitFAc (liftTerm c T) (liftTerm c I) := by
  simp only [hasWitFAc, wfAll1DotAtC, wfAll1PsiAtC, wfAllFDotAtC, isFCE2PsiAtC,
    clBotFC, clAtomFC, clBinFC, clUnFC, shapeFCnul, shapeFCun, shapeFCbin, argsInDotC,
    nulT, unT, binT, consT, bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn, eqCodeFn,
    andc, orc, implc, forallc, lencT, nthcT, varc, funcc, cons, nil, zero, succ, numeralM,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode, liftTerm_termCode]

theorem liftTerm_hasWitFAcT (c : Nat) (UF T I : Term) :
    liftTerm c (hasWitFAcT UF T I)
      = hasWitFAcT (liftTerm c UF) (liftTerm c T) (liftTerm c I) := by
  simp only [hasWitFAcT, wfAll1DotAtC, wfAll1PsiAtC, wfAllFDotAtC, isFCE2PsiAtC,
    clBotFC, clAtomFC, clBinFC, clUnFC, shapeFCnul, shapeFCun, shapeFCbin, argsInDotC,
    nulT, unT, binT, consT, bdAllCode, inFormCodeFn, ltCodeFn, atom2CodeFn, eqCodeFn,
    andc, orc, implc, forallc, lencT, nthcT, varc, funcc, cons, nil, zero, succ, numeralM,
    liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode, liftTerm_termCode]

/-! ## §9 · [1.] `isFC1` REFLEJADO -/

/-- ⭐ **`isFC1` reflejado**, con los tres argumentos abstractos. Es una conjunción de tres, y
    las tres mitades ya estaban: §7 (`pcc_wfAllF_trackedC`), C3‑T (`pcc_wfAll1_trackedC`) y el
    kit genérico (`pcc_In_atom_tracked`). -/
theorem pcc_isFC1_trackedC (wF wT c : Term) :
    Prf (isFC1 wF wT c ⇒ provFromCode (isFC1DotC (tcFn wF) (tcFn wT) (tcFn c))) := by
  refine prf_deduction ?_
  have h : PrfH [isFC1 wF wT c] (isFC1 wF wT c) := prfH_hyp_self _
  exact PrfH_and_intro_code _ _
    (PrfH_and_intro_code _ _
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll1_trackedC wT) _)
        (PrfH_and_elim_left (PrfH_and_elim_left h)))
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllF_trackedC wF wT) _)
        (PrfH_and_elim_right (PrfH_and_elim_left h))))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c wF) _) (PrfH_and_elim_right h))

/-! ## §10 · [2.] EL `∃∃`

Dos descensos genéricos —uno por testigo, a niveles distintos— y dos `pcc_exIntro_code_open`. -/

/-- El descenso de `wfAllFDotAtC`, **a nivel arbitrario y con las cuatro ranuras abiertas**.
    Gemelo de `prf_substfc_wfAll1DotAtC_gen`. -/
theorem prf_substfc_wfAllFDotAtC_gen (v : Nat) (s WF WT WF' WT' RF RT RF' RT' : Term)
    (hF : Prf (substtc (numeral (v + 1)) (liftc zero s) WF =eq RF))
    (hT : Prf (substtc (numeral (v + 1)) (liftc zero s) WT =eq RT))
    (hF' : Prf (substtc (numeral (v + 2)) (liftc zero (liftc zero s)) WF' =eq RF'))
    (hT' : Prf (substtc (numeral (v + 2)) (liftc zero (liftc zero s)) WT' =eq RT')) :
    Prf (substfc (numeral v) s (wfAllFDotAtC WF WT WF' WT')
      =eq wfAllFDotAtC RF RT RF' RT') := by
  have hi1 : Prf (substtc (numeral (v + 1)) (liftc zero s) (varc (numeral 0))
      =eq varc (numeral 0)) :=
    prf_mp (prf_substtc_var_lt _ _ (numeral 0)) (prf_gnum_lt (by omega : 0 < v + 1))
  have hj2 : Prf (substtc (numeral (v + 2)) (liftc zero (liftc zero s)) (varc (numeral 1))
      =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt _ _ (numeral 1)) (prf_gnum_lt (by omega : 1 < v + 2))
  have hnode : Prf (substtc (numeral (v + 1)) (liftc zero s) (nthcT WF (varc (numeral 0)))
      =eq nthcT RF (varc (numeral 0))) :=
    prf_eq_trans (prf_substtc_nthcT _ _ _ _) (prf_congr_nthcT hF hi1)
  have hargs : Prf (substtc (numeral (v + 2)) (liftc zero (liftc zero s))
      (nthcT (nthcT WF' (varc (numeral 1))) (termCode (numeralM 2)))
      =eq nthcT (nthcT RF' (varc (numeral 1))) (termCode (numeralM 2))) := by
    refine prf_eq_trans (prf_substtc_nthcT _ _ _ _) ?_
    exact prf_congr_nthcT
      (prf_eq_trans (prf_substtc_nthcT _ _ _ _) (prf_congr_nthcT hF' hj2))
      (prf_substtc_termCode_numeralM (v + 2) 2 _)
  unfold wfAllFDotAtC isFCE2PsiAtC
  refine prf_eq_trans (prf_substfc_forall _ s _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl _ (liftc zero s) _ _) (prf_congr_implc ?_ ?_)
  · exact prf_eq_trans (prf_substfc_atom2CodeFn _ (liftc zero s) lt_sym _ _)
      (prf_congr_atom2CodeFn hi1
        (prf_eq_trans (prf_substtc_lencT _ _ _) (prf_congr_lencT hF)))
  refine prf_eq_trans (prf_substfc_or _ (liftc zero s) _ _)
    (prf_congr_orc (prf_substfc_clBotFC_at (v + 1) (liftc zero s) _ _ hnode) ?_)
  refine prf_eq_trans (prf_substfc_or _ (liftc zero s) _ _)
    (prf_congr_orc (prf_substfc_clAtomFC_at (v + 1) (liftc zero s) _ _ _ _ _ _
      hnode hargs hT') ?_)
  refine prf_eq_trans (prf_substfc_or _ (liftc zero s) _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at (v + 1) (liftc zero s) _ _ _ _ 4 hnode hT) ?_)
  refine prf_eq_trans (prf_substfc_or _ (liftc zero s) _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at (v + 1) (liftc zero s) _ _ _ _ 5 hnode hF) ?_)
  refine prf_eq_trans (prf_substfc_or _ (liftc zero s) _ _)
    (prf_congr_orc (prf_substfc_clUnFC_at (v + 1) (liftc zero s) _ _ _ _ 6 hnode hF) ?_)
  refine prf_eq_trans (prf_substfc_or _ (liftc zero s) _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at (v + 1) (liftc zero s) _ _ _ _ 7 hnode hF) ?_)
  exact prf_eq_trans (prf_substfc_or _ (liftc zero s) _ _)
    (prf_congr_orc (prf_substfc_clBinFC_at (v + 1) (liftc zero s) _ _ _ _ 8 hnode hF)
      (prf_substfc_clUnFC_at (v + 1) (liftc zero s) _ _ _ _ 9 hnode hF))

/-- **PASO A del `∃∃`**: se rellena `wF`, el testigo del `∃` EXTERIOR, **a nivel 1**. -/
theorem prf_substfc_hasWitFAc_wF (T I UF : Term)
    (hUF1 : Prf (liftc zero UF =eq UF))
    (hT1 : Prf (substtc (numeral 1) (liftc zero UF) T =eq T))
    (hI1 : Prf (substtc (numeral 1) (liftc zero UF) I =eq I)) :
    Prf (substfc (numeral 1) (liftc zero UF) (hasWitFAc T I) =eq hasWitFAcT UF T I) := by
  have hUF2 : Prf (liftc zero (liftc zero UF) =eq UF) :=
    prf_eq_trans (NumCodeClosedPrf.prf_congr_liftc hUF1) hUF1
  have hUF3 : Prf (liftc zero (liftc zero (liftc zero UF)) =eq UF) :=
    prf_eq_trans (NumCodeClosedPrf.prf_congr_liftc hUF2) hUF1
  have e2 : Prf (substtc (numeral 2) (liftc zero (liftc zero UF)) (varc (numeral 2)) =eq UF) :=
    prf_eq_trans (prf_mp
      (prf_substtc_var_eq (numeral 2) (liftc zero (liftc zero UF)) (numeral 2)) (prf_refl _))
      hUF2
  have e3 : Prf (substtc (numeral 3) (liftc zero (liftc zero (liftc zero UF)))
      (varc (numeral 3)) =eq UF) :=
    prf_eq_trans (prf_mp
      (prf_substtc_var_eq (numeral 3) (liftc zero (liftc zero (liftc zero UF))) (numeral 3))
      (prf_refl _)) hUF3
  have k12 : Prf (substtc (numeral 2) (liftc zero (liftc zero UF)) (varc (numeral 1))
      =eq varc (numeral 1)) :=
    prf_mp (prf_substtc_var_lt _ _ (numeral 1)) (prf_gnum_lt (by omega : 1 < 2))
  have k23 : Prf (substtc (numeral 3) (liftc zero (liftc zero (liftc zero UF)))
      (varc (numeral 2)) =eq varc (numeral 2)) :=
    prf_mp (prf_substtc_var_lt _ _ (numeral 2)) (prf_gnum_lt (by omega : 2 < 3))
  have hUFslot : Prf (substtc (numeral 1) (liftc zero UF) (varc (numeral 1)) =eq UF) :=
    prf_eq_trans
      (prf_mp (prf_substtc_var_eq (numeral 1) (liftc zero UF) (numeral 1)) (prf_refl _)) hUF1
  unfold hasWitFAc hasWitFAcT
  refine prf_eq_trans (prf_substfc_and _ (liftc zero UF) _ _) (prf_congr_andc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_and _ (liftc zero UF) _ _) (prf_congr_andc ?_ ?_)
    · exact prf_substfc_wfAll1DotAtC_gen 1 (liftc zero UF) _ _ _ _ k12 k23
    · exact prf_substfc_wfAllFDotAtC_gen 1 (liftc zero UF) _ _ _ _ _ _ _ _ e2 k12 e3 k23
  · refine prf_eq_trans (prf_substfc_atom2CodeFn _ (liftc zero UF) in_sym _ _) ?_
    exact prf_congr_atom2CodeFn
      (prf_eq_trans (prf_substtc_nthcT _ _ _ _) (prf_congr_nthcT hT1 hI1)) hUFslot

/-- **PASO B del `∃∃`**: se rellena `wT`, el testigo del `∃` INTERIOR, **a nivel 0**. -/
theorem prf_substfc_hasWitFAcT_wT (T I UF UT : Term)
    (hUT1 : Prf (liftc zero UT =eq UT))
    (hUF1 : Prf (substtc (numeral 1) (liftc zero UT) UF =eq UF))
    (hUF2 : Prf (substtc (numeral 2) (liftc zero (liftc zero UT)) UF =eq UF))
    (hUF0 : Prf (substtc zero UT UF =eq UF))
    (hT0 : Prf (substtc zero UT T =eq T)) (hI0 : Prf (substtc zero UT I =eq I)) :
    Prf (substfc zero UT (hasWitFAcT UF T I) =eq isFC1DotC UF UT (nthcT T I)) := by
  have hUT2 : Prf (liftc zero (liftc zero UT) =eq UT) :=
    prf_eq_trans (NumCodeClosedPrf.prf_congr_liftc hUT1) hUT1
  have e1 : Prf (substtc (numeral 1) (liftc zero UT) (varc (numeral 1)) =eq UT) :=
    prf_eq_trans
      (prf_mp (prf_substtc_var_eq (numeral 1) (liftc zero UT) (numeral 1)) (prf_refl _)) hUT1
  have e2 : Prf (substtc (numeral 2) (liftc zero (liftc zero UT)) (varc (numeral 2)) =eq UT) :=
    prf_eq_trans (prf_mp
      (prf_substtc_var_eq (numeral 2) (liftc zero (liftc zero UT)) (numeral 2)) (prf_refl _))
      hUT2
  unfold hasWitFAcT isFC1DotC
  refine prf_eq_trans (prf_substfc_and zero UT _ _) (prf_congr_andc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_and zero UT _ _) (prf_congr_andc ?_ ?_)
    · exact prf_substfc_wfAll1DotAtC UT hUT1
    · exact prf_substfc_wfAllFDotAtC_gen 0 UT _ _ _ _ _ _ _ _ hUF1 e1 hUF2 e2
  · refine prf_eq_trans (prf_substfc_atom2CodeFn zero UT in_sym _ _) ?_
    exact prf_congr_atom2CodeFn
      (prf_eq_trans (prf_substtc_nthcT _ _ _ _) (prf_congr_nthcT hT0 hI0)) hUF0

/-- ⭐⭐ **EL CUERPO, REFLEJADO Y CERRADO POR EL `∃∃`.** Los dos `pcc_exIntro_code_open` se
    encadenan por `prf_substfc_ex`, que es lo que convierte el `substfc` de nivel 0 sobre el
    `exc` en un `exc` del `substfc` de nivel 1. -/
theorem pcc_isFC1_exc_body (t : Term) (i : Nat) :
    Prf (isFC1 (.var 1) (.var 0) (nthc t (numeralM i)) ⇒
      (lt (numeralM i) (lenc t) ⇒
        provFromCode (exc (exc (hasWitFAc (tcFn t) (termCode (numeralM i))))))) := by
  refine prf_deduction (deduction_aux ?_ (lt (numeralM i) (lenc t))
    [isFC1 (.var 1) (.var 0) (nthc t (numeralM i))] rfl)
  have hlt : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (lt (numeralM i) (lenc t)) := PrfH.hyp _ _ (List.Mem.head _)
  have hFC : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (isFC1 (.var 1) (.var 0) (nthc t (numeralM i))) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  -- (1) las tres mitades de `isFC1`, por separado (no hay `and`-elim a nivel de CÓDIGO:
  --     se ensamblan directamente, que además es más corto)
  have hL1 : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (wfAll1DotC (tcFn (.var 0)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll1_trackedC (.var 0)) _)
      (PrfH_and_elim_left (PrfH_and_elim_left hFC))
  have hL2 : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (wfAllFDotC (tcFn (.var 1)) (tcFn (.var 0)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAllF_trackedC (.var 1) (.var 0)) _)
      (PrfH_and_elim_right (PrfH_and_elim_left hFC))
  have hR0 : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (inFormCodeFn (tcFn (nthc t (numeralM i))) (tcFn (.var 1)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc t (numeralM i)) (.var 1)) _)
      (PrfH_and_elim_right hFC)
  -- (2) el transporte de la casilla: `(nthc t ı̇)˙ → nthcT ṫ ı̄`, que pide la cota
  have hev : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (eqCodeFn (nthcT (tcFn t) (termCode (numeralM i)))
        (tcFn (nthc t (numeralM i))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_congr_eqCodeFn
        (prf_congr_nthcT (prf_refl _) (prf_tc_numeralM i)) (prf_refl _))) _)
      (PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc t (numeralM i)) _) hlt)
  have hsym : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (eqCodeFn (tcFn (nthc t (numeralM i)))
        (nthcT (tcFn t) (termCode (numeralM i))))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn t) (prf_substtc_termCode_numeralM 0 i))
      hev (by hw_auto) (by hw_auto)
  have hR : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (inFormCodeFn (nthcT (tcFn t) (termCode (numeralM i)))
        (tcFn (.var 1)))) :=
    PrfH_in_transport _ _ _ (substtc_inv_tcFn (.var 1)) hsym hR0
  have hfilled : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (isFC1DotC (tcFn (.var 1)) (tcFn (.var 0))
        (nthcT (tcFn t) (termCode (numeralM i))))) :=
    PrfH_and_intro_code _ _ (PrfH_and_intro_code _ _ hL1 hL2) hR
  -- (3) `∃` INTERIOR (`wT`)
  have hB := prf_substfc_hasWitFAcT_wT (tcFn t) (termCode (numeralM i))
    (tcFn (.var 1)) (tcFn (.var 0)) (prf_liftc_tcFn (.var 0))
    (prf_substtc_tcFn_at 1 _ (.var 1)) (prf_substtc_tcFn_at 2 _ (.var 1))
    (prf_substtc_tcFn_at 0 _ (.var 1))
    (prf_substtc_tcFn_at 0 _ t) (prf_substtc_termCode_numeralM 0 i _)
  have hsub : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (substfc zero (tcFn (.var 0))
        (hasWitFAcT (tcFn (.var 1)) (tcFn t) (termCode (numeralM i))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hB)) _) hfilled
  have hex1 : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (exc (hasWitFAcT (tcFn (.var 1)) (tcFn t) (termCode (numeralM i))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_exIntro_code_open
      (hasWitFAcT (tcFn (.var 1)) (tcFn t) (termCode (numeralM i))) (tcFn (.var 0))
      (by simp only [liftTerm_hasWitFAcT, liftTerm_tcFn, liftTerm_termCode]; hw_auto)
      (by simp only [liftTerm_tcFn]; hw_auto)) _) hsub
  -- (4) `∃` EXTERIOR (`wF`), encadenado por `prf_substfc_ex`
  have hA := prf_substfc_hasWitFAc_wF (tcFn t) (termCode (numeralM i)) (tcFn (.var 1))
    (prf_liftc_tcFn (.var 1)) (prf_substtc_tcFn_at 1 _ t)
    (prf_substtc_termCode_numeralM 1 i _)
  have hchain : Prf (exc (hasWitFAcT (tcFn (.var 1)) (tcFn t) (termCode (numeralM i)))
      =eq substfc zero (tcFn (.var 1))
            (exc (hasWitFAc (tcFn t) (termCode (numeralM i))))) :=
    prf_eq_symm (prf_eq_trans
      (prf_substfc_ex zero (tcFn (.var 1)) (hasWitFAc (tcFn t) (termCode (numeralM i))))
      (prf_congr_exc hA))
  have hex2 : PrfH [lt (numeralM i) (lenc t), isFC1 (.var 1) (.var 0) (nthc t (numeralM i))]
      (provFromCode (substfc zero (tcFn (.var 1))
        (exc (hasWitFAc (tcFn t) (termCode (numeralM i)))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr hchain) _) hex1
  exact PrfH.mp _ _ _ (prf_to_prfH (pcc_exIntro_code_open
    (exc (hasWitFAc (tcFn t) (termCode (numeralM i)))) (tcFn (.var 1))
    (by simp only [liftTerm_exc_open, liftTerm_hasWitFAc, liftTerm_tcFn, liftTerm_termCode]
        hw_auto)
    (by simp only [liftTerm_tcFn]; hw_auto)) _) hex2

/-- ⭐⭐⭐ **`hasWitF` REFLEJADO**, con `t` abstracto: el `∃∃` objeto eliminado con dos
    `prf_ex_elim_imp`, módulo la cota `ı̇ < lenc t` que `Hcond` ya trae. -/
theorem pcc_hasWitF_exc (t : Term) (i : Nat) :
    Prf (hasWitF (nthc t (numeralM i)) ⇒
      (lt (numeralM i) (lenc t) ⇒
        provFromCode (exc (exc (hasWitFAc (tcFn t) (termCode (numeralM i))))))) := by
  have inner : Prf (Formula.ex (isFC1 (.var 1) (.var 0)
      (liftTerm 0 (liftTerm 0 (nthc t (numeralM i)))))
      ⇒ liftFormula 0 (lt (numeralM i) (lenc t) ⇒
          provFromCode (exc (exc (hasWitFAc (tcFn t) (termCode (numeralM i))))))) := by
    refine prf_ex_elim_imp ?_
    refine PrfH.mp _ _ _ ?_ (prfH_hyp_self _)
    simpa only [liftFormula, liftFormula_provFromCode_open, liftTerm_exc_open,
      liftTerm_hasWitFAc, liftTerm_tcFn, liftTerm_termCode, isFC1, land, In,
      lt, lenc, nthc, liftTerm, liftTerms, liftTerm_numeralM, cons, nil, zero, succ,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceGT, reduceIte, if_true]
      using prf_to_prfH (pcc_isFC1_exc_body (liftTerm 0 (liftTerm 0 t)) i) _
  unfold hasWitF
  exact prf_ex_elim_imp (PrfH.mp _ _ _ (prf_to_prfH inner _) (prfH_hyp_self _))


/-! ## §11 · [3.] LA FONTANERÍA `condD`, Y `DEUDA_hGuardF` CERRADA

Mismo gesto que §12 de C3‑T: `prf_substfc_arith_open` convierte el `substfc` **objeto** en la
función META `substCodeF`, y de ahí la alineación es una igualdad de términos que sale por
`rfl`. El único punto que `rfl` no alcanza sigue siendo el índice `numeralM i` con `i`
**variable** (`substCodeT_closed` es un teorema, no una defeq). -/

/-- ⭐ **`condD` de la guarda de FÓRMULA, COMPUTADO** — con el índice abstracto, por `rfl`. -/
theorem substCodeF_hasWitF_nthc (t I : Term) :
    substCodeF 0 (tcFn t) (hasWitF (nthc (.var 0) I))
      = exc (exc (hasWitFAc (liftc zero (liftc zero (tcFn t)))
                    (substCodeT 2 (liftc zero (liftc zero (tcFn t)))
                      (liftTerm 0 (liftTerm 0 I))))) := rfl

/-- Congruencia de `hasWitFAc` en la ranura de la LÍNEA. -/
theorem prf_congr_hasWitFAc_T {T T' I : Term} (h : Prf (T =eq T')) :
    Prf (hasWitFAc T I =eq hasWitFAc T' I) := by
  unfold hasWitFAc
  exact prf_congr_andc (prf_refl _)
    (prf_congr_atom2CodeFn (prf_congr_nthcT h (prf_refl _)) (prf_refl _))

/-- ⭐ **La alineación**: el código que `condD` impone **es** la imagen que §10 produce. Los
    **dos** `liftc` que `substCodeF` deja al entrar en los dos `∃` se colapsan con
    `prf_liftc_tcFn`. -/
theorem prf_condD_hasWitF_eq (t : Term) (i : Nat) :
    Prf (condD (hasWitF (nthc (.var 0) (numeralM i))) t
      =eq exc (exc (hasWitFAc (tcFn t) (termCode (numeralM i))))) := by
  have hlift : Prf (liftc zero (liftc zero (tcFn t)) =eq tcFn t) :=
    prf_eq_trans (NumCodeClosedPrf.prf_congr_liftc (prf_liftc_tcFn t)) (prf_liftc_tcFn t)
  have h : substCodeF 0 (tcFn t) (hasWitF (nthc (.var 0) (numeralM i)))
      = exc (exc (hasWitFAc (liftc zero (liftc zero (tcFn t)))
          (termCode (numeralM i)))) := by
    rw [substCodeF_hasWitF_nthc, liftTerm_numeralM, liftTerm_numeralM,
      substCodeT_closed 2 (liftc zero (liftc zero (tcFn t))) (numeralM i)
        (fun c => liftTerm_numeralM c i)]
  refine prf_eq_trans ?_ (prf_congr_exc (prf_congr_exc (prf_congr_hasWitFAc_T hlift)))
  show Prf (substfc zero (tcFn t) (formCode (hasWitF (nthc (.var 0) (numeralM i)))) =eq _)
  rw [← h]
  exact prf_substfc_arith_open 0 (tcFn t) _

/-- ⭐⭐⭐ **`DEUDA_hGuardF` PROBADA**, para toda casilla `i` bajo la longitud canónica `n`.

    La cota `i < n` es la misma de C3‑T y por la misma razón: el transporte
    `(nthc t ı̇)˙ → nthcT ṫ ı̄` es `pcc_eval_nthc`, y sin ella ese paso no existe. -/
theorem pcc_hGuardF (i n : Nat) (t : Term) (hin : i < n) :
    ROBINSON_PlusPlus.Meta.LineWFGuardPrf.DEUDA_hGuardF i n t := by
  show Prf (lineWF t ⇒ ((lenc t =eq numeralM n) ⇒
    (substFormula 0 t (hasWitF (nthc (.var 0) (numeralM i))) ⇒
      provFromCode (condD (hasWitF (nthc (.var 0) (numeralM i))) t))))
  have hsub : substFormula 0 t (hasWitF (nthc (.var 0) (numeralM i)))
      = hasWitF (nthc t (numeralM i)) := by
    simp only [substF_hasWitF, nthc, substTerm, substTerms, substTerm_numeralM,
      FOL.substTerm_liftTerm, if_true]
  rw [hsub]
  refine prf_deduction (deduction_aux (deduction_aux ?_
    (hasWitF (nthc t (numeralM i))) [lenc t =eq numeralM n, lineWF t] rfl)
    (lenc t =eq numeralM n) [lineWF t] rfl)
  have hhw : PrfH [hasWitF (nthc t (numeralM i)), lenc t =eq numeralM n, lineWF t]
      (hasWitF (nthc t (numeralM i))) := PrfH.hyp _ _ (List.Mem.head _)
  have hlenc : PrfH [hasWitF (nthc t (numeralM i)), lenc t =eq numeralM n, lineWF t]
      (lenc t =eq numeralM n) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH [hasWitF (nthc t (numeralM i)), lenc t =eq numeralM n, lineWF t]
      (lt (numeralM i) (lenc t)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlenc)
      (prf_to_prfH (prf_lt_numeralM hin) _)
  have hexc : PrfH [hasWitF (nthc t (numeralM i)), lenc t =eq numeralM n, lineWF t]
      (provFromCode (exc (exc (hasWitFAc (tcFn t) (termCode (numeralM i)))))) :=
    PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_hasWitF_exc t i) _) hhw) hlt
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_condD_hasWitF_eq t i))) _) hexc

/-! ## §12 · ⭐⭐⭐ LA CASCADA DE ADR‑020, ENTERAMENTE DESCARGADA -/

/-- ⭐⭐⭐ **`hGuard` SIN DEUDAS.** `hGuard_of_deudas` (`Meta/LineWFGuardPrf.lean`) pedía las
    **dos** obligaciones que ADR‑020 dejó abiertas; ya no pide ninguna. Lo único que se añade
    es que los índices de casilla caigan bajo la longitud canónica — cosa que cumplen las
    **once** casillas reales, y que la cota de `pcc_eval_nthc` hace inevitable. -/
theorem hGuard_of_slots (t : Term) (n : Nat) (C : Formula)
    (hC : ROBINSON_PlusPlus.Meta.LineWFGuardPrf.Hcond n t C)
    (gs : List ROBINSON_PlusPlus.Meta.LineWFGuardPrf.GuardSlot)
    (hgsT : ∀ i, List.Mem (ROBINSON_PlusPlus.Meta.LineWFGuardPrf.GuardSlot.wit i) gs → i < n)
    (hgsF : ∀ i, List.Mem (ROBINSON_PlusPlus.Meta.LineWFGuardPrf.GuardSlot.witF i) gs → i < n) :
    ROBINSON_PlusPlus.Meta.LineWFGuardPrf.Hcond n t
      (ROBINSON_PlusPlus.Meta.LineWFGuardPrf.guardedCond gs C) :=
  ROBINSON_PlusPlus.Meta.LineWFGuardPrf.hcond_absorbe_cascade t n C hC gs
    (fun g hg => by
      cases g with
      | wit i => exact pcc_hGuardT i n t (hgsT i hg)
      | witF i => exact pcc_hGuardF i n t (hgsF i hg))

/-- **Las ONCE casillas de la enmienda, con su longitud canónica**: las cuatro `wit`
    —`(3,4)`, `(3,4)`, `(3,5)`, `(4,5)`— y las siete `witF` —`(2,4)`, `(2,4)`, `(3,4)`,
    `(2,5)`, `(2,3)`, `(2,4)`, `(2,3)`—. **Todas cumplen `i < n`.** -/
example :
    [(3,4), (3,4), (3,5), (4,5),
     (2,4), (2,4), (3,4), (2,5), (2,3), (2,4), (2,3)].all
      (fun p => decide (p.1 < p.2)) = true := by decide

end ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf

/-! ## `export` — por PROPÓSITO DECLARADO

El consumidor previsto es el chasis de ADR‑020: probada `DEUDA_hGuardF`, `hGuard_of_slots`
absorbe la cascada **sin ninguna obligación abierta**.

⚠️ **Y eso NO deja `pcc_lineWF_tracked` incondicional**: `pcc_lineWF_tracked_modulo_7` sigue
pidiendo un reflector por tag, y en el árbol hay **14** —ninguno de los 7 de sustitución—. Lo
que a esos siete les falta es ya **sólo su condición ESTRUCTURAL**, que es lo que B3.2/B3.4
compraron; el conjunto extra que esta ADR añadió ya no estorba (§3.46.4, §3.47).

Nada lo consume todavía, y se dice en vez de fingir una medición de consumo (mismo criterio
que `Meta/D3ChainDotPrf.lean`). -/
export ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf (
  shapeFCnul treeNul1 pcc_shapeNul_fc shapeNulCtx prf_substfc_shapeNulCtx
  PrfH_shapeFCnul_transport prf_substfc_shapeFCnul_at
  clBotFC clBinFC clUnFC clAtomFC isFCE2DotC
  PrfH_clIn prf_or_imp_of
  pcc_clBot_fc pcc_clUn_fc pcc_clBin_fc pcc_clAtom_fc pcc_isFormCodeE2_trackedC
  prf_substfc_clBotFC_at prf_substfc_clUnFC_at prf_substfc_clBinFC_at
  prf_substfc_argsInDotC_at prf_substfc_clAtomFC_at
  isFCE2PsiAtC wfAllFPsiC wfAllFPsi wfAllFPair
  liftF_wfAllFPair substF_wfAllFPair liftT_wfAllFBnd substT_wfAllFBnd
  liftT_wfAllFPsi substT_wfAllFPsi
  prf_substfc_wfAllFPsi prf_wfAllFPsi_id prf_wfAllF_body pcc_wfAllF_pair_tracked
  prf_congr_shapeFCnul prf_congr_shapeFCun prf_congr_shapeFCbin prf_congr_argsInDotC
  prf_congr_clBotFC prf_congr_clUnFC prf_congr_clBinFC prf_congr_clAtomFC
  prf_congr_isFCE2PsiAtC prf_congr_wfAllFPsiC
  PrfH_congr_wfAllF_1 PrfH_congr_wfAllF_2 prf_wfAllF_to_pair
  wfAllFDotC hPinv_wfAllFPsiC pcc_wfAllF_trackedC
  wfAllFDotAtC hasWitFAc hasWitFAcT isFC1DotC
  liftTerm_hasWitFAc liftTerm_hasWitFAcT pcc_isFC1_trackedC
  prf_substfc_wfAllFDotAtC_gen prf_substfc_hasWitFAc_wF prf_substfc_hasWitFAcT_wT
  pcc_isFC1_exc_body pcc_hasWitF_exc
  substCodeF_hasWitF_nthc prf_congr_hasWitFAc_T prf_condD_hasWitF_eq pcc_hGuardF hGuard_of_slots
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_shapeNul_fc
#print axioms ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_isFormCodeE2_trackedC
#print axioms ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_wfAllF_trackedC
#print axioms ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_isFC1_trackedC
#print axioms ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_hasWitF_exc
#print axioms ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.pcc_hGuardF
#print axioms ROBINSON_PlusPlus.Meta.HasWitFTrackedPrf.hGuard_of_slots
