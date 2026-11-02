/-
SCOUT A3 — ¿hay una formulación de `nodeOk`/`isFCB` que EVITE el cruce del binder `exc`?

Este fichero mide la propuesta (d0): **dotar `In` como su ÁTOMO** (`inFormCodeFn`, que YA existe
en `Meta/Sigma1CorePrf.lean:55`), NO como su despliegue `∃`‑acotado (`bdInDot`, el de A1).
Con eso el cuerpo dotado `PsiF w` NO tiene ningún binder, y el descenso de `substfc` es
íntegramente de NIVEL 0.

Lo que se compila aquí:
  * `prf_substfc_nodeOkDot_gen` — el descenso GENÉRICO de `substfc zero s` por los 12 disyuntos.
  * `prf_substfc_PsiF`          — su instancia en el cuerpo real.
  * `hPsiId_A3`                 — la obligación `hPsiId` de `pcc_bdAll_intro`, cerrada por
                                  `prf_substfc_PsiF (varc (numeral 0))`, porque el RHS es
                                  DEFINICIONALMENTE `PsiF w` (`rfl`).
  * `hbody_target_A3`           — la forma del `hbody` tras normalizar.
  * `liftTerm_PsiF` / `substTerm_PsiF` — las obligaciones `hPl`/`hPs`.
-/
import ROBINSON_PlusPlus.Meta

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

namespace A3Scout

/-! ## 1 · El nodo DOTADO, con hueco explícito y SIN binder -/

/-- `substfc 0 s` sobre el código del átomo `In`, con hueco ANIDADO en el 1er argumento.
    Generaliza `prf_substfc_inFormCode_hole1` (que exige el hueco pelado `⌜v₀⌝`). -/
theorem prf_substfc_inDot (s A A' W : Term)
    (hA : Prf (substtc zero s A =eq A')) (hW : ∀ V, Prf (substtc zero V W =eq W)) :
    Prf (substfc zero s (inFormCodeFn A W) =eq inFormCodeFn A' W) := by
  show Prf (substfc zero s (atomc (strCode in_sym) (cons A (cons W nil)))
    =eq atomc (strCode in_sym) (cons A' (cons W nil)))
  refine prf_eq_trans (prf_substfc_atom zero s (strCode in_sym) (cons A (cons W nil))) ?_
  refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
  refine prf_eq_trans (prf_substtsc_cons zero s A (cons W nil)) ?_
  refine prf_eq_trans (prf_congr_cons_head hA) ?_
  refine prf_congr_cons_tail ?_
  exact prf_eq_trans (prf_substtsc_cons zero s W nil)
    (prf_eq_trans (prf_congr_cons_head (hW s)) (prf_congr_cons_tail (prf_substtsc_nil zero s)))

/-- Forma dotada de `carc X = k̄ ∧ lenc X = n̄` (los dos `=eq` de todo nodo). -/
noncomputable def shapeDot (X : Term) (k n : Nat) : Term :=
  andc (eqCodeFn (carcT X) (tcFn (numeralM k))) (eqCodeFn (lencT X) (tcFn (numeralM n)))

/-- `unOk` dotado: forma + UN hijo en `w`. -/
noncomputable def unDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 2) (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)

/-- `binOk` dotado: forma + DOS hijos en `w`. -/
noncomputable def binDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3)
    (andc (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)
          (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W))

/-- `strBinOk` dotado: casilla 1 OPACA (cadena), hijo en la 2. -/
noncomputable def strBinDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3) (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W)

/-- `varOk` dotado. -/
noncomputable def varDot (X : Term) : Term := shapeDot X 0 2

/-- Disyunción de código asociada a la derecha (espejo de `lorAll`). -/
def lorAllc : Term → List Term → Term
  | a, []      => a
  | a, b :: bs => orc a (lorAllc b bs)

/-- **El nodo dotado, 12 casos.** `W` es el código de `w`; `X` el código del nodo.
    ⚠️ NO hay ni un `exc`: todos los átomos son `=eq` o `In`, y `In` va como ÁTOMO. -/
noncomputable def nodeOkDot (W X : Term) : Term :=
  lorAllc (shapeDot X 2 1)
    [ strBinDot W X 3
    , binDot W X 4
    , binDot W X 5
    , unDot  W X 6
    , binDot W X 7
    , binDot W X 8
    , unDot  W X 9
    , varDot X
    , strBinDot W X 1
    , eqCodeFn X (tcFn nil)
    , andc (inFormCodeFn (carcT X) W) (inFormCodeFn (cdrcT X) W) ]

/-! ## 2 · EL DESCENSO GENÉRICO de `substfc zero s` — todo a NIVEL 0 -/

theorem prf_substfc_shapeDot (s X X' : Term) (k n : Nat)
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (shapeDot X k n) =eq shapeDot X' k n) := by
  unfold shapeDot
  refine prf_eq_trans (prf_substfc_and zero s _ _) (prf_congr_andc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_eq zero s _ _) (prf_congr_eqCodeFn ?_ ?_)
    · exact prf_eq_trans (prf_substtc_carcT zero s X) (prf_congr_carcT hX)
    · exact substtc_inv_tcFn (numeralM k) s
  · refine prf_eq_trans (prf_substfc_eq zero s _ _) (prf_congr_eqCodeFn ?_ ?_)
    · exact prf_eq_trans (prf_substtc_lencT zero s X) (prf_congr_lencT hX)
    · exact substtc_inv_tcFn (numeralM n) s

/-- El hijo `nthcT X k̇` bajo `substtc zero s`. -/
theorem prf_substtc_child (s X X' : Term) (k : Nat)
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substtc zero s (nthcT X (tcFn (numeralM k))) =eq nthcT X' (tcFn (numeralM k))) :=
  prf_eq_trans (prf_substtc_nthcT zero s X (tcFn (numeralM k)))
    (prf_congr_nthcT hX (substtc_inv_tcFn (numeralM k) s))

theorem prf_substfc_unDot (s W X X' : Term) (k : Nat)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (unDot W X k) =eq unDot W X' k) := by
  unfold unDot
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 2 hX)
      (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 1 hX) hW))

theorem prf_substfc_binDot (s W X X' : Term) (k : Nat)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (binDot W X k) =eq binDot W X' k) := by
  unfold binDot
  refine prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 3 hX) ?_)
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 1 hX) hW)
      (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 2 hX) hW))

theorem prf_substfc_strBinDot (s W X X' : Term) (k : Nat)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (strBinDot W X k) =eq strBinDot W X' k) := by
  unfold strBinDot
  exact prf_eq_trans (prf_substfc_and zero s _ _)
    (prf_congr_andc (prf_substfc_shapeDot s X X' k 3 hX)
      (prf_substfc_inDot s _ _ W (prf_substtc_child s X X' 2 hX) hW))

/-- **EL DESCENSO**: `substfc zero s` atraviesa los 12 disyuntos y sólo toca el hueco de `X`. -/
theorem prf_substfc_nodeOkDot_gen (s W X X' : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W)) (hX : Prf (substtc zero s X =eq X')) :
    Prf (substfc zero s (nodeOkDot W X) =eq nodeOkDot W X') := by
  unfold nodeOkDot lorAllc
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 2 1 hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_strBinDot s W X X' 3 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDot s W X X' 4 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDot s W X X' 5 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_unDot s W X X' 6 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDot s W X X' 7 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_binDot s W X X' 8 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_unDot s W X X' 9 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_shapeDot s X X' 0 2 hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _)
    (prf_congr_orc (prf_substfc_strBinDot s W X X' 1 hW hX) ?_)
  refine prf_eq_trans (prf_substfc_or zero s _ _) (prf_congr_orc ?_ ?_)
  · exact prf_eq_trans (prf_substfc_eq zero s _ _)
      (prf_congr_eqCodeFn hX (substtc_inv_tcFn nil s))
  · refine prf_eq_trans (prf_substfc_and zero s _ _) (prf_congr_andc ?_ ?_)
    · exact prf_substfc_inDot s _ _ W
        (prf_eq_trans (prf_substtc_carcT zero s X) (prf_congr_carcT hX)) hW
    · exact prf_substfc_inDot s _ _ W
        (prf_eq_trans (prf_substtc_cdrcT zero s X) (prf_congr_cdrcT hX)) hW

/-! ## 3 · El cuerpo real y las obligaciones de `pcc_bdAll_intro` -/

/-- **El cuerpo dotado del `∀` acotado**, con el hueco `⌜v₀⌝` en el ÍNDICE.
    `PsiF w = nodeOkDot ẇ (nthc(ẇ, ⌜v₀⌝))`. -/
noncomputable def PsiF (w : Term) : Term :=
  nodeOkDot (tcFn w) (nthcT (tcFn w) (varc (numeral 0)))

/-- El descenso instanciado: `substfc 0 s (PsiF w) =eq nodeOkDot ẇ (nthc(ẇ, s))`. -/
theorem prf_substfc_PsiF (w s : Term) :
    Prf (substfc zero s (PsiF w) =eq nodeOkDot (tcFn w) (nthcT (tcFn w) s)) :=
  prf_substfc_nodeOkDot_gen s (tcFn w) _ _ (substtc_inv_tcFn w)
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn w) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn w s) (prf_substtc_varc0 s)))

/-- **`hPsiId` de `pcc_bdAll_intro`, CERRADA.** El RHS del descenso en `s := ⌜v₀⌝` es
    DEFINICIONALMENTE `PsiF w`: no hace falta ni un paso más. Esto es exactamente lo que
    un binder `exc` en el cuerpo IMPEDIRÍA (allí `s` se convierte en `liftc 0 s`, y
    `liftc 0 ⌜v₀⌝ = ⌜v₁⌝` sólo es una igualdad DEMOSTRABLE, no definicional). -/
theorem hPsiId_A3 (w : Term) :
    Prf (substfc zero (varc (numeral 0)) (PsiF w) =eq PsiF w) :=
  prf_substfc_PsiF w (varc (numeral 0))

/-- La forma normalizada del objetivo de `hbody`: reflejar el nodo `nthc w i` con el
    código COMPUTADO `nthc(ẇ, ı̇)`. -/
theorem hbody_target_A3 (w i : Term)
    (h : Prf (provFromCode (nodeOkDot (tcFn w) (nthcT (tcFn w) (tcFn i))))) :
    Prf (provFromCode (substfc zero (tcFn i) (PsiF w))) :=
  prf_mp (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiF w (tcFn i)))) h

/-! ## 4 · Las obligaciones `hPl` / `hPs` (conmutación con `liftTerm` / `substTerm`) -/

theorem liftTerm_PsiF (c : Nat) (w : Term) : liftTerm c (PsiF w) = PsiF (liftTerm c w) := by
  simp only [PsiF, nodeOkDot, lorAllc, shapeDot, unDot, binDot, strBinDot, varDot,
    inFormCodeFn, eqCodeFn, andc, orc, atomc, carcT, cdrcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral,
    liftTerm_strCode]

theorem substTerm_PsiF (v : Nat) (t w : Term) :
    substTerm v t (PsiF w) = PsiF (substTerm v t w) := by
  simp only [PsiF, nodeOkDot, lorAllc, shapeDot, unDot, binDot, strBinDot, varDot,
    inFormCodeFn, eqCodeFn, andc, orc, atomc, carcT, cdrcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral,
    substTerm_strCode]

/-! ## 5 · CONTRASTE: la opción (a) — el mismo descenso CON el binder `exc` de `bdInDot`

    Aquí se mide, compilando, el coste exacto del cruce. Dos hechos:
    (i) el cruce SE PUEDE hacer con lemas existentes — no es un muro;
    (ii) pero deja `liftc zero s` sobre el valor sustituido, así que el descenso ya **no es
         genérico en `s`**: `hPsiId` deja de ser una instancia suya. -/

/-- Invariancia de `tcFn w` a NIVEL 1 (la que pide el interior del `exc`). -/
theorem substtc_inv_tcFn_at1 (w : Term) : ∀ V, Prf (substtc (succ zero) V (tcFn w) =eq tcFn w) :=
  fun V => prf_substtc_tcFn_at 1 V w

/-- `⌜v₀⌝` (la variable LIGADA por el `exc`) sobrevive a `substtc` de nivel 1. -/
theorem prf_substtc_varc0_at1 (V : Term) :
    Prf (substtc (succ zero) V (varc (numeral 0)) =eq varc (numeral 0)) :=
  prf_mp (prf_substtc_var_lt (succ zero) V (numeral 0)) (prf_gnum_lt (by omega : 0 < 1))

/-- **EL CRUCE DEL BINDER, COMPILADO.** `substfc zero s` entra en el `bdExCode` de `bdInDot`
    y llega al hueco: pero lo que llega ahí es `liftc zero s`, no `s`. -/
theorem prf_substfc_bdInDot_cross (s w A A' : Term)
    (hA : Prf (substtc (succ zero) (liftc zero s) A =eq A')) :
    Prf (substfc zero s
          (bdExCode (lencT (tcFn w)) (eqCodeFn (nthcT (tcFn w) (varc (numeral 0))) A))
      =eq bdExCode (lencT (tcFn w)) (eqCodeFn (nthcT (tcFn w) (varc (numeral 0))) A')) := by
  unfold bdExCode
  refine prf_eq_trans (prf_substfc_ex zero s _) (prf_congr_exc ?_)
  refine prf_eq_trans (prf_substfc_and (succ zero) (liftc zero s) _ _) (prf_congr_andc ?_ ?_)
  · -- la COTA: átomo `<`, a mano (no hay `prf_substfc_ltCodeFn_varc0` a nivel 1)
    show Prf (substfc (succ zero) (liftc zero s)
        (atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (lencT (tcFn w)) nil)))
      =eq atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (lencT (tcFn w)) nil)))
    refine prf_eq_trans (prf_substfc_atom (succ zero) (liftc zero s) (strCode lt_sym) _) ?_
    refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
    refine prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero s) _ _) ?_
    refine prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0_at1 (liftc zero s))) ?_
    refine prf_congr_cons_tail ?_
    have hlen : Prf (substtc (succ zero) (liftc zero s) (lencT (tcFn w)) =eq lencT (tcFn w)) :=
      prf_eq_trans (prf_substtc_lencT (succ zero) (liftc zero s) (tcFn w))
        (prf_congr_lencT (substtc_inv_tcFn_at1 w (liftc zero s)))
    exact prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero s) _ _)
      (prf_eq_trans (prf_congr_cons_head hlen)
        (prf_congr_cons_tail (prf_substtsc_nil (succ zero) (liftc zero s))))
  · -- el CUERPO: aquí llega el hueco, pero con `liftc zero s` encima
    refine prf_eq_trans (prf_substfc_eq (succ zero) (liftc zero s) _ _)
      (prf_congr_eqCodeFn ?_ hA)
    exact prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero s) _ _)
      (prf_congr_nthcT (substtc_inv_tcFn_at1 w (liftc zero s))
        (prf_substtc_varc0_at1 (liftc zero s)))

/-- Y ésta es la razón por la que el cruce ROMPE la genericidad: el hueco exterior tiene que
    escribirse `⌜v₁⌝` bajo el binder, y `substtc zero` lo DECREMENTA (`prf_substtc_var_gt`) ⇒
    colisiona con la variable ligada del `exc`. El chasis de A1 (`PrfH_bdEx_intro_open`,
    `pcc_bdEx_intro`) está cableado para UNA sola code‑var libre en el cuerpo. -/
theorem prf_varc1_collapses (V : Term) :
    Prf (substtc zero V (varc (numeral 1)) =eq varc (numeral 0)) := by
  refine prf_eq_trans (prf_mp (prf_substtc_var_gt zero V (numeral 1)) ?_) ?_
  · exact prf_gnum_lt (by omega : 0 < 1)
  · exact prf_congr_cons_tail (prf_congr_cons_head (prf_pred_succ zero))

/-! ## 6 · LA ÚNICA PIEZA NUEVA que pide la formulación recomendada:
    el puente `bdInDot ⇒ ⌜In⌝` DENTRO de `Prov` (gemelo exacto de `pcc_ltBwd_computed`). -/

noncomputable def bdInB (w : Term) : Term := lencT (liftc zero (tcFn w))
noncomputable def bdInPhic (x w : Term) : Term :=
  eqCodeFn (nthcT (liftc zero (tcFn w)) (varc (numeral 0))) (liftc zero (tcFn x))
noncomputable def bdInDot (x w : Term) : Term := bdExCode (bdInB w) (bdInPhic x w)

/-- `(∃i<lenc L. nthc L i = x) ⇒ In x L` con `x = #1`, `L = #0`. -/
def phiInBwd : Formula := Formula.impl (boundedIn (.var 1) (.var 0)) (In (.var 1) (.var 0))

theorem InBwd : Prf (forall_2 phiInBwd) :=
  Prf.gen _ (Prf.gen _ (prf_In_of_boundedIn (.var 1) (.var 0)))

/-- **EL PUENTE**: `⊢ Prov(⌜ (∃i<lenc(ẇ). nthc(ẇ,i)=ẋ) ⇒ ẋ ∈ ẇ ⌝)`, `x`, `w` ABSTRACTOS.
    Compuesto con A1 (`pcc_In_tracked`) por MP interno da el reflector del ÁTOMO `In`. -/
theorem pcc_InBwd_computed (x w : Term) :
    Prf (provFromCode (implc (bdInDot x w) (inFormCodeFn (tcFn x) (tcFn w)))) := by
  let A : Term := tcFn x
  let B : Term := tcFn w
  let W : Term := liftc zero A
  have h0 : Prf (provFromCode (substfc zero B (substfc (succ zero) W (formCode phiInBwd)))) :=
    pcc_thm_inst2 phiInBwd InBwd A B
  -- (1) `substfc` INTERNO (nivel 1): computa por `rfl` a `substCodeF 1 W phiInBwd`
  have hin : Prf (substfc (succ zero) W (formCode phiInBwd)
      =eq implc (exc (andc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                           (eqCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0)))
                                     (liftc zero W))))
                (inFormCodeFn W (varc (numeral 0)))) :=
    prf_substfc_arith_open 1 W phiInBwd
  have h1 := prf_mp (prf_provCode_congr (prf_congr_substfc3 hin)) h0
  -- (2) `substfc` EXTERNO (nivel 0, testigo `B`)
  have hv1 : ∀ t : Term, Prf (substtc (succ zero) t (varc (numeral 1)) =eq t) := fun t =>
    prf_mp (prf_substtc_var_eq (succ zero) t (numeral 1)) (prf_refl _)
  have hWnorm : ∀ t : Term, Prf (substtc (succ zero) t (liftc zero W) =eq liftc zero A) := by
    intro t
    refine prf_eq_trans (prf_congr_substtc3 (prf_congr_liftc (prf_liftc_tcFn x))) ?_
    refine prf_eq_trans (prf_congr_substtc3 (prf_liftc_tcFn x)) ?_
    exact prf_eq_trans (prf_substtc_tcFn_at 1 t x) (prf_eq_symm (prf_liftc_tcFn x))
  have hout : Prf (substfc zero B
      (implc (exc (andc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                        (eqCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0)))
                                  (liftc zero W))))
             (inFormCodeFn W (varc (numeral 0))))
      =eq implc (bdInDot x w) (inFormCodeFn A B)) := by
    refine prf_eq_trans (prf_substfc_impl zero B _ _) (prf_congr_implc ?_ ?_)
    · -- lado `∃`: cruza el binder (nivel 1, testigo `liftc 0 B`)
      refine prf_eq_trans (prf_substfc_ex zero B _) (prf_congr_exc ?_)
      refine prf_eq_trans (prf_substfc_and (succ zero) (liftc zero B) _ _)
        (prf_congr_andc ?_ ?_)
      · show Prf (substfc (succ zero) (liftc zero B)
            (atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (lencT (varc (numeral 1))) nil)))
          =eq atomc (strCode lt_sym) (cons (varc (numeral 0)) (cons (bdInB w) nil)))
        refine prf_eq_trans (prf_substfc_atom (succ zero) (liftc zero B) (strCode lt_sym) _) ?_
        refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
        have hlen : Prf (substtc (succ zero) (liftc zero B) (lencT (varc (numeral 1)))
            =eq bdInB w) :=
          prf_eq_trans (prf_substtc_lencT (succ zero) (liftc zero B) (varc (numeral 1)))
            (prf_congr_lencT (hv1 (liftc zero B)))
        refine prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero B) _ _) ?_
        refine prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0_at1 (liftc zero B))) ?_
        refine prf_congr_cons_tail ?_
        exact prf_eq_trans (prf_substtsc_cons (succ zero) (liftc zero B) _ _)
          (prf_eq_trans (prf_congr_cons_head hlen)
            (prf_congr_cons_tail (prf_substtsc_nil (succ zero) (liftc zero B))))
      · refine prf_eq_trans (prf_substfc_eq (succ zero) (liftc zero B) _ _)
          (prf_congr_eqCodeFn ?_ (hWnorm (liftc zero B)))
        exact prf_eq_trans (prf_substtc_nthcT (succ zero) (liftc zero B) _ _)
          (prf_congr_nthcT (hv1 (liftc zero B)) (prf_substtc_varc0_at1 (liftc zero B)))
    · show Prf (substfc zero B (atomc (strCode in_sym) (cons W (cons (varc (numeral 0)) nil)))
        =eq atomc (strCode in_sym) (cons A (cons B nil)))
      refine prf_eq_trans (prf_substfc_atom zero B (strCode in_sym) _) ?_
      refine prf_congr_cons_tail (prf_congr_cons_tail (prf_congr_cons_head ?_))
      refine prf_eq_trans (prf_substtsc_cons zero B W (cons (varc (numeral 0)) nil)) ?_
      refine prf_eq_trans (prf_congr_cons_head
        (prf_eq_trans (substtc_inv_liftc_tcFn x B) (prf_liftc_tcFn x))) ?_
      refine prf_congr_cons_tail ?_
      exact prf_eq_trans (prf_substtsc_cons zero B (varc (numeral 0)) nil)
        (prf_eq_trans (prf_congr_cons_head (prf_substtc_varc0 B))
          (prf_congr_cons_tail (prf_substtsc_nil zero B)))
  exact prf_mp (prf_provCode_congr hout) h1

/-! ## 7 · CIERRE DEL LAZO: A1 (copiada de `sondeos/InTracked.lean`) + el puente
    = el reflector del ÁTOMO `In`, que es lo que consume `nodeOkDot`. -/

theorem substtc_inv_bdInB (w : Term) : ∀ W, Prf (substtc zero W (bdInB w) =eq bdInB w) :=
  substtc_inv_lencT (substtc_inv_liftc_tcFn w)

theorem liftTerm_bdInDot (c : Nat) (x w : Term) :
    liftTerm c (bdInDot x w) = bdInDot (liftTerm c x) (liftTerm c w) := by
  unfold bdInDot bdInB bdInPhic bdExCode
  simp only [exc, andc, ltCodeFn, atom2CodeFn, eqCodeFn, lencT, nthcT, funcc, varc, liftc, tcFn,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- **A1** (copia literal del sondeo ya compilado). -/
theorem pcc_boundedIn_tracked (x w : Term) :
    Prf (boundedIn x w ⇒ provFromCode (bdInDot x w)) := by
  refine prf_deduction ?_
  have hex : PrfH [boundedIn x w] (boundedIn x w) := prfH_hyp_self _
  refine PrfH_ex_elim hex ?_
  rw [liftFormula_provFromCode_open, liftTerm_bdInDot]
  let X : Term := liftTerm 0 x
  let W : Term := liftTerm 0 w
  let exBody : Formula := land (lt (.var 0) (liftTerm 0 (lenc w)))
    (Formula.eq (nthc (liftTerm 0 w) (.var 0)) (liftTerm 0 x))
  let Γ' : List Formula := [exBody, liftFormula 0 (boundedIn x w)]
  show PrfH Γ' (provFromCode (bdInDot X W))
  have hC : PrfH Γ' exBody := PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH Γ' (lt (.var 0) (lenc W)) := PrfH_and_elim_left hC
  have hbody : PrfH Γ' (Formula.eq (nthc W (.var 0)) X) := PrfH_and_elim_right hC
  have hlt1 : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (tcFn (lenc W)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_lt_tracked (.var 0) (lenc W)) _) hlt
  have hBeq : Prf (provFromCode (eqc (bdInB W) (tcFn (lenc W)))) :=
    prf_mp (prf_provCode_congr
      (prf_congr_eqCodeFn (prf_congr_lencT (prf_eq_symm (prf_liftc_tcFn W))) (prf_refl _)))
      (pcc_eval_lenc W)
  have hBsym : PrfH Γ' (provFromCode (eqc (tcFn (lenc W)) (bdInB W))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_bdInB W) (prf_to_prfH hBeq _)
  have hcompLt : ∀ t : Term, Prf (substfc zero t (ltCodeFn (tcFn (.var 0)) (varc (numeral 0)))
      =eq ltCodeFn (tcFn (.var 0)) t) := fun t =>
    prf_substfc_ltCodeFn_snd (tcFn (.var 0)) t (substtc_inv_tcFn (.var 0))
  have hA1 : PrfH Γ' (provFromCode (substfc zero (tcFn (lenc W))
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcompLt _))) _) hlt1
  have hA2 : PrfH Γ' (provFromCode (substfc zero (bdInB W)
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH_leibniz_apply _ _ _ hBsym hA1
  have hltB : PrfH Γ' (provFromCode (ltCodeFn (tcFn (.var 0)) (bdInB W))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcompLt _)) _) hA2
  have hev : PrfH Γ' (provFromCode (eqCodeFn (nthcT (tcFn W) (tcFn (.var 0)))
      (tcFn (nthc W (.var 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc W (.var 0)) _) hlt
  have hcodeq : PrfH Γ' (eqCodeFn (nthcT (tcFn W) (tcFn (.var 0))) (tcFn (nthc W (.var 0)))
      =eq eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0))) (liftc zero (tcFn X))) :=
    PrfH_congr_eqCodeFn
      (prf_to_prfH (prf_congr_nthcT (prf_eq_symm (prf_liftc_tcFn W)) (prf_refl _)) _)
      (PrfH_eq_trans (PrfH_congr_tcFn hbody) (prf_to_prfH (prf_eq_symm (prf_liftc_tcFn X)) _))
  have hphi0 : PrfH Γ' (provFromCode (eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0)))
      (liftc zero (tcFn X)))) := PrfH_provCode_congr hcodeq hev
  have hcompPhi : Prf (substfc zero (tcFn (.var 0)) (bdInPhic X W)
      =eq eqCodeFn (nthcT (liftc zero (tcFn W)) (tcFn (.var 0))) (liftc zero (tcFn X))) := by
    unfold bdInPhic
    refine prf_eq_trans (prf_substfc_eq zero (tcFn (.var 0)) _ _) ?_
    refine prf_congr_eqCodeFn ?_ (substtc_inv_liftc_tcFn X (tcFn (.var 0)))
    refine prf_eq_trans (prf_substtc_nthcT zero (tcFn (.var 0)) _ _) ?_
    exact prf_congr_nthcT (substtc_inv_liftc_tcFn W (tcFn (.var 0)))
      (prf_substtc_varc0 (tcFn (.var 0)))
  have hphi : PrfH Γ' (provFromCode (substfc zero (tcFn (.var 0)) (bdInPhic X W))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm hcompPhi)) _) hphi0
  exact PrfH_bdEx_intro_open (bdInB W) (bdInPhic X W) (tcFn (.var 0))
    (substtc_inv_bdInB W) hltB hphi

/-- **EL RESULTADO QUE HACE VIABLE LA FORMULACIÓN RECOMENDADA**: reflexión del `In` como
    ÁTOMO, con `x` y `w` ABSTRACTOS. Es A1 seguido de UN MP interno con el puente. -/
theorem pcc_In_atom_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w))) := by
  refine prf_deduction ?_
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _)
      (prfH_hyp_self _)
  have h1 : PrfH [In x w] (provFromCode (bdInDot x w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_InBwd_computed x w) _) h1

end A3Scout

#print axioms A3Scout.pcc_In_atom_tracked
#print axioms A3Scout.pcc_InBwd_computed
#print axioms A3Scout.prf_substfc_bdInDot_cross
#print axioms A3Scout.prf_varc1_collapses
#print axioms A3Scout.prf_substfc_nodeOkDot_gen
#print axioms A3Scout.prf_substfc_PsiF
#print axioms A3Scout.hPsiId_A3
#print axioms A3Scout.hbody_target_A3
#print axioms A3Scout.liftTerm_PsiF
#print axioms A3Scout.substTerm_PsiF
