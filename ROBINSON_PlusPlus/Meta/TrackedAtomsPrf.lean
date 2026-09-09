import ROBINSON_PlusPlus.Meta.BdAllIntroPrf
import ROBINSON_PlusPlus.Meta.D3InDotPrf
import ROBINSON_PlusPlus.Meta.InAxiomsCodePrf
import ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf
import ROBINSON_PlusPlus.Meta.CodeTreeReflect
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
import ROBINSON_PlusPlus.Meta.LiftcCodePrf
/-!
# `Meta/TrackedAtomsPrf.lean` — el KIT GENÉRICO de reflexión Σ₁, con argumentos ABSTRACTOS

Reflejar una fórmula Δ₀ **dentro de `Prov`** con los argumentos abstractos es la operación que
piden a la vez **C3** (los reflectores `DEUDA_hGuardT`/`DEUDA_hGuardF` de
`Meta/LineWFGuardPrf.lean`) y **D3** (`DEUDA_chainOkBDot` de `Meta/D3ChainDotPrf.lean`). Este
módulo pone en producción las piezas **genéricas** de esa operación, promovidas de
`sondeos/A3IsFCBTracked.lean`:

    pcc_boundedIn_tracked (x w) : Prf (boundedIn x w ⇒ provFromCode (bdInDot x w))
    pcc_In_atom_tracked   (x w) : Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w)))
    pcc_shape_tracked   (X k n) : la forma `carc X = k̇ ∧ lenc X = ṅ`, reflejada
    pcc_child_tracked (q X j n) : la casilla `j`-ésima de un nodo de longitud `n`
    pcc_carcIn_tracked  (q X)   ·  pcc_cdrcIn_tracked (q X)

⭐ **`pcc_In_atom_tracked` es la pieza clave**: `In` es un **átomo** del lenguaje
(`Minimal/Axioms.lean:149`), y reflejarlo con `x` y `w` **abstractos** es lo que permite que
`isTC1 w c = wfAll1 w ∧ In c w` —la guarda de ADR‑020— se refleje por partes. La ruta es
`prf_In_iff_boundedIn` (`Meta/BoundedInPrf.lean:391`) → `pcc_boundedIn_tracked` → transporte
por `pcc_InBwd_computed`.

## Por qué esto vale para los dos frentes

`sondeos/A3IsFCBTracked.lean` probó `pcc_isFCB_tracked (w c) : isFCB w c ⇒ Prov(⌜isFCBDot w c⌝)`
con `isFCB w c = wfAll w ∧ In c w`. **Esa es exactamente la forma de `isTC1`**, y `isTC1` es lo
que hay dentro de `hasWit`. El kit de abajo es la mitad de aquel trabajo que **no depende del
predicado de nodo** — y por eso sirve igual para `isTermCodeE1` (término, C3‑T), para
`isFormCodeE2` (fórmula, C3‑F) y para `lineOkB` (D3).

⚠️ **Lo que NO sube y por qué.** De las 81 declaraciones del sondeo, aquí entran **21**: el
cierre transitivo de las seis piezas genéricas, sin un solo homónimo. El resto es el predicado
de nodo **concreto** de aquel frente (`nodeOk`, sus ocho disyuntos y su imagen punteada), que
no es reutilizable: cada frente tiene el suyo.

⚠️ **Y una diferencia de diseño que hay que tener presente al reusarlo**: aquel sondeo eligió
deliberadamente meter el `In` **como ÁTOMO** y no como su despliegue `∃`‑acotado, para que el
cuerpo del `∀` acotado **no tuviera ningún binder** y todo el descenso de `substfc` viviera en
nivel 0. `isTermCodeE1` **no** tiene esa propiedad: su segundo disyunto lleva
`argsIn wT (nthc X 2)`, que es un `∀` acotado **anidado**. Reusar el kit no exime de resolver
ese anidamiento.
-/

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
open ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf
open ROBINSON_PlusPlus.Meta.CodeCtorKit ROBINSON_PlusPlus.Meta.CodeTreeReflect

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.TrackedAtomsPrf

noncomputable def shapeDot (X : Term) (k n : Nat) : Term :=
  andc (eqCodeFn (carcT X) (tcFn (numeralM k))) (eqCodeFn (lencT X) (tcFn (numeralM n)))

/-- `substfc 0 s` sobre el código del átomo `In`, con hueco ANIDADO en el 1er argumento. -/
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

/-- Congruencia de `forallc` a nivel META. Producción tenía la de `exc` (`prf_congr_exc`,
    `Meta/EvalLtPrf.lean:60`) pero no ésta, y la pide cualquier descenso por un `∀` acotado. -/
theorem prf_congr_forallc {a a' : Term} (h : Prf (a =eq a')) :
    Prf (forallc a =eq forallc a') := by
  unfold forallc
  exact prf_congr_cons_tail (prf_congr_cons_head h)

/-- Congruencia de `bdAllCode` a nivel META, en sus dos argumentos. -/
theorem prf_congr_bdAllCode {B B' P P' : Term} (hB : Prf (B =eq B')) (hP : Prf (P =eq P')) :
    Prf (bdAllCode B P =eq bdAllCode B' P') := by
  unfold bdAllCode
  exact prf_congr_forallc (prf_congr_implc (prf_congr_atom2CodeFn (prf_refl _) hB) hP)

/-- Congruencia INTERNA de `nthcT` en su PRIMER argumento (molde `pcc_congr_consT_arg1_code`). -/
theorem pcc_congr_nthcT_arg1_code (B X Y : Term)
    (hB : ∀ W, Prf (substtc zero W B =eq B)) (hX : ∀ W, Prf (substtc zero W X =eq X))
    (hwB : Prf (hasWit B) := by hw_auto) (hwX : Prf (hasWit X) := by hw_auto)
    (hwY : Prf (hasWit Y) := by hw_auto) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (nthcT X B) (nthcT Y B))) := by
  let Ac : Term := eqc (nthcT X B) (nthcT (varc (numeral 0)) B)
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (nthcT X B) (nthcT w B)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (nthcT X B) (nthcT (varc (numeral 0)) B)) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · exact prf_eq_trans (prf_substtc_nthcT zero w X B) (prf_congr_nthcT (hX w) (hB w))
    · exact prf_eq_trans (prf_substtc_nthcT zero w (varc (numeral 0)) B)
        (prf_congr_nthcT (prf_substtc_varc0 w) (hB w))
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (nthcT X B))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _)
      (prf_hasWitF_eq2 (nthcT X B) (nthcT (varc (numeral 0)) B)
        (prf_hasWit_funcc2 _ X B hwX hwB)
        (prf_hasWit_funcc2 _ (varc (numeral 0)) B (prf_hasWit_varc (numeral 0)) hwB)) hwX hwY)

/-- Introducción del `∨` a nivel de código, bajo contexto (versión `PrfH` de la mitad
    izquierda de `pcc_reflect_or`). -/
theorem PrfH_orL_code {Γ : List Formula} (Ac Bc : Term) (h : PrfH Γ (provFromCode Ac)) :
    PrfH Γ (provFromCode (orc Ac Bc)) :=
  PrfH.mp _ _ _ (prf_to_prfH (prf_mp (pcc_mp_code_open Ac (orc Ac Bc)) (pcc_j1_code Ac Bc)) _) h

/-- Idem, mitad derecha. -/
theorem PrfH_orR_code {Γ : List Formula} (Ac Bc : Term) (h : PrfH Γ (provFromCode Bc)) :
    PrfH Γ (provFromCode (orc Ac Bc)) :=
  PrfH.mp _ _ _ (prf_to_prfH (prf_mp (pcc_mp_code_open Bc (orc Ac Bc)) (pcc_j2_code Ac Bc)) _) h

/-! ### La congruencia de `bdAllCode` en su COTA, DENTRO de `Prov`

⚠️ Hace falta porque la cota de un `∀` acotado **va dentro del `forallc`**
(`bdAllCode B Phic = forallc (implc (ltCodeFn ⌜v₀⌝ B) Phic)`), y el paso de `tcFn (lenc Y)` a
`lencT Ẏ` —que es `pcc_eval_lenc`— **sólo vale dentro de `Prov`**: los dos términos no son
iguales a nivel objeto. Así que el transporte de la cota tiene que hacerse ahí dentro.

🔑 **El truco es el mismo de `wfAll1Psi`**: el hueco del Leibniz se escribe `⌜v₁⌝`, de modo que
`substfc zero ·` lo alcanza al bajar por el `forallc` (donde el nivel sube a `σ0`). -/

/-- El contexto de Leibniz para transportar la cota: el hueco es `⌜v₁⌝`, que queda a nivel `σ0`
    justo dentro del `forallc`. -/
noncomputable def bdAllBndCtx (Phic : Term) : Term :=
  bdAllCode (varc (succ (numeral 0))) Phic

/-- Y así se computa: rellenar el hueco da el `bdAllCode` con la cota lifteada. -/
theorem prf_substfc_bdAllBndCtx (Phic s : Term)
    (hPinv : ∀ u : Term, Prf (substfc (succ zero) u Phic =eq Phic)) :
    Prf (substfc zero s (bdAllBndCtx Phic) =eq bdAllCode (liftc zero s) Phic) := by
  unfold bdAllBndCtx bdAllCode
  refine prf_eq_trans (prf_substfc_forall zero s _) (prf_congr_forallc ?_)
  refine prf_eq_trans (prf_substfc_impl (succ zero) (liftc zero s) _ _)
    (prf_congr_implc ?_ (hPinv (liftc zero s)))
  refine prf_eq_trans (prf_substfc_atom2CodeFn (succ zero) (liftc zero s) lt_sym _ _) ?_
  refine prf_congr_atom2CodeFn
    (prf_mp (prf_substtc_var_lt (succ zero) (liftc zero s) (numeral 0)) (prf_zero_lt_succ zero))
    ?_
  exact prf_mp (prf_substtc_var_eq (succ zero) (liftc zero s) (succ (numeral 0))) (prf_refl _)

/-- ⭐ **LA CONGRUENCIA DE LA COTA, DENTRO DE `Prov`.** Con `B` y `B'` **cerrados** a nivel de
    código (que es el caso: son `tcFn …` o `lencT (tcFn …)`), el `liftc` se colapsa y queda la
    congruencia limpia. -/
theorem PrfH_bdAllCode_congr_bnd {Γ : List Formula} (B B' Phic : Term)
    (hPinv : ∀ u : Term, Prf (substfc (succ zero) u Phic =eq Phic))
    (hBc : Prf (liftc zero B =eq B)) (hBc' : Prf (liftc zero B' =eq B'))
    (hB : PrfH Γ (provFromCode (eqCodeFn B B')))
    (h : PrfH Γ (provFromCode (bdAllCode B Phic)))
    (hwB : Prf (hasWit B) := by hw_auto) (hwB' : Prf (hasWit B') := by hw_auto)
    (hwP : Prf (hasWitF (bdAllBndCtx Phic)) := by hw_auto) :
    PrfH Γ (provFromCode (bdAllCode B' Phic)) := by
  have hcomp : ∀ u : Term, Prf (substfc zero u (bdAllBndCtx Phic)
      =eq bdAllCode (liftc zero u) Phic) := fun u => prf_substfc_bdAllBndCtx Phic u hPinv
  have hB0 : PrfH Γ (provFromCode (substfc zero B (bdAllBndCtx Phic))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm
      (prf_eq_trans (hcomp B) (prf_congr_bdAllCode hBc (prf_refl Phic))))) _) h
  have hB1 : PrfH Γ (provFromCode (substfc zero B' (bdAllBndCtx Phic))) :=
    PrfH_leibniz_apply _ B B' hB hB0 hwP hwB hwB'
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr
    (prf_eq_trans (hcomp B') (prf_congr_bdAllCode hBc' (prf_refl Phic)))) _) hB1

/-! ### KIT de distribución de `liftc` sobre los constructores DOTADOS

⭐ **Esto es lo que de verdad hacía falta para el `pcc_bdAll_intro` exterior**, y no el lema
general de sustitución/lift. Cuando un `∀` acotado va **anidado**, lo que va dentro del binder
hay que pre‑`liftc`‑arlo (idiom de `bdInB` en `sondeos/A3IsFCBTracked.lean:318`), y allí el
argumento era **cerrado** (`tcFn w`), así que `prf_liftc_tcFn` lo colapsaba. Con un argumento
que **contiene el hueco del índice** eso ya no vale… pero tampoco hace falta el lema general
`substtc (σv) (liftc 0 t) (liftc 0 Z) =eq liftc 0 (substtc v t Z)` con `Z` **arbitrario**: los
`Z` que aparecen son códigos de **forma conocida**, y basta con que `liftc` sepa atravesar sus
constructores. Eso es este kit, y son cinco líneas por constructor.

Los axiomas objeto ya estaban (`ax_liftc_var_ge`, `ax_liftc_func`, `ax_liftsc_nil/cons`); lo
único que faltaba era componerlos. -/

/-- `liftc 0 ⌜v₀⌝ = ⌜v₁⌝`: el desplazamiento del hueco al entrar en un binder.

    ⚠️ **Instancia `v := 0`** de `prf_liftc_varc_numeral` (`Meta/SubstCodeOpenPrf.lean` §5),
    la versión genérica bajada por ADR‑019 el 2026‑09‑10. Se conserva el nombre porque tiene
    **tres consumidores**; lo que se retira es la derivación duplicada. -/
theorem prf_liftc_varc0 : Prf (liftc zero (varc (numeral 0)) =eq varc (succ (numeral 0))) :=
  ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf.prf_liftc_varc_numeral 0

/-- `liftc` atraviesa un constructor dotado UNARIO. -/
theorem prf_liftc_funcc1 (c s a : Term) :
    Prf (liftc c (funcc s (cons a nil)) =eq funcc s (cons (liftc c a) nil)) :=
  prf_eq_trans (prf_liftc_func c s _)
    (prf_congr_funcc2 (prf_eq_trans (prf_liftsc_cons c a nil)
      (prf_congr_cons_tail (prf_liftsc_nil c))))

/-- `liftc` atraviesa un constructor dotado BINARIO. -/
theorem prf_liftc_funcc2 (c s a b : Term) :
    Prf (liftc c (funcc s (cons a (cons b nil)))
      =eq funcc s (cons (liftc c a) (cons (liftc c b) nil))) :=
  prf_eq_trans (prf_liftc_func c s _)
    (prf_congr_funcc2 (prf_eq_trans (prf_liftsc_cons c a (cons b nil))
      (prf_congr_cons_tail (prf_eq_trans (prf_liftsc_cons c b nil)
        (prf_congr_cons_tail (prf_liftsc_nil c))))))

/-- `liftc` atraviesa `nthcT`. -/
theorem prf_liftc_nthcT (c x y : Term) :
    Prf (liftc c (nthcT x y) =eq nthcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "nthc") x y

/-- `liftc` atraviesa `lencT`. -/
theorem prf_liftc_lencT (c x : Term) :
    Prf (liftc c (lencT x) =eq lencT (liftc c x)) :=
  prf_liftc_funcc1 c (strCode "lenc") x

/-- `liftc` atraviesa `carcT`. -/
theorem prf_liftc_carcT (c x : Term) :
    Prf (liftc c (carcT x) =eq carcT (liftc c x)) :=
  prf_liftc_funcc1 c (strCode "carc") x

/-- `liftc` atraviesa `cdrcT`. -/
theorem prf_liftc_cdrcT (c x : Term) :
    Prf (liftc c (cdrcT x) =eq cdrcT (liftc c x)) :=
  prf_liftc_funcc1 c (strCode "cdrc") x

/-- **`substfc` sobre una forma `shapeDot`**: sólo toca la ranura del nodo. Es la pieza que
    consume cualquier recorrido de disyuntos por forma (C3‑T, C3‑F). -/
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

/-- La misma, a **nivel arbitrario**: la pide cualquier invariancia bajo un binder. -/
theorem prf_substfc_shapeDot_at (v s X X' : Term) (k n : Nat)
    (hX : Prf (substtc v s X =eq X'))
    (hk : Prf (substtc v s (tcFn (numeralM k)) =eq tcFn (numeralM k)))
    (hn : Prf (substtc v s (tcFn (numeralM n)) =eq tcFn (numeralM n))) :
    Prf (substfc v s (shapeDot X k n) =eq shapeDot X' k n) := by
  unfold shapeDot
  refine prf_eq_trans (prf_substfc_and v s _ _) (prf_congr_andc ?_ ?_)
  · refine prf_eq_trans (prf_substfc_eq v s _ _) (prf_congr_eqCodeFn ?_ hk)
    exact prf_eq_trans (prf_substtc_carcT v s X) (prf_congr_carcT hX)
  · refine prf_eq_trans (prf_substfc_eq v s _ _) (prf_congr_eqCodeFn ?_ hn)
    exact prf_eq_trans (prf_substtc_lencT v s X) (prf_congr_lencT hX)

/-! ### ⭐ La forma posicional, reflejada a su código `formCode` LITERAL (vía `CTree`)

`shapeDot` es la forma `carc X = k̇ ∧ lenc X = ṅ` — la que `pcc_shape_tracked` sabe producir.
Pero el `condD` de ADR‑020 **no admite elegir imagen**: pide la de `formCode`, y
`formCode (shapeUn X k)` es la **ECUACIÓN** `Ẋ = ⟨k̄, nthcT Ẋ 1̄⟩`, no la conjunción de
accesores. Las dos son equivalentes en la teoría objeto, pero son **códigos distintos**.

⭐ No hace falta ningún teorema objeto nuevo para cruzar ese hueco: `Meta/CodeTreeReflect.lean`
ya tiene, genérico y probado **por inducción sobre el árbol**, todo lo que se necesita —
`pcc_tc_objAt` (el «código del código» del árbol) y `PrfH_dotVN` (el paso de valores punteados
a accesores rastreados). Aquí sólo se componen, y el resultado sirve para cualquier forma
posicional de cualquier frente. -/

/-- ⭐ **UNA FORMA POSICIONAL, REFLEJADA DIRECTAMENTE A SU CÓDIGO `formCode`.**

    `S` es la hipótesis de la que se saca la forma (típicamente `shapeUn X k` o `shapeBin X k`);
    `hsh` dice que `S` da la ecuación posicional y `hlen` su longitud, que es lo que
    `PrfH_dotVN` necesita para acotar los índices de las hojas. -/
theorem pcc_shape_tree (X : Term) (T : CTree) {n : Nat} (hmax : Nat.le (CTree.maxLeaf T) n)
    (S : Formula) (hsh : Prf (S ⇒ (X =eq T.objAt X)))
    (hlen : Prf (S ⇒ (lenc X =eq numeralM n))) :
    Prf (S ⇒ provFromCode (eqCodeFn (tcFn X) (T.dotN X))) := by
  refine prf_deduction ?_
  have hS : PrfH [S] S := prfH_hyp_self S
  have h1 : PrfH [S] (provFromCode (eqCodeFn (tcFn X) (tcFn (T.objAt X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked X (T.objAt X)) _)
      (PrfH.mp _ _ _ (prf_to_prfH hsh _) hS)
  have h12 : PrfH [S] (provFromCode (eqc (tcFn X) (T.dotV X))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_tcFn X) h1
      (prf_to_prfH (pcc_tc_objAt X T) _)
      (prf_hasWit_tcFn X) (prf_hasWit_tcFn (T.objAt X)) (prf_hasWit_dotV X T)
  exact PrfH_eq_trans_code _ _ _ (substtc_inv_tcFn X) h12
    (PrfH_dotVN X (PrfH.mp _ _ _ (prf_to_prfH hlen _) hS) T hmax)
    (prf_hasWit_tcFn X) (prf_hasWit_dotV X T) (prf_hasWit_dotN X T)

/-- **`substtc` sobre la casilla `k`‑ésima dotada**: idem, sólo la ranura del nodo. -/
theorem prf_substtc_child (s X X' : Term) (k : Nat)
    (hX : Prf (substtc zero s X =eq X')) :
    Prf (substtc zero s (nthcT X (tcFn (numeralM k))) =eq nthcT X' (tcFn (numeralM k))) :=
  prf_eq_trans (prf_substtc_nthcT zero s X (tcFn (numeralM k)))
    (prf_congr_nthcT hX (substtc_inv_tcFn (numeralM k) s))

/-- Transporte de la ranura del nodo dentro de una `shapeDot`, DENTRO de `Prov`. -/
theorem PrfH_shapeDot_transport {Γ : List Formula} (u v : Term) (k n : Nat)
    (hu : ∀ W, Prf (substtc zero W u =eq u)) (hv : ∀ W, Prf (substtc zero W v =eq v))
    (heq : PrfH Γ (provFromCode (eqCodeFn u v)))
    (h : PrfH Γ (provFromCode (shapeDot u k n)))
    (hwu : Prf (hasWit u) := by hw_auto) (hwv : Prf (hasWit v) := by hw_auto) :
    PrfH Γ (provFromCode (shapeDot v k n)) := by
  have hcomp : ∀ w : Term, Prf (substfc zero w (shapeDot (varc (numeral 0)) k n)
      =eq shapeDot w k n) := fun w =>
    prf_substfc_shapeDot w (varc (numeral 0)) w k n (prf_substtc_varc0 w)
  have h0 : PrfH Γ (provFromCode (substfc zero u (shapeDot (varc (numeral 0)) k n))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp u))) _) h
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp v)) _)
    (PrfH_leibniz_apply _ u v heq h0 (by hw_auto) hwu hwv)

noncomputable def bdInB (w : Term) : Term := lencT (liftc zero (tcFn w))

noncomputable def bdInPhic (x w : Term) : Term :=
  eqCodeFn (nthcT (liftc zero (tcFn w)) (varc (numeral 0))) (liftc zero (tcFn x))

noncomputable def bdInDot (x w : Term) : Term := bdExCode (bdInB w) (bdInPhic x w)

theorem substtc_inv_bdInB (w : Term) : ∀ W, Prf (substtc zero W (bdInB w) =eq bdInB w) :=
  substtc_inv_lencT (substtc_inv_liftc_tcFn w)

theorem liftTerm_bdInDot (c : Nat) (x w : Term) :
    liftTerm c (bdInDot x w) = bdInDot (liftTerm c x) (liftTerm c w) := by
  unfold bdInDot bdInB bdInPhic bdExCode
  simp only [exc, andc, ltCodeFn, atom2CodeFn, eqCodeFn, lencT, nthcT, funcc, varc, liftc, tcFn,
    cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_numeral, liftTerm_strCode]

/-- **A1** (copia literal de `sondeos/InTracked.lean`). -/
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
    PrfH_eq_symm_code _ _ (substtc_inv_bdInB W) (prf_to_prfH hBeq _) (by hw_auto) (by hw_auto)
  have hcompLt : ∀ t : Term, Prf (substfc zero t (ltCodeFn (tcFn (.var 0)) (varc (numeral 0)))
      =eq ltCodeFn (tcFn (.var 0)) t) := fun t =>
    prf_substfc_ltCodeFn_snd (tcFn (.var 0)) t (substtc_inv_tcFn (.var 0))
  have hA1 : PrfH Γ' (provFromCode (substfc zero (tcFn (lenc W))
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcompLt _))) _) hlt1
  have hA2 : PrfH Γ' (provFromCode (substfc zero (bdInB W)
      (ltCodeFn (tcFn (.var 0)) (varc (numeral 0))))) :=
    PrfH_leibniz_apply _ _ _ hBsym hA1 (by hw_auto) (by hw_auto) (by hw_auto)
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
    (substtc_inv_bdInB W) hltB hphi (by hw_auto) (by hw_auto) (by hw_auto)

def phiInBwd : Formula := Formula.impl (boundedIn (.var 1) (.var 0)) (In (.var 1) (.var 0))

theorem InBwd : Prf (forall_2 phiInBwd) :=
  Prf.gen _ (Prf.gen _ (prf_In_of_boundedIn (.var 1) (.var 0)))

theorem prf_substtc_varc0_at1 (V : Term) :
    Prf (substtc (succ zero) V (varc (numeral 0)) =eq varc (numeral 0)) :=
  prf_mp (prf_substtc_var_lt (succ zero) V (numeral 0)) (prf_gnum_lt (by omega : 0 < 1))

/-- **EL PUENTE**: `⊢ Prov(⌜ (∃i<lenc(ẇ). nthc(ẇ,i)=ẋ) ⇒ ẋ ∈ ẇ ⌝)`, `x`, `w` ABSTRACTOS. -/
theorem pcc_InBwd_computed (x w : Term) :
    Prf (provFromCode (implc (bdInDot x w) (inFormCodeFn (tcFn x) (tcFn w)))) := by
  let A : Term := tcFn x
  let B : Term := tcFn w
  let W : Term := liftc zero A
  have h0 : Prf (provFromCode (substfc zero B (substfc (succ zero) W (formCode phiInBwd)))) :=
    pcc_thm_inst2 phiInBwd InBwd A B (by hw_auto) (by hw_auto)
  have hin : Prf (substfc (succ zero) W (formCode phiInBwd)
      =eq implc (exc (andc (ltCodeFn (varc (numeral 0)) (lencT (varc (numeral 1))))
                           (eqCodeFn (nthcT (varc (numeral 1)) (varc (numeral 0)))
                                     (liftc zero W))))
                (inFormCodeFn W (varc (numeral 0)))) :=
    prf_substfc_arith_open 1 W phiInBwd
  have h1 := prf_mp (prf_provCode_congr (prf_congr_substfc3 hin)) h0
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
    · refine prf_eq_trans (prf_substfc_ex zero B _) (prf_congr_exc ?_)
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

/-- **Reflexión del `In` como ÁTOMO**, con `x` y `w` ABSTRACTOS. -/
theorem pcc_In_atom_tracked (x w : Term) :
    Prf (In x w ⇒ provFromCode (inFormCodeFn (tcFn x) (tcFn w))) := by
  refine prf_deduction ?_
  have hbd : PrfH [In x w] (boundedIn x w) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_and_elim_left (prf_In_iff_boundedIn x w)) _)
      (prfH_hyp_self _)
  have h1 : PrfH [In x w] (provFromCode (bdInDot x w)) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_boundedIn_tracked x w) _) hbd
  exact PrfH_mp_code_apply (prf_to_prfH (pcc_InBwd_computed x w) _) h1

theorem PrfH_congr_cdrcT {Γ : List Formula} {x y : Term} (h : PrfH Γ (x =eq y)) :
    PrfH Γ (cdrcT x =eq cdrcT y) := by
  unfold cdrcT funcc
  exact PrfH_congr_cons_tail (PrfH_congr_cons_tail (PrfH_congr_cons_head (PrfH_congr_cons_head h)))

theorem pcc_carcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (consOk X)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_carcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_carc (carc X) (cdrc X)) _)

theorem pcc_cdrcD_bridge_cons (X : Term) :
    Prf (consOk X ⇒ provFromCode (eqCodeFn (cdrcT (tcFn X)) (tcFn (cdrc X)))) := by
  refine prf_deduction ?_
  have hcons := prfH_hyp_self (consOk X)
  exact PrfH_provCode_congr
    (PrfH_congr_eqCodeFn (PrfH_congr_cdrcT (PrfH_congr_tcFn (PrfH_eq_symm hcons)))
      (prf_to_prfH (prf_refl _) _))
    (prf_to_prfH (pcc_eval_cdrc (carc X) (cdrc X)) _)

/-- Transporte interno dentro del 1er argumento del átomo `In`. -/
theorem PrfH_in_transport {Γ : List Formula} (u v W : Term)
    (hW : ∀ V, Prf (substtc zero V W =eq W))
    (heq : PrfH Γ (provFromCode (eqc u v)))
    (h : PrfH Γ (provFromCode (inFormCodeFn u W)))
    (hwW : Prf (hasWit W) := by hw_auto) (hwu : Prf (hasWit u) := by hw_auto)
    (hwv : Prf (hasWit v) := by hw_auto) :
    PrfH Γ (provFromCode (inFormCodeFn v W)) := by
  let Cin : Term := inFormCodeFn (varc (numeral 0)) W
  have hcomp : ∀ t : Term, Prf (substfc zero t Cin =eq inFormCodeFn t W) := fun t =>
    prf_substfc_inDot t (varc (numeral 0)) t W (prf_substtc_varc0 t) hW
  have h1 : PrfH Γ (provFromCode (substfc zero u Cin)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp u))) _) h
  have h2 : PrfH Γ (provFromCode (substfc zero v Cin)) :=
    PrfH_leibniz_apply Cin u v heq h1
      (prf_hasWitF_atom2 (strCode in_sym) (varc (numeral 0)) W
        (prf_hasWit_varc (numeral 0)) hwW) hwu hwv
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp v)) _) h2

/-- Los dos `=eq` de forma: tag y longitud, ya en forma COMPUTADA (`carcT Ẋ`, `lencT Ẋ`). -/
theorem pcc_shape_tracked (X : Term) (k n : Nat) :
    Prf (consOk X ⇒ (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n))
      ⇒ provFromCode (shapeDot (tcFn X) k n))) := by
  refine prf_deduction (deduction_aux ?_
    (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)))
    [consOk X] rfl)
  let Γ : List Formula :=
    [land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n)), consOk X]
  show PrfH Γ (provFromCode (shapeDot (tcFn X) k n))
  have hsh : PrfH Γ
      (land (Formula.eq (carc X) (numeralM k)) (Formula.eq (lenc X) (numeralM n))) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hcons : PrfH Γ (consOk X) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hcarc : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (carc X)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hcons
  have hcarc2 : PrfH Γ (provFromCode (eqCodeFn (tcFn (carc X)) (tcFn (numeralM k)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (carc X) (numeralM k)) _)
      (PrfH_and_elim_left hsh)
  have hA : PrfH Γ (provFromCode (eqCodeFn (carcT (tcFn X)) (tcFn (numeralM k)))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) hcarc hcarc2
      (by hw_auto) (by hw_auto) (by hw_auto)
  have hlen : PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (lenc X)))) :=
    prf_to_prfH (pcc_eval_lenc X) Γ
  have hlen2 : PrfH Γ (provFromCode (eqCodeFn (tcFn (lenc X)) (tcFn (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (lenc X) (numeralM n)) _)
      (PrfH_and_elim_right hsh)
  have hB : PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (numeralM n)))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_lencT (substtc_inv_tcFn X)) hlen hlen2
      (by hw_auto) (by hw_auto) (by hw_auto)
  exact PrfH_and_intro_code _ _ hA hB

/-- ⭐ **La pertenencia de un hijo con el índice ABSTRACTO** — el cuerpo que pide la
    aplicación de `pcc_bdAll_intro` a un `∀` acotado **anidado** (p. ej. el `argsIn` que lleva
    dentro `isTermCodeE1`).

    Es `pcc_child_tracked` sin la parte que fuerza el índice literal, y sale **más corto**:
    allí la cota `j < lenc X` había que derivarla de `lenc X = ṅ` y `j < n`; aquí llega
    directamente como hipótesis, que es justo la forma en que `pcc_bdAll_intro` la entrega.

    🔑 Y es la pieza que muestra que **el anidamiento del `∀` acotado NO es un muro**: las dos
    aplicaciones de `pcc_bdAll_intro` son a nivel **META** (`∀ Y i` en Lean), así que el `∀`
    anidado lo está en la fórmula OBJETO, no bajo un binder de Lean. -/
theorem pcc_child_tracked_at (q Y i : Term) :
    Prf (lt i (lenc Y) ⇒ (In (nthc Y i) q ⇒
      provFromCode (inFormCodeFn (nthcT (tcFn Y) (tcFn i)) (tcFn q)))) := by
  refine prf_deduction (deduction_aux ?_ (In (nthc Y i) q) [lt i (lenc Y)] rfl)
  have hin : PrfH [In (nthc Y i) q, lt i (lenc Y)] (In (nthc Y i) q) :=
    PrfH.hyp _ _ (List.Mem.head _)
  have hlt : PrfH [In (nthc Y i) q, lt i (lenc Y)] (lt i (lenc Y)) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hev : PrfH _ (provFromCode (eqCodeFn (nthcT (tcFn Y) (tcFn i)) (tcFn (nthc Y i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc Y i) _) hlt
  have hevS : PrfH _ (provFromCode (eqCodeFn (tcFn (nthc Y i)) (nthcT (tcFn Y) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn Y) (substtc_inv_tcFn i)) hev (by hw_auto) (by hw_auto)
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (nthc Y i)) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc Y i) q) _) hin
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn q) hevS hat

/-- La pertenencia de un HIJO en la casilla `j`, en forma COMPUTADA (`nthcT Ẋ ȷ̇`). -/
theorem pcc_child_tracked (q X : Term) (j n : Nat) (hjn : j < n) :
    Prf (Formula.eq (lenc X) (numeralM n) ⇒ (In (nthc X (numeralM j)) q ⇒
      provFromCode (inFormCodeFn (nthcT (tcFn X) (tcFn (numeralM j))) (tcFn q)))) := by
  refine prf_deduction (deduction_aux ?_ (In (nthc X (numeralM j)) q)
    [Formula.eq (lenc X) (numeralM n)] rfl)
  have hin : PrfH [In (nthc X (numeralM j)) q, Formula.eq (lenc X) (numeralM n)]
      (In (nthc X (numeralM j)) q) := PrfH.hyp _ _ (List.Mem.head _)
  have hlen : PrfH [In (nthc X (numeralM j)) q, Formula.eq (lenc X) (numeralM n)]
      (Formula.eq (lenc X) (numeralM n)) := PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hlt : PrfH _ (lt (numeralM j) (lenc X)) :=
    PrfH_lt_subst2 (PrfH_eq_symm hlen)
      (prf_to_prfH (prf_lt_numeralM hjn) _)
  have hev : PrfH _ (provFromCode (eqCodeFn (nthcT (tcFn X) (tcFn (numeralM j)))
      (tcFn (nthc X (numeralM j))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM j)) _) hlt
  have hevS : PrfH _ (provFromCode (eqCodeFn (tcFn (nthc X (numeralM j)))
      (nthcT (tcFn X) (tcFn (numeralM j))))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn X) (substtc_inv_tcFn (numeralM j))) hev (by hw_auto) (by hw_auto)
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (nthc X (numeralM j))) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (nthc X (numeralM j)) q) _) hin
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn q) hevS hat

theorem pcc_carcIn_tracked (q X : Term) :
    Prf (consOk X ⇒ (In (carc X) q ⇒
      provFromCode (inFormCodeFn (carcT (tcFn X)) (tcFn q)))) := by
  refine prf_deduction (deduction_aux ?_ (In (carc X) q) [consOk X] rfl)
  have hin : PrfH [In (carc X) q, consOk X] (In (carc X) q) := PrfH.hyp _ _ (List.Mem.head _)
  have hcons : PrfH [In (carc X) q, consOk X] (consOk X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hbr := PrfH.mp _ _ _ (prf_to_prfH (pcc_carcD_bridge_cons X) _) hcons
  have hbrS : PrfH _ (provFromCode (eqCodeFn (tcFn (carc X)) (carcT (tcFn X)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) hbr (by hw_auto) (by hw_auto)
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (carc X)) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (carc X) q) _) hin
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn q) hbrS hat

theorem pcc_cdrcIn_tracked (q X : Term) :
    Prf (consOk X ⇒ (In (cdrc X) q ⇒
      provFromCode (inFormCodeFn (cdrcT (tcFn X)) (tcFn q)))) := by
  refine prf_deduction (deduction_aux ?_ (In (cdrc X) q) [consOk X] rfl)
  have hin : PrfH [In (cdrc X) q, consOk X] (In (cdrc X) q) := PrfH.hyp _ _ (List.Mem.head _)
  have hcons : PrfH [In (cdrc X) q, consOk X] (consOk X) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  have hbr := PrfH.mp _ _ _ (prf_to_prfH (pcc_cdrcD_bridge_cons X) _) hcons
  have hbrS : PrfH _ (provFromCode (eqCodeFn (tcFn (cdrc X)) (cdrcT (tcFn X)))) :=
    PrfH_eq_symm_code _ _ (substtc_inv_cdrcT (substtc_inv_tcFn X)) hbr (by hw_auto) (by hw_auto)
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (cdrc X)) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (cdrc X) q) _) hin
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn q) hbrS hat

end ROBINSON_PlusPlus.Meta.TrackedAtomsPrf

/-! ## `export` — por PROPÓSITO DECLARADO

Los consumidores previstos son **C3** (`DEUDA_hGuardT`/`DEUDA_hGuardF`) y **D3**
(`DEUDA_chainOkBDot`), ninguno de los cuales existe todavía. Se exporta el kit entero porque
todo él es genérico: no hay aquí fontanería privada de ningún frente. -/
export ROBINSON_PlusPlus.Meta.TrackedAtomsPrf (
  shapeDot prf_substfc_inDot prf_substfc_shapeDot prf_substfc_shapeDot_at pcc_shape_tree
  prf_substtc_child
  prf_congr_forallc prf_congr_bdAllCode
  pcc_congr_nthcT_arg1_code PrfH_shapeDot_transport PrfH_orL_code PrfH_orR_code
  bdAllBndCtx prf_substfc_bdAllBndCtx PrfH_bdAllCode_congr_bnd
  prf_liftc_varc0 prf_liftc_funcc1 prf_liftc_funcc2
  prf_liftc_nthcT prf_liftc_lencT prf_liftc_carcT prf_liftc_cdrcT
  bdInB bdInPhic bdInDot substtc_inv_bdInB liftTerm_bdInDot pcc_boundedIn_tracked
  phiInBwd InBwd prf_substtc_varc0_at1 pcc_InBwd_computed pcc_In_atom_tracked
  PrfH_congr_cdrcT pcc_carcD_bridge_cons pcc_cdrcD_bridge_cons PrfH_in_transport
  pcc_shape_tracked pcc_child_tracked pcc_child_tracked_at
  pcc_carcIn_tracked pcc_cdrcIn_tracked
)

/-! ## FOOTPRINT -/

#print axioms ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_In_atom_tracked
#print axioms ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_boundedIn_tracked
#print axioms ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_shape_tracked
#print axioms ROBINSON_PlusPlus.Meta.TrackedAtomsPrf.pcc_child_tracked
