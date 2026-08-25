/-
✅ A3 CERRADA — `pcc_isFCB_tracked (w c) : Prf (isFCB w c ⇒ provFromCode (isFCBDot w c))`
   con `w` y `c` ABSTRACTOS. Footprint SANCIONADO, cero axiomas nuevos, cero `sorry`.

    lake env lean Probe/A3_directa.lean      (0 errores, 0 warnings)

    'A3Directa.pcc_isFCB_tracked' depends on axioms: [propext, Classical.choice, Quot.sound,
     ROBINSON_PlusPlus.Meta.Representability2Prf.prf_axiomsCodeT_eq]

Fichero AUTOCONTENIDO (sólo `import ROBINSON_PlusPlus.Meta`).

## Las tres decisiones que lo hicieron salir

1. **Imagen punteada (d): el `In` va como ÁTOMO** (`inFormCodeFn`, ya en producción), no como
   su despliegue `∃`-acotado (`bdInDot`). ⇒ el cuerpo `PsiF` NO tiene ningún binder, todo el
   descenso de `substfc` vive en NIVEL 0, y **`hPsiId` sale por instanciación pura** del
   descenso genérico (el RHS es `PsiF q` por `rfl`). El precio es UNA pieza nueva,
   `pcc_InBwd_computed` (gemelo de `pcc_ltBwd_computed`), que ya venía medida.

2. **UNA sola Leibniz interna para los 12 disyuntos.** En `hbody` NO se transporta caso a caso
   de la forma «reflexión pura» a la «computada»: se prueba `Prov(nodeOkDot q̇ Ẋ)` entero
   (con `Ẋ = tcFn (nthc q i)`) y se transporta con el contexto `nodeOkDot q̇ ⌜v₀⌝`, porque
   `substfc` cubre TODAS las ocurrencias del hueco a la vez. Coste: 1 `PrfH_leibniz_apply`.

3. **R‑A3‑1 CASO A CASO, no global.** `consOk X` (el nodo es un `cons`) se añade a los 11
   disyuntos que usan `carc`, y **NO al caso `X = nil`**. Ponerlo como conjunto global (como
   proponía la especificación previa) habría hecho imposible el nodo `nil` —
   `termsCodeM [] = nil` es un sub-código legítimo — y habría roto los testigos reales.
   §10 lo comprueba: instancia CERRADA `⊢ Prov(⌜isFCB(w_⊥, ⌜⊥⌝)⌝)`.

## ⚠️ PROCEDENCIA — este resultado sobrevivió a una refutación que mató a la mitad de sus rivales

Se atacó A3 con **4 estrategias independientes**, cada una verificada por un agente adversarial
que recompilaba por su cuenta. Resultado: **2 confirmadas, 2 REFUTADAS**.

| intento | `consOk` | veredicto |
|---|---|---|
| `directa` (**éste**) | **caso a caso**, `nil` desnudo | ✅ irrefutable en 5 frentes |
| `bottomup` | **caso a caso**, `nil` desnudo | ✅ confirmado |
| `fragmento` | **global** | ⛔ refutado |
| `reformula` | **global** | ⛔ refutado (y no lo declaró en su informe) |

Las dos refutaciones son **independientes y COMPILADAS** (`sondeos/A3ConsOkRefuta.lean`):
con `consOk` **global**, la teoría objeto **REFUTA** que `nil` sea nodo (`nil_ne_cons`,
`Meta/CodeDistinct.lean:67`), y `nil` es **obligatorio** en todo testigo real —
`termCodeM zero = cons 1 (cons ⌜"0"⌝ (cons nil nil))`, cuya casilla 2 es `nil`, y la cola de
toda lista de argumentos termina en `termsCodeM [] = nil`. ⇒ `∃w. isFCB w c` se quedaría **sin
testigos** para toda fórmula que mencione un símbolo con argumentos, o sea para todas salvo `⊥`
y sus combinaciones booleanas. El teorema seguiría siendo verdadero **y vacío**.

**La moraleja, para el libro:** reforzar el antecedente objeto es la dirección que ABARATA el
teorema, y por eso es donde hay que mirar. Aquí se detectó porque alguien lo compiló, no porque
alguien lo leyera.

## ⚠️ DOS DESVIACIONES respecto a `sondeos/ParseWitness.lean`, ambas declaradas

1. **`consOk` en 11 de los 12 disyuntos** (arriba). Hace falta porque `pcc_eval_carc` sólo evalúa
   sobre `cons` EXPLÍCITO, y aquí el nodo es abstracto.
   * **Solidez**: `consOk` **restringe** `nodeOk` ⇒ `Prov` nunca crece. Sin problema.
   * **Completitud**: para un testigo real cada nodo de los 11 casos **es** un `cons`, luego
     `consOk` se descarga solo. ⚠️ **Pero añade una obligación al hito (i)**: la construcción de
     `subCodes` tendrá que probar `consOk` por nodo. Trivial, pero no estaba en el plan.
2. **La COTA sale en forma de reflexión pura** `tcFn (lenc w)`, no evaluada `lencT (tcFn w)`.
   Son iguales **dentro de `Prov`** (`pcc_eval_lenc`), pero convertirlas cuesta **un lema entero**
   (una segunda travesía estructural de `PsiF` a nivel 1, del tamaño de `hPsiId`). Se difiere a
   quien lo necesite.
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

namespace A3Directa

/-! ## 0 · Combinadores lógicos que se usan a lo largo del fichero -/

theorem impT {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH h2 _) (PrfH.mp _ _ _ (prf_to_prfH h1 _) (prfH_hyp_self _))

/-- `∨`-elim en forma de implicación (`Prf₀.j3`). -/
theorem prf_or_elim_imp {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) :
    Prf (lor A B ⇒ C) := by
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _
    (PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.j3 A B C)) (prfH_hyp_self _))
    (prf_to_prfH h1 _)) (prf_to_prfH h2 _)

/-- `∨`-intro izquierdo INTERNO, en forma de implicación. -/
theorem prf_orL_imp (Ac Bc : Term) : Prf (provFromCode Ac ⇒ provFromCode (orc Ac Bc)) :=
  prf_mp (pcc_mp_code_open Ac (orc Ac Bc)) (pcc_j1_code Ac Bc)

/-- `∨`-intro derecho INTERNO, en forma de implicación. -/
theorem prf_orR_imp (Ac Bc : Term) : Prf (provFromCode Bc ⇒ provFromCode (orc Ac Bc)) :=
  prf_mp (pcc_mp_code_open Bc (orc Ac Bc)) (pcc_j2_code Ac Bc)

/-! ## 1 · EL OBJETO (copia de `sondeos/ParseWitness.lean` + enmienda R‑A3‑1)

    ⚠️ **R‑A3‑1**: `nodeOk` pide `carc X = k̄` para `X` ABSTRACTO, y su dotado necesita
    `Prov(⌜carcT Ẋ = (carc X)˙⌝)`. Los tres puentes que existen exigen saber que `X` es un
    `cons` (`pcc_eval_carc`), o `lineWF`, o `chainOk`. Añadimos por eso `consOk X` **CASO A
    CASO** — y NO en el caso `X = nil`, que no usa `carc` y donde `consOk nil` podría ser
    falso (rompería los testigos reales: `termsCodeM [] = nil` es un nodo legítimo).
    `consOk` es OBJETO puro y **no aparece en la imagen punteada**: `isFCB` sólo se
    RESTRINGE ⇒ `Prov` nunca crece. -/

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

/-- El nodo es un `cons` (enmienda R‑A3‑1). -/
def consOk (X : Term) : Formula := Formula.eq X (cons (carc X) (cdrc X))

/-- Envoltorio: «además de `F`, el nodo es un `cons`». -/
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

/-! ## 2 · LA IMAGEN PUNTEADA — formulación (d): el `In` va como ÁTOMO (`inFormCodeFn`),
    NO como su despliegue `∃`-acotado. Así el cuerpo del `∀` acotado **no tiene ningún
    binder** y todo el descenso de `substfc` vive en NIVEL 0. -/

noncomputable def shapeDot (X : Term) (k n : Nat) : Term :=
  andc (eqCodeFn (carcT X) (tcFn (numeralM k))) (eqCodeFn (lencT X) (tcFn (numeralM n)))

noncomputable def unDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 2) (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)

noncomputable def binDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3)
    (andc (inFormCodeFn (nthcT X (tcFn (numeralM 1))) W)
          (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W))

noncomputable def strBinDot (W X : Term) (k : Nat) : Term :=
  andc (shapeDot X k 3) (inFormCodeFn (nthcT X (tcFn (numeralM 2))) W)

noncomputable def varDot (X : Term) : Term := shapeDot X 0 2

def lorAllc : Term → List Term → Term
  | a, []      => a
  | a, b :: bs => orc a (lorAllc b bs)

/-- El nodo DOTADO, 12 casos en el mismo orden que `nodeOk`. -/
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

/-- **`PsiF`**: el cuerpo dotado del `∀` acotado, con el hueco `⌜v₀⌝` en el ÍNDICE. -/
noncomputable def PsiF (w : Term) : Term :=
  nodeOkDot (tcFn w) (nthcT (tcFn w) (varc (numeral 0)))

/-- **Imagen punteada de `wfAll`** (lo que `pcc_bdAll_intro` entrega, literalmente). -/
noncomputable def wfAllDot (w : Term) : Term := bdAllCode (tcFn (lenc w)) (PsiF w)

/-- **Imagen punteada de `isFCB`**. -/
noncomputable def isFCBDot (w c : Term) : Term :=
  andc (wfAllDot w) (inFormCodeFn (tcFn c) (tcFn w))

/-! ## 3 · EL DESCENSO GENÉRICO de `substfc zero s` por los 12 disyuntos (todo NIVEL 0) -/

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
  unfold nodeOkDot lorAllc varDot
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

/-- El descenso instanciado en el cuerpo real. -/
theorem prf_substfc_PsiF (w s : Term) :
    Prf (substfc zero s (PsiF w) =eq nodeOkDot (tcFn w) (nthcT (tcFn w) s)) :=
  prf_substfc_nodeOkDot_gen s (tcFn w) _ _ (substtc_inv_tcFn w)
    (prf_eq_trans (prf_substtc_nthcT zero s (tcFn w) (varc (numeral 0)))
      (prf_congr_nthcT (substtc_inv_tcFn w s) (prf_substtc_varc0 s)))

/-! ## 4 · El reflector del ÁTOMO `In` (A1 + el puente `bdInDot ⇒ ⌜In⌝` dentro de `Prov`) -/

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

def phiInBwd : Formula := Formula.impl (boundedIn (.var 1) (.var 0)) (In (.var 1) (.var 0))

theorem InBwd : Prf (forall_2 phiInBwd) :=
  Prf.gen _ (Prf.gen _ (prf_In_of_boundedIn (.var 1) (.var 0)))

theorem substtc_inv_tcFn_at1 (w : Term) : ∀ V, Prf (substtc (succ zero) V (tcFn w) =eq tcFn w) :=
  fun V => prf_substtc_tcFn_at 1 V w

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
    pcc_thm_inst2 phiInBwd InBwd A B
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

/-! ## 5 · Los PUENTES `carcT`/`cdrcT` desgatillados (R‑A3‑1) y el transporte en `In` -/

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
    (h : PrfH Γ (provFromCode (inFormCodeFn u W))) :
    PrfH Γ (provFromCode (inFormCodeFn v W)) := by
  let Cin : Term := inFormCodeFn (varc (numeral 0)) W
  have hcomp : ∀ t : Term, Prf (substfc zero t Cin =eq inFormCodeFn t W) := fun t =>
    prf_substfc_inDot t (varc (numeral 0)) t W (prf_substtc_varc0 t) hW
  have h1 : PrfH Γ (provFromCode (substfc zero u Cin)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hcomp u))) _) h
  have h2 : PrfH Γ (provFromCode (substfc zero v Cin)) := PrfH_leibniz_apply Cin u v heq h1
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp v)) _) h2

/-! ## 6 · LOS 12 CASOS (reflexión de cada disyunto sobre el nodo `X` ABSTRACTO) -/

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
  have hlen : PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (lenc X)))) :=
    prf_to_prfH (pcc_eval_lenc X) Γ
  have hlen2 : PrfH Γ (provFromCode (eqCodeFn (tcFn (lenc X)) (tcFn (numeralM n)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eq_tracked (lenc X) (numeralM n)) _)
      (PrfH_and_elim_right hsh)
  have hB : PrfH Γ (provFromCode (eqCodeFn (lencT (tcFn X)) (tcFn (numeralM n)))) :=
    PrfH_eq_trans_code _ _ _ (substtc_inv_lencT (substtc_inv_tcFn X)) hlen hlen2
  exact PrfH_and_intro_code _ _ hA hB

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
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (PrfH_eq_symm hlen)
      (prf_to_prfH (prf_lt_numeralM hjn) _)
  have hev : PrfH _ (provFromCode (eqCodeFn (nthcT (tcFn X) (tcFn (numeralM j)))
      (tcFn (nthc X (numeralM j))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc X (numeralM j)) _) hlt
  have hevS : PrfH _ (provFromCode (eqCodeFn (tcFn (nthc X (numeralM j)))
      (nthcT (tcFn X) (tcFn (numeralM j))))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn X) (substtc_inv_tcFn (numeralM j))) hev
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
    PrfH_eq_symm_code _ _ (substtc_inv_carcT (substtc_inv_tcFn X)) hbr
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
    PrfH_eq_symm_code _ _ (substtc_inv_cdrcT (substtc_inv_tcFn X)) hbr
  have hat : PrfH _ (provFromCode (inFormCodeFn (tcFn (cdrc X)) (tcFn q))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked (cdrc X) q) _) hin
  exact PrfH_in_transport _ _ _ (substtc_inv_tcFn q) hbrS hat

/-! ### Los cinco moldes de disyunto -/

theorem pcc_nulOk_case (X : Term) (k : Nat) :
    Prf (cOk X (nulOk X k) ⇒ provFromCode (shapeDot (tcFn X) k 1)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (nulOk X k))
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 1) _)
    (PrfH_and_elim_left h)) (PrfH_and_elim_right h)

theorem pcc_varOk_case (X : Term) :
    Prf (cOk X (varOk X) ⇒ provFromCode (varDot (tcFn X))) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (varOk X))
  exact PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X 0 2) _)
    (PrfH_and_elim_left h)) (PrfH_and_elim_right h)

theorem pcc_unOk_case (q X : Term) (k : Nat) :
    Prf (cOk X (unOk q X k) ⇒ provFromCode (unDot (tcFn q) (tcFn X) k)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (unOk q X k))
  have hcons := PrfH_and_elim_left h
  have hun := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hun
  have hmem := PrfH_and_elim_right hun
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 2) _) hcons) hsh
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked q X 1 2 (by omega)) _) (PrfH_and_elim_right hsh)) hmem
  exact PrfH_and_intro_code _ _ h1 h2

theorem pcc_binOk_case (q X : Term) (k : Nat) :
    Prf (cOk X (binOk q X k) ⇒ provFromCode (binDot (tcFn q) (tcFn X) k)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (binOk q X k))
  have hcons := PrfH_and_elim_left h
  have hbin := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hbin
  have hmem := PrfH_and_elim_right hbin
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 3) _) hcons) hsh
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked q X 1 3 (by omega)) _) (PrfH_and_elim_right hsh))
    (PrfH_and_elim_left hmem)
  have h3 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked q X 2 3 (by omega)) _) (PrfH_and_elim_right hsh))
    (PrfH_and_elim_right hmem)
  exact PrfH_and_intro_code _ _ h1 (PrfH_and_intro_code _ _ h2 h3)

theorem pcc_strBinOk_case (q X : Term) (k : Nat) :
    Prf (cOk X (strBinOk q X k) ⇒ provFromCode (strBinDot (tcFn q) (tcFn X) k)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (strBinOk q X k))
  have hcons := PrfH_and_elim_left h
  have hsb := PrfH_and_elim_right h
  have hsh := PrfH_and_elim_left hsb
  have hmem := PrfH_and_elim_right hsb
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_shape_tracked X k 3) _) hcons) hsh
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _
    (prf_to_prfH (pcc_child_tracked q X 2 3 (by omega)) _) (PrfH_and_elim_right hsh)) hmem
  exact PrfH_and_intro_code _ _ h1 h2

theorem pcc_nilCase (X : Term) :
    Prf (Formula.eq X nil ⇒ provFromCode (eqCodeFn (tcFn X) (tcFn nil))) :=
  pcc_eq_tracked X nil

theorem pcc_consCase (q X : Term) :
    Prf (cOk X (land (In (carc X) q) (In (cdrc X) q)) ⇒
      provFromCode (andc (inFormCodeFn (carcT (tcFn X)) (tcFn q))
                         (inFormCodeFn (cdrcT (tcFn X)) (tcFn q)))) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (cOk X (land (In (carc X) q) (In (cdrc X) q)))
  have hcons := PrfH_and_elim_left h
  have hmem := PrfH_and_elim_right h
  have h1 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_carcIn_tracked q X) _) hcons)
    (PrfH_and_elim_left hmem)
  have h2 := PrfH.mp _ _ _ (PrfH.mp _ _ _ (prf_to_prfH (pcc_cdrcIn_tracked q X) _) hcons)
    (PrfH_and_elim_right hmem)
  exact PrfH_and_intro_code _ _ h1 h2

/-! ## 7 · EL ENSAMBLAJE de los 12 disyuntos: `nodeOk q X ⇒ Prov(nodeOkDot ẇ Ẋ)` -/

theorem pcc_nodeOk_pure (q X : Term) :
    Prf (nodeOk q X ⇒ provFromCode (nodeOkDot (tcFn q) (tcFn X))) := by
  have s11 : Prf (cOk X (land (In (carc X) q) (In (cdrc X) q)) ⇒
      provFromCode (andc (inFormCodeFn (carcT (tcFn X)) (tcFn q))
                         (inFormCodeFn (cdrcT (tcFn X)) (tcFn q)))) := pcc_consCase q X
  have s10 : Prf (lor (Formula.eq X nil)
      (cOk X (land (In (carc X) q) (In (cdrc X) q))) ⇒
      provFromCode (orc (eqCodeFn (tcFn X) (tcFn nil))
        (andc (inFormCodeFn (carcT (tcFn X)) (tcFn q))
              (inFormCodeFn (cdrcT (tcFn X)) (tcFn q))))) :=
    prf_or_elim_imp (impT (pcc_nilCase X) (prf_orL_imp _ _)) (impT s11 (prf_orR_imp _ _))
  have s9 := prf_or_elim_imp
    (impT (pcc_strBinOk_case q X 1) (prf_orL_imp (strBinDot (tcFn q) (tcFn X) 1) _))
    (impT s10 (prf_orR_imp (strBinDot (tcFn q) (tcFn X) 1) _))
  have s8 := prf_or_elim_imp
    (impT (pcc_varOk_case X) (prf_orL_imp (varDot (tcFn X)) _))
    (impT s9 (prf_orR_imp (varDot (tcFn X)) _))
  have s7 := prf_or_elim_imp
    (impT (pcc_unOk_case q X 9) (prf_orL_imp (unDot (tcFn q) (tcFn X) 9) _))
    (impT s8 (prf_orR_imp (unDot (tcFn q) (tcFn X) 9) _))
  have s6 := prf_or_elim_imp
    (impT (pcc_binOk_case q X 8) (prf_orL_imp (binDot (tcFn q) (tcFn X) 8) _))
    (impT s7 (prf_orR_imp (binDot (tcFn q) (tcFn X) 8) _))
  have s5 := prf_or_elim_imp
    (impT (pcc_binOk_case q X 7) (prf_orL_imp (binDot (tcFn q) (tcFn X) 7) _))
    (impT s6 (prf_orR_imp (binDot (tcFn q) (tcFn X) 7) _))
  have s4 := prf_or_elim_imp
    (impT (pcc_unOk_case q X 6) (prf_orL_imp (unDot (tcFn q) (tcFn X) 6) _))
    (impT s5 (prf_orR_imp (unDot (tcFn q) (tcFn X) 6) _))
  have s3 := prf_or_elim_imp
    (impT (pcc_binOk_case q X 5) (prf_orL_imp (binDot (tcFn q) (tcFn X) 5) _))
    (impT s4 (prf_orR_imp (binDot (tcFn q) (tcFn X) 5) _))
  have s2 := prf_or_elim_imp
    (impT (pcc_binOk_case q X 4) (prf_orL_imp (binDot (tcFn q) (tcFn X) 4) _))
    (impT s3 (prf_orR_imp (binDot (tcFn q) (tcFn X) 4) _))
  have s1 := prf_or_elim_imp
    (impT (pcc_strBinOk_case q X 3) (prf_orL_imp (strBinDot (tcFn q) (tcFn X) 3) _))
    (impT s2 (prf_orR_imp (strBinDot (tcFn q) (tcFn X) 3) _))
  have s0 := prf_or_elim_imp
    (impT (pcc_nulOk_case X 2) (prf_orL_imp (shapeDot (tcFn X) 2 1) _))
    (impT s1 (prf_orR_imp (shapeDot (tcFn X) 2 1) _))
  exact s0

/-! ## 8 · Las 8 obligaciones de `pcc_bdAll_intro` -/

theorem hbl_ok : ∀ (k : Nat) (q : Term), liftTerm k (lenc q) = lenc (liftTerm k q) := by
  intro k q; simp only [lenc, liftTerm, liftTerms]

theorem hbs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (lenc q) = lenc (substTerm v t q) := by
  intro v t q; simp only [lenc, substTerm, substTerms]

theorem hPl_ok : ∀ (k : Nat) (q : Term), liftTerm k (PsiF q) = PsiF (liftTerm k q) := by
  intro k q
  simp only [PsiF, nodeOkDot, lorAllc, shapeDot, unDot, binDot, strBinDot, varDot,
    inFormCodeFn, eqCodeFn, andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, liftTerm, liftTerms, liftTerm_numeral,
    liftTerm_strCode]

theorem hPs_ok : ∀ (v : Nat) (t q : Term), substTerm v t (PsiF q) = PsiF (substTerm v t q) := by
  intro v t q
  simp only [PsiF, nodeOkDot, lorAllc, shapeDot, unDot, binDot, strBinDot, varDot,
    inFormCodeFn, eqCodeFn, andc, orc, carcT, cdrcT, lencT, nthcT, funcc, varc,
    tcFn, cons, nil, zero, succ, numeralM, substTerm, substTerms, substTerm_numeral,
    substTerm_strCode]

theorem hCl_ok : ∀ (k : Nat) (q : Term), liftFormula k (wfAll q) = wfAll (liftTerm k q) := by
  intro k q
  simp only [wfAll, nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk,
    land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero, liftFormula, liftTerm, liftTerms,
    liftTerm_numeralM, if_pos (Nat.zero_lt_succ k), ← FOL.liftTerm_comm_zero]

theorem hCs_ok : ∀ (v : Nat) (t q : Term),
    substFormula v t (wfAll q) = wfAll (substTerm v t q) := by
  intro v t q
  have h1 : ¬ ((0 : Nat) = v + 1) := by omega
  have h2 : ¬ ((0 : Nat) > v + 1) := by omega
  simp only [wfAll, nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk,
    land, lor, In, lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
    substTerm_numeralM, FOL.substTerm_lift_comm_zero, if_neg h1, if_neg h2]

/-- **`hPsiId`**: sustituir el hueco `⌜v₀⌝` por sí mismo es la identidad — sale por
    instanciación pura del descenso, porque el RHS es DEFINICIONALMENTE `PsiF q`. -/
theorem hPsiId_ok : ∀ q : Term,
    Prf (substfc zero (varc (numeral 0)) (PsiF q) =eq PsiF q) :=
  fun q => prf_substfc_PsiF q (varc (numeral 0))

/-! ### `hbody`: el trabajo grande -/

theorem hbody_ok : ∀ q i : Term, Prf (wfAll q ⇒ (lt i (lenc q)
    ⇒ provFromCode (substfc zero (tcFn i) (PsiF q)))) := by
  intro q i
  refine prf_deduction (deduction_aux ?_ (lt i (lenc q)) [wfAll q] rfl)
  have hlt : PrfH [lt i (lenc q), wfAll q] (lt i (lenc q)) := PrfH.hyp _ _ (List.Mem.head _)
  have hwf : PrfH [lt i (lenc q), wfAll q] (wfAll q) :=
    PrfH.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
  -- (1) especialización objeto: de `wfAll q` e `i < lenc q` sale `nodeOk q (nthc q i)`
  have hsubst : substFormula 0 i (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (nodeOk (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0))))
      = Formula.impl (lt i (lenc q)) (nodeOk q (nthc q i)) := by
    simp only [nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      lt, carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      substTerm_numeralM, FOL.substTerm_liftTerm, if_true]
  have h0 := PrfH.mp _ _ _ (PrfH.incl0 [lt i (lenc q), wfAll q] _
    (Prf₀.q1 (Formula.impl (lt (.var 0) (liftTerm 0 (lenc q)))
      (nodeOk (liftTerm 0 q) (nthc (liftTerm 0 q) (.var 0)))) i)) hwf
  rw [hsubst] at h0
  have hnode : PrfH [lt i (lenc q), wfAll q] (nodeOk q (nthc q i)) := PrfH.mp _ _ _ h0 hlt
  -- (2) reflexión PURA del nodo (el hueco es `Ẋ = tcFn (nthc q i)`)
  have hpure : PrfH [lt i (lenc q), wfAll q]
      (provFromCode (nodeOkDot (tcFn q) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_nodeOk_pure q (nthc q i)) _) hnode
  -- (3) evaluación provable del índice: `nthcT(q̇, ı̇) = (nthc q i)˙`, y su simétrica
  have hev : PrfH [lt i (lenc q), wfAll q]
      (provFromCode (eqCodeFn (nthcT (tcFn q) (tcFn i)) (tcFn (nthc q i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (pcc_eval_nthc q i) _) hlt
  have hevS : PrfH [lt i (lenc q), wfAll q]
      (provFromCode (eqCodeFn (tcFn (nthc q i)) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH_eq_symm_code _ _
      (substtc_inv_nthcT (substtc_inv_tcFn q) (substtc_inv_tcFn i)) hev
  -- (4) UNA Leibniz interna con el contexto `nodeOkDot q̇ ⌜v₀⌝` cubre los 12 disyuntos
  have hC : ∀ t : Term,
      Prf (substfc zero t (nodeOkDot (tcFn q) (varc (numeral 0))) =eq nodeOkDot (tcFn q) t) :=
    fun t => prf_substfc_nodeOkDot_gen t (tcFn q) (varc (numeral 0)) t
      (substtc_inv_tcFn q) (prf_substtc_varc0 t)
  have h1 : PrfH [lt i (lenc q), wfAll q]
      (provFromCode (substfc zero (tcFn (nthc q i)) (nodeOkDot (tcFn q) (varc (numeral 0))))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (prf_eq_symm (hC _))) _) hpure
  have h2 : PrfH [lt i (lenc q), wfAll q]
      (provFromCode (substfc zero (nthcT (tcFn q) (tcFn i))
        (nodeOkDot (tcFn q) (varc (numeral 0))))) :=
    PrfH_leibniz_apply _ _ _ hevS h1
  have h3 : PrfH [lt i (lenc q), wfAll q]
      (provFromCode (nodeOkDot (tcFn q) (nthcT (tcFn q) (tcFn i)))) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hC _)) _) h2
  exact PrfH.mp _ _ _
    (prf_to_prfH (prf_provCode_congr (prf_eq_symm (prf_substfc_PsiF q (tcFn i)))) _) h3

/-! ## 9 · A3 -/

theorem pcc_wfAll_tracked (w : Term) : Prf (wfAll w ⇒ provFromCode (wfAllDot w)) :=
  pcc_bdAll_intro wfAll lenc PsiF w hCl_ok hCs_ok hbl_ok hbs_ok hPl_ok hPs_ok hPsiId_ok hbody_ok

/-- **A3**: `isFCB w c ⇒ Prov(⌜isFCBDot w c⌝)`, con `w` y `c` **ABSTRACTOS**. -/
theorem pcc_isFCB_tracked (w c : Term) : Prf (isFCB w c ⇒ provFromCode (isFCBDot w c)) := by
  refine prf_deduction ?_
  have h := prfH_hyp_self (isFCB w c)
  exact PrfH_and_intro_code _ _
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_wfAll_tracked w) _) (PrfH_and_elim_left h))
    (PrfH.mp _ _ _ (prf_to_prfH (pcc_In_atom_tracked c w) _) (PrfH_and_elim_right h))

/-! ## 10 · NO VACUIDAD — la enmienda R‑A3‑1 se descarga sola en testigos reales

    Se comprueba extremo a extremo sobre `⊥`: el testigo es `objList [⌜⊥⌝]`, cada nodo es
    un `cons` LITERAL, y `consOk` sale de `prf_carc_cons`/`prf_cdrc_cons`. Además el caso
    `X = nil` (la lista vacía de argumentos) NO lleva `consOk`, así que sigue disponible. -/

/-- `cdrc (cons h t) = t` en `Prf` (el gemelo de `prf_carc_cons`, que no estaba). -/
theorem prf_cdrc_cons (h t : Term) : Prf (cdrc (cons h t) =eq t) := by
  have hax : Prf ax_cdrc := prf_ax (by simp [axioms])
  have hh := prf_spec (prf_spec hax h) t
  simp [substFormula, substTerm, substTerms, cdrc, cons, FOL.substTerm_liftTerm] at hh
  exact hh

/-- La enmienda es TRIVIAL para nodos que son `cons` literales — que es lo que construyen
    `objList`/`subCodes`. -/
theorem prf_consOk_cons (h t : Term) : Prf (consOk (cons h t)) :=
  prf_eq_trans (prf_congr_cons_head (prf_eq_symm (prf_carc_cons h t)))
    (prf_congr_cons_tail (prf_eq_symm (prf_cdrc_cons h t)))

def wBot : Term := objList [formCodeM Formula.bottom]

theorem prf_nodeOk_bot (w : Term) : Prf (nodeOk w (formCodeM Formula.bottom)) := by
  have htag : Prf (Formula.eq (carc (formCodeM Formula.bottom)) (numeralM 2)) :=
    prf_carc_cons (numeralM 2) nil
  have hlen : Prf (Formula.eq (lenc (formCodeM Formula.bottom)) (numeralM 1)) :=
    prf_eq_trans (prf_lenc_cons (numeralM 2) nil) (prf_eq_congr_succ prf_lenc_nil)
  have hnul : Prf (cOk (formCodeM Formula.bottom) (nulOk (formCodeM Formula.bottom) 2)) :=
    prf_and_intro (prf_consOk_cons (numeralM 2) nil) (prf_and_intro htag hlen)
  unfold nodeOk lorAll
  exact prf_mp (Prf.incl (Prf₀.j1 _ _)) hnul

theorem prf_lenc_objList : ∀ L : List Term,
    Prf (Formula.eq (lenc (objList L)) (numeralM L.length))
  | []      => prf_lenc_nil
  | e :: es =>
      prf_eq_trans (prf_lenc_cons e (objList es)) (prf_eq_congr_succ (prf_lenc_objList es))

theorem prf_In_objList : ∀ (L : List Term) (x : Term), List.Mem x L → Prf (In x (objList L))
  | [],      x, h => by cases h
  | e :: es, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact prf_in_cons_head x (objList es)
      · exact prf_in_cons_tail e (prf_In_objList es x h')

theorem PrfH_congr_nthc_idx {Γ : List Formula} {w i₁ i₂ : Term} (h : PrfH Γ (i₁ =eq i₂)) :
    PrfH Γ (nthc w i₁ =eq nthc w i₂) := by
  let f : Formula :=
    Formula.eq (nthc (liftTerm 0 w) (liftTerm 0 i₁)) (nthc (liftTerm 0 w) (.var 0))
  have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (nthc w i₁) (nthc w s) := by
    intro s
    simp only [f, nthc, substFormula, substTerm, substTerms, FOL.substTerm_liftTerm, if_true]
  exact (hS i₂) ▸ PrfH_leibniz_subst (A := f) h ((hS i₁) ▸ prf_to_prfH (prf_refl (nthc w i₁)) Γ)

/-- Leibniz sobre el nodo: UNA sola aplicación, no 12. -/
theorem PrfH_congr_nodeOk {Γ : List Formula} {w X₁ X₂ : Term} (h : PrfH Γ (X₁ =eq X₂))
    (hN : PrfH Γ (nodeOk w X₁)) : PrfH Γ (nodeOk w X₂) := by
  let f : Formula := nodeOk (liftTerm 0 w) (.var 0)
  have hS : ∀ s : Term, substFormula 0 s f = nodeOk w s := by
    intro s
    simp only [f, nodeOk, cOk, consOk, lorAll, nulOk, unOk, binOk, strBinOk, varOk, land, lor, In,
      carc, cdrc, lenc, nthc, cons, nil, zero, substFormula, substTerm, substTerms,
      FOL.substTerm_liftTerm, substTerm_numeralM, if_true]
  exact (hS X₂) ▸ PrfH_leibniz_subst (A := f) h ((hS X₁) ▸ hN)

theorem prf_isFCB_bottom : Prf (isFCB wBot (formCodeM Formula.bottom)) := by
  refine prf_and_intro ?_ (prf_In_objList _ _ (List.Mem.head _))
  refine Prf.gen _ (prf_deduction ?_)
  have hlift : liftTerm 0 wBot = wBot := by
    simp only [wBot, objList, formCodeM, cons, nil, zero, numeralM, succ, liftTerm, liftTerms]
  rw [hlift]
  have hlen : Prf (Formula.eq (lenc wBot) (numeralM 1)) := prf_lenc_objList _
  have hlt1 : PrfH [lt (.var 0) (lenc wBot)] (lt (.var 0) (succ zero)) :=
    ROBINSON_PlusPlus.Meta.BoundedInPrf.PrfH_lt_subst2 (prf_to_prfH hlen _)
      (PrfH.hyp _ _ (List.Mem.head _))
  have hsplit : PrfH [lt (.var 0) (lenc wBot)]
      (lor (lt (.var 0) zero) (Formula.eq (.var 0) zero)) :=
    PrfH.mp _ _ _ (prf_to_prfH (prf_lt_succ_split (.var 0) zero) _) hlt1
  refine PrfH_or_elim hsplit ?brA ?brB
  case brA =>
    exact PrfH.mp _ _ _ (PrfH.incl0 _ _ (Prf₀.efq _))
      (PrfH.mp _ _ _ (prf_to_prfH (prf_not_lt_zero (.var 0)) _) (PrfH.hyp _ _ (List.Mem.head _)))
  case brB =>
    have hi : PrfH (Formula.eq (.var 0) zero :: [lt (.var 0) (lenc wBot)])
        (Formula.eq (.var 0) zero) := PrfH.hyp _ _ (List.Mem.head _)
    have hX : PrfH (Formula.eq (.var 0) zero :: [lt (.var 0) (lenc wBot)])
        (Formula.eq (nthc wBot (.var 0)) (formCodeM Formula.bottom)) :=
      PrfH_eq_trans (PrfH_congr_nthc_idx (w := wBot) hi)
        (prf_to_prfH (prf_nthc_zero (formCodeM Formula.bottom) nil) _)
    exact PrfH_congr_nodeOk (PrfH_eq_symm hX) (prf_to_prfH (prf_nodeOk_bot wBot) _)

/-- **INSTANCIA CERRADA, extremo a extremo**: `⊢ Prov(⌜ isFCB(w_⊥, ⌜⊥⌝) ⌝)`.
    Certifica que A3 **no es vacía** y que la enmienda R‑A3‑1 no mata los testigos reales. -/
theorem pcc_isFCB_bottom : Prf (provFromCode (isFCBDot wBot (formCodeM Formula.bottom))) :=
  prf_mp (pcc_isFCB_tracked wBot (formCodeM Formula.bottom)) prf_isFCB_bottom

end A3Directa

set_option pp.explicit false in
#check @A3Directa.pcc_isFCB_tracked
#check @A3Directa.pcc_wfAll_tracked
#check @A3Directa.pcc_isFCB_bottom

#print axioms A3Directa.pcc_isFCB_tracked
#print axioms A3Directa.pcc_wfAll_tracked
#print axioms A3Directa.hbody_ok
#print axioms A3Directa.pcc_nodeOk_pure
#print axioms A3Directa.pcc_In_atom_tracked
#print axioms A3Directa.hPsiId_ok
#print axioms A3Directa.prf_isFCB_bottom
#print axioms A3Directa.pcc_isFCB_bottom
