/-
Probe/T2_higiene.lean — AUDITORIA DE HIGIENE de `ROBINSON_PlusPlus/Meta/CodeWitnessPrf.lean`.

Medido contra el fichero de produccion en su estado de 2026-09-03, 2306 lineas
(md5 6201514e00ccde0bc35d01db14c326df), es decir DESPUES de que entrase
`Meta/EvalLiftcPrf.lean` y de que `prf_argsIn_head`/`prf_argsIn_tail` bajasen a `SinWTs`.

Este fichero NO toca produccion. Solo mide. Tres frentes:

  §1  El bloque `export` que le falta al modulo, PEGADO AQUI TAL CUAL y ejercitado con
      los 202 nombres SIN cualificar. Incluye el control de que HOY, sin el bloque,
      esos nombres NO resuelven; y la regresion sobre los `open` de los dos
      consumidores de produccion (`LiftcCodePrf`, `EvalLiftcPrf`).
  §2  Los SIETE lemas duplicados entre `SinWTs` y `ENS`: puente `rfl` compilado para
      cada uno, mas bateria de controles negativos (uno de ellos con los DOS lados del
      MISMO tipo, para que el `rfl` no sea degenerado por irrelevancia de pruebas).
  §3  Los docstrings falsos, verificados con censo de `env.constants` (no grep) y con
      `#print axioms`.

NOTA sobre que prueba un `rfl` entre dos TEOREMAS: `Prf X` es un `Prop`, luego por
irrelevancia de pruebas dos teoremas con el MISMO enunciado son defeq automaticamente.
Por eso el `rfl` de §2 mide exactamente lo que interesa —que los ENUNCIADOS son
identicos— y NO que las demostraciones lo sean. El control negativo §2.9, entre dos
`def` (no Props) del MISMO tipo, es el que acredita que la tecnica discrimina.
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Provability

/-! ############################################################################
    # §1 · EL BLOQUE `export` QUE LE FALTA AL MODULO
    ############################################################################ -/

/-! ## §1.0 · CONTROL «ANTES»: hoy, sin bloque `export`, el nombre a secas NO existe.

    Esto se elabora ANTES de los tres `export` de §1.1, o sea en el estado REAL de
    produccion. Los tres nombres son de los tres namespaces distintos. -/

example : True := by
  fail_if_success (have _h := @liftF_isTC1)      -- ENS  · el que reporta el encargo
  fail_if_success (have _h := @prf_hasWitF_real) -- HW   · la no-vacuidad
  fail_if_success (have _h := @prf_argsIn_head)  -- SinWTs · bajado hoy desde EvalLiftcPrf
  trivial

/-! Y no es que no existan: existen, CUALIFICADOS. El fallo es de proyeccion a raiz. -/
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_isTC1
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.HW.prf_hasWitF_real
#check @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_head

/-! ## §1.1 · EL BLOQUE, LISTO PARA PEGAR AL FINAL DE `Meta/CodeWitnessPrf.lean`
       (despues de `end ROBINSON_PlusPlus.Meta.CodeWitnessPrf`, AI-GUIDE §17.1).

    Tres bloques, uno por namespace (AI-GUIDE §17.5), alfabeticos (§17.4).
    202 nombres de los 212 declarados. Las DIEZ exclusiones, y por que:

    * `SinWTs.prf_congr_liftc` y `SinWTs.PrfH_congr_liftc` — COLISION REAL. Ya hay alias
      en raiz para esos dos nombres, puestos por `Meta/NumCodeClosedPrf.lean`. Ademas son
      REDUNDANTES: se derivan de los de produccion (medido en §4.2). Se quedan
      cualificados; lo que procede es borrarlos, no exportarlos.
    * `SinWTs.mem_of_getElem?` — homonimo de `List.mem_of_getElem?` del core (y de los de
      `Array`/`Vector`). Hoy no colisiona porque `List` no esta abierto en ningun modulo
      del proyecto, pero poner ese nombre en la RAIZ es una mina. Ademas es una
      re-demostracion de un lema del core (medido en §4.1). No se exporta.
    * Los SIETE de `ENS` duplicados de `SinWTs` (§2): a raiz sale el de `SinWTs`, que es
      el que ya consumen `LiftcCodePrf` (open selectivo, :90) y `EvalLiftcPrf` (:336).
      El de `ENS` no sale, porque se va a BORRAR.

    No hay ninguna declaracion `private` ni `_aux` en el modulo: la regla §17.3 no muerde. -/

-- Export: API publica del reconocedor de codigo de TERMINO con UNA lista testigo.
export ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs (
  argsIn argsInBody binOkF closed_mem_tcodes1 closed_mem_tcodes1s closed_termCodeM
  CodeClosed cOk consOk crit_argsIn_lenc_zero crit_closed_implc crit_cOk2_absurd
  crit_cOk3_absurd crit_isFormCodeB2_rejects crit_isFormCodeB2_rejects_funcc
  crit_isFormCodeB2_rejects_varc crit_isTC1_junk_refuted_open crit_isTermCodeB1_rejects
  crit_isTermCodeB1_rejects_andc crit_isTermCodeB1_rejects_atomc
  crit_isTermCodeB1_rejects_botc crit_isTermCodeB1_rejects_eqc
  crit_isTermCodeB1_rejects_exc crit_isTermCodeB1_rejects_forallc
  crit_isTermCodeB1_rejects_implc crit_isTermCodeB1_rejects_orc
  crit_isTermCodeE1_funcc_lenc_zero crit_isTermCodeE1_payload_libre
  crit_isTermCodeE1_rejects crit_isTermCodeE1_rejects_implc
  crit_junk_SubCodesCritica_open1 crit_junk_var0_witness1 crit_num_ne crit_tag_absurd
  funcOkT1 impT isFormCodeB2 isTC1 isTermCodeB1 isTermCodeE1 lencLiftPred lencLiftPred_at
  liftF_argsIn liftF_isTermCodeE1 liftF_wfAll1 liftT_liftc liftT_liftsc liftTerm_objList
  lorAll mem_self_tcodes1 mem_tcodes1s_of_mem nthLiftPred nthLiftPred_at nthLiftPred_base
  nthLiftPred_step nulOkF okE1_T okE1_Ts prf_argsIn_head prf_argsIn_lift
  prf_argsIn_lift_body prf_argsIn_of_closed prf_argsIn_tail prf_bdAll_numeral
  prf_bdAll_of_bound prf_boundedIn_liftsc prf_cdrc_cons prf_congr_argsIn
  prf_congr_In_left prf_congr_lenc prf_congr_liftsc prf_congr_nthc_lst prf_consOk_cons
  prf_crit_In_rejects_open1 prf_In_liftsc prf_In_objList prf_isTC1_lift prf_isTC1_tcodes
  prf_isTC1_tcodes_lifted prf_isTC1_tcodes_lifted2 prf_isTermCodeE1_func
  prf_isTermCodeE1_lift prf_isTermCodeE1_str prf_isTermCodeE1_var prf_lenc_c1 prf_lenc_c2
  prf_lenc_c3 prf_lenc_liftsc prf_lenc_liftsc_all prf_lenc_liftsc_step prf_lenc_objList
  prf_lenc_termsCodeM prf_lorL prf_lorR prf_nthc_c1 prf_nthc_c2 prf_nthc_liftsc
  prf_nthc_objList prf_nthc_termsCodeM prf_or_elim_imp prf_orL prf_orR
  prf_shape_strengthens prf_shapeBin_str prf_shapeUn_str prf_str_and prf_wfAll1_lift
  prf_wfAll1_lift_body PrfH_congr_argsIn PrfH_congr_In_left PrfH_congr_isTermCodeE1
  PrfH_congr_lenc PrfH_congr_nthc_idx PrfH_congr_nthc_lst PrfH_congr_succ
  PrfH_inst_argsIn PrfH_inst_wfAll1 shapeBin shapeUn strBinOkF1 substF_argsIn
  substF_isTermCodeE1 substTerm_objList tcodes1 tcodes1s unOkF varOkT wfAll1 wfAll1Body
)

-- Export: API publica del reconocedor de codigo de FORMULA ecuacional (DOS listas).
-- Los SIETE homonimos de `SinWTs` NO salen por aqui: a raiz sale el de `SinWTs`.
export ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS (
  clAtom clBin clBot clEq clUn CRIT_E2_rejects_funcc CRIT_E2_rejects_varc
  CRIT_hasWit_lift CRIT_hasWit_real CRIT_hasWit_real_lifted CRIT_isFC1_rejects_varc
  hasWit hasWitF isFC1 isFormCodeE2 liftF_hasWit liftF_hasWitF liftF_isFC1
  liftF_isFormCodeE2 liftF_isTC1 liftF_wfAllF lor_map prf_isFormCodeE2_of_boundedIn
  prf_isFormCodeE2_of_In prf_isFormCodeE2_str prf_shapeBin_str' prf_shapeNul_str
  prf_shapeUn_str' PrfH_congr_isFormCodeE2 PrfH_inst_wfAllF shapeNul substF_hasWit
  substF_isFC1 substF_isFormCodeE2 substF_isTC1 substF_wfAll1 substF_wfAllF wfAllF
  wfAllFBody
)

-- Export: API publica de la NO-VACUIDAD (testigos explicitos y computables).
export ROBINSON_PlusPlus.Meta.CodeWitnessPrf.HW (
  cl_atom_real cl_bin_real cl_eq_real cl_un_real closed_formCodeM closed_mem_fcodesF
  closed_mem_tcodesF fcodesF lift_wF lift_wT mem_self_fcodesF node_and node_atom node_bot
  node_eq node_ex node_forall node_impl node_or okF okT_F prf_hasWitF_real prf_isFC1_real
  prf_refl' prf_shapeBin_real prf_shapeNul_real prf_shapeUn_real prf_wfAll1_of_list
  prf_wfAll1_real prf_wfAllF_of_list prf_wfAllF_real subst_wF subst_wT tcodesF
)

/-! ## §1.2 · LOS 202 NOMBRES, EJERCITADOS SIN CUALIFICAR.

    Un `export` que nombra algo inexistente ya falla en el propio `export`; lo que NO
    detecta es la AMBIGUEDAD, que en Lean 4 es perezosa y solo rompe en el punto de uso.
    Por eso se referencian los 202, uno a uno. Si esto compila, ninguno choca. -/
#check @argsIn
#check @argsInBody
#check @binOkF
#check @closed_mem_tcodes1
#check @closed_mem_tcodes1s
#check @closed_termCodeM
#check @CodeClosed
#check @cOk
#check @consOk
#check @crit_argsIn_lenc_zero
#check @crit_closed_implc
#check @crit_cOk2_absurd
#check @crit_cOk3_absurd
#check @crit_isFormCodeB2_rejects
#check @crit_isFormCodeB2_rejects_funcc
#check @crit_isFormCodeB2_rejects_varc
#check @crit_isTC1_junk_refuted_open
#check @crit_isTermCodeB1_rejects
#check @crit_isTermCodeB1_rejects_andc
#check @crit_isTermCodeB1_rejects_atomc
#check @crit_isTermCodeB1_rejects_botc
#check @crit_isTermCodeB1_rejects_eqc
#check @crit_isTermCodeB1_rejects_exc
#check @crit_isTermCodeB1_rejects_forallc
#check @crit_isTermCodeB1_rejects_implc
#check @crit_isTermCodeB1_rejects_orc
#check @crit_isTermCodeE1_funcc_lenc_zero
#check @crit_isTermCodeE1_payload_libre
#check @crit_isTermCodeE1_rejects
#check @crit_isTermCodeE1_rejects_implc
#check @crit_junk_SubCodesCritica_open1
#check @crit_junk_var0_witness1
#check @crit_num_ne
#check @crit_tag_absurd
#check @funcOkT1
#check @impT
#check @isFormCodeB2
#check @isTC1
#check @isTermCodeB1
#check @isTermCodeE1
#check @lencLiftPred
#check @lencLiftPred_at
#check @liftF_argsIn
#check @liftF_isTermCodeE1
#check @liftF_wfAll1
#check @liftT_liftc
#check @liftT_liftsc
#check @liftTerm_objList
#check @lorAll
#check @mem_self_tcodes1
#check @mem_tcodes1s_of_mem
#check @nthLiftPred
#check @nthLiftPred_at
#check @nthLiftPred_base
#check @nthLiftPred_step
#check @nulOkF
#check @okE1_T
#check @okE1_Ts
#check @prf_argsIn_head
#check @prf_argsIn_lift
#check @prf_argsIn_lift_body
#check @prf_argsIn_of_closed
#check @prf_argsIn_tail
#check @prf_bdAll_numeral
#check @prf_bdAll_of_bound
#check @prf_boundedIn_liftsc
#check @prf_cdrc_cons
#check @prf_congr_argsIn
#check @prf_congr_In_left
#check @prf_congr_lenc
#check @prf_congr_liftsc
#check @prf_congr_nthc_lst
#check @prf_consOk_cons
#check @prf_crit_In_rejects_open1
#check @prf_In_liftsc
#check @prf_In_objList
#check @prf_isTC1_lift
#check @prf_isTC1_tcodes
#check @prf_isTC1_tcodes_lifted
#check @prf_isTC1_tcodes_lifted2
#check @prf_isTermCodeE1_func
#check @prf_isTermCodeE1_lift
#check @prf_isTermCodeE1_str
#check @prf_isTermCodeE1_var
#check @prf_lenc_c1
#check @prf_lenc_c2
#check @prf_lenc_c3
#check @prf_lenc_liftsc
#check @prf_lenc_liftsc_all
#check @prf_lenc_liftsc_step
#check @prf_lenc_objList
#check @prf_lenc_termsCodeM
#check @prf_lorL
#check @prf_lorR
#check @prf_nthc_c1
#check @prf_nthc_c2
#check @prf_nthc_liftsc
#check @prf_nthc_objList
#check @prf_nthc_termsCodeM
#check @prf_or_elim_imp
#check @prf_orL
#check @prf_orR
#check @prf_shape_strengthens
#check @prf_shapeBin_str
#check @prf_shapeUn_str
#check @prf_str_and
#check @prf_wfAll1_lift
#check @prf_wfAll1_lift_body
#check @PrfH_congr_argsIn
#check @PrfH_congr_In_left
#check @PrfH_congr_isTermCodeE1
#check @PrfH_congr_lenc
#check @PrfH_congr_nthc_idx
#check @PrfH_congr_nthc_lst
#check @PrfH_congr_succ
#check @PrfH_inst_argsIn
#check @PrfH_inst_wfAll1
#check @shapeBin
#check @shapeUn
#check @strBinOkF1
#check @substF_argsIn
#check @substF_isTermCodeE1
#check @substTerm_objList
#check @tcodes1
#check @tcodes1s
#check @unOkF
#check @varOkT
#check @wfAll1
#check @wfAll1Body
#check @clAtom
#check @clBin
#check @clBot
#check @clEq
#check @clUn
#check @CRIT_E2_rejects_funcc
#check @CRIT_E2_rejects_varc
#check @CRIT_hasWit_lift
#check @CRIT_hasWit_real
#check @CRIT_hasWit_real_lifted
#check @CRIT_isFC1_rejects_varc
#check @hasWit
#check @hasWitF
#check @isFC1
#check @isFormCodeE2
#check @liftF_hasWit
#check @liftF_hasWitF
#check @liftF_isFC1
#check @liftF_isFormCodeE2
#check @liftF_isTC1
#check @liftF_wfAllF
#check @lor_map
#check @prf_isFormCodeE2_of_boundedIn
#check @prf_isFormCodeE2_of_In
#check @prf_isFormCodeE2_str
#check @prf_shapeBin_str'
#check @prf_shapeNul_str
#check @prf_shapeUn_str'
#check @PrfH_congr_isFormCodeE2
#check @PrfH_inst_wfAllF
#check @shapeNul
#check @substF_hasWit
#check @substF_isFC1
#check @substF_isFormCodeE2
#check @substF_isTC1
#check @substF_wfAll1
#check @substF_wfAllF
#check @wfAllF
#check @wfAllFBody
#check @cl_atom_real
#check @cl_bin_real
#check @cl_eq_real
#check @cl_un_real
#check @closed_formCodeM
#check @closed_mem_fcodesF
#check @closed_mem_tcodesF
#check @fcodesF
#check @lift_wF
#check @lift_wT
#check @mem_self_fcodesF
#check @node_and
#check @node_atom
#check @node_bot
#check @node_eq
#check @node_ex
#check @node_forall
#check @node_impl
#check @node_or
#check @okF
#check @okT_F
#check @prf_hasWitF_real
#check @prf_isFC1_real
#check @prf_refl'
#check @prf_shapeBin_real
#check @prf_shapeNul_real
#check @prf_shapeUn_real
#check @prf_wfAll1_of_list
#check @prf_wfAll1_real
#check @prf_wfAllF_of_list
#check @prf_wfAllF_real
#check @subst_wF
#check @subst_wT
#check @tcodesF

/-! ## §1.3 · Y USADOS DE VERDAD, no solo `#check`: el vocabulario del frente a secas. -/

example (w c : Term) : Formula := isTC1 w c
example (wT Y : Term) : Formula := argsIn wT Y
example (c : Term) : Formula := hasWitF c
example (phi : Formula) : List Term := fcodesF phi
example (phi : Formula) : List Term := tcodesF phi

example (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := liftF_isTC1 k w c

example (phi : Formula) : Prf (hasWitF (formCodeM phi)) := prf_hasWitF_real phi

example (w hd tl : Term) : Prf (Formula.impl (argsIn w (cons hd tl)) (In hd w)) :=
  prf_argsIn_head w hd tl

example (w hd tl : Term) : Prf (Formula.impl (argsIn w (cons hd tl)) (argsIn w tl)) :=
  prf_argsIn_tail w hd tl

example {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := impT h1 h2

example {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) : Prf (lor A B ⇒ C) :=
  prf_or_elim_imp h1 h2

/-- El nombre a secas resuelve al MISMO constante que el cualificado. Puente `rfl`. -/
example : @isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 := rfl
example : @impT = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT := rfl
example : @liftF_isTC1 = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.liftF_isTC1 := rfl
example : @prf_hasWitF_real = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.HW.prf_hasWitF_real := rfl

/-! ## §1.4 · REGRESION — EL RIESGO REAL DEL BLOQUE

    Los dos consumidores de produccion hacen `open` de estos namespaces. Con los alias en
    RAIZ ademas del `open`, cada nombre se resuelve por DOS caminos. Aqui se reproducen
    sus bloques `open` LITERALES y se usan los nombres, para medir si Lean deduplica
    (mismo constante por los dos caminos ⇒ sin ambiguedad) o si el bloque los rompe. -/

section RegresionLiftcCodePrf
-- literal de `Meta/LiftcCodePrf.lean:89-90` (open SELECTIVO)
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
  (shapeUn shapeBin argsIn argsInBody isTermCodeE1 impT prf_or_elim_imp)

example (X : Term) (k : Nat) : Formula := shapeUn X k
example (X : Term) (k : Nat) : Formula := shapeBin X k
example (wT Y : Term) : Formula := argsIn wT Y
example (wT Y : Term) : Formula := argsInBody wT Y
example (wT X : Term) : Formula := isTermCodeE1 wT X
example {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := impT h1 h2
example {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) : Prf (lor A B ⇒ C) :=
  prf_or_elim_imp h1 h2
end RegresionLiftcCodePrf

section RegresionEvalLiftcPrf
-- literal de `Meta/EvalLiftcPrf.lean:166-168` (SinWTs ENTERO + ENS selectivo)
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS
  (hasWit liftF_isTC1 substF_isTC1 substF_wfAll1 liftF_hasWit substF_hasWit CRIT_hasWit_real)

example (w c : Term) : Formula := isTC1 w c
example (w : Term) : Formula := wfAll1 w
example (wT X : Term) : Formula := isTermCodeE1 wT X
example (c : Term) : Formula := hasWit c
example (k : Nat) (w c : Term) :
    liftFormula k (isTC1 w c) = isTC1 (liftTerm k w) (liftTerm k c) := liftF_isTC1 k w c
example (v : Nat) (s w : Term) :
    substFormula v s (wfAll1 w) = wfAll1 (substTerm v s w) := substF_wfAll1 v s w
example (t : Term) : Prf (hasWit (termCodeM t)) := CRIT_hasWit_real t
-- los cinco De Bruijn que `EvalLiftcPrf` usa de `SinWTs` (por eso su open de ENS es selectivo)
example (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := liftF_argsIn k wT Y
example (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) :=
  substF_argsIn v s wT Y
example (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X) = isTermCodeE1 (liftTerm k wT) (liftTerm k X) :=
  liftF_isTermCodeE1 k wT X
example (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X) = isTermCodeE1 (substTerm v s wT) (substTerm v s X) :=
  substF_isTermCodeE1 v s wT X
example (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := liftF_wfAll1 k w

/-- ⚠️ MEDIDA CONTRA `EvalLiftcPrf.lean:329-333`. Ese docstring dice que `impT` esta
    cualificado ahi porque «este modulo abre los DOS namespaces» y dejarlo a secas
    «haria depender de un desempate del elaborador». FALSO: su `open` de `ENS` es
    SELECTIVO y NO incluye `impT`, asi que a secas resuelve —sin desempate— a
    `SinWTs.impT`. Se mide con los mismos `open` de arriba. -/
example {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := impT h1 h2
example : @impT = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT := rfl

/-- CONTROL: la ambiguedad que `EvalLiftcPrf:158-161` SI documenta bien —
    `SinWTs.prf_congr_liftc` contra el alias de raiz de `NumCodeClosedPrf`— sigue viva,
    y es PRE-EXISTENTE al bloque `export` (por eso ese nombre queda fuera del bloque). -/
example : True := by
  fail_if_success (have _h := @prf_congr_liftc)
  trivial
end RegresionEvalLiftcPrf

/-! ############################################################################
    # §2 · LOS SIETE LEMAS DUPLICADOS ENTRE `SinWTs` Y `ENS`
    ############################################################################ -/

namespace T2Dup

open ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-! ## §2.1-§2.7 · LOS SIETE PUENTES `rfl`, ENTRE CONSTANTES CUALIFICADAS. -/

theorem dup_1_liftF_argsIn         : @SinWTs.liftF_argsIn         = @ENS.liftF_argsIn := rfl
theorem dup_2_substF_argsIn        : @SinWTs.substF_argsIn        = @ENS.substF_argsIn := rfl
theorem dup_3_liftF_isTermCodeE1   : @SinWTs.liftF_isTermCodeE1   = @ENS.liftF_isTermCodeE1 := rfl
theorem dup_4_substF_isTermCodeE1  : @SinWTs.substF_isTermCodeE1  = @ENS.substF_isTermCodeE1 := rfl
theorem dup_5_liftF_wfAll1         : @SinWTs.liftF_wfAll1         = @ENS.liftF_wfAll1 := rfl
theorem dup_6_impT                 : @SinWTs.impT                 = @ENS.impT := rfl
theorem dup_7_prf_or_elim_imp      : @SinWTs.prf_or_elim_imp      = @ENS.prf_or_elim_imp := rfl

/-! ## §2.8 · CONTROLES NEGATIVOS «DE TIPO»: el `rfl` discrimina ENUNCIADOS.

    Cada par es «primo hermano» del correspondiente de arriba (lift/subst, wfAll1/wfAllF,
    isTermCodeE1/isFormCodeE2, impT/prf_or_elim_imp). Si el puente fuese degenerado,
    estos tambien pasarian. Ninguno pasa. -/

example : True := by
  fail_if_success (exact (rfl : @SinWTs.liftF_argsIn = @SinWTs.substF_argsIn))
  fail_if_success (exact (rfl : @SinWTs.substF_argsIn = @SinWTs.liftF_argsIn))
  fail_if_success (exact (rfl : @SinWTs.liftF_isTermCodeE1 = @ENS.liftF_isFormCodeE2))
  fail_if_success (exact (rfl : @SinWTs.substF_isTermCodeE1 = @ENS.substF_isFormCodeE2))
  fail_if_success (exact (rfl : @SinWTs.liftF_wfAll1 = @ENS.liftF_wfAllF))
  fail_if_success (exact (rfl : @SinWTs.impT = @SinWTs.prf_or_elim_imp))
  fail_if_success (exact (rfl : @SinWTs.prf_or_elim_imp = @SinWTs.impT))
  trivial

/-! ## §2.9 · EL CONTROL QUE ACREDITA LA TECNICA — sobre `def`, no sobre `Prop`.

    Los siete de arriba son TEOREMAS: viven en `Prop`, luego la irrelevancia de pruebas
    los colapsa en cuanto los TIPOS coinciden. Podria objetarse que el `rfl` no mira
    nada. Aqui se cierra la objecion con dos `def` del MISMO TIPO exacto
    (`Term → Nat → Formula`), donde la irrelevancia NO opera y `rfl` tiene que comparar
    CUERPOS: el positivo pasa, el negativo no. -/

-- NEGATIVO: mismo tipo, cuerpos distintos ⇒ `rfl` FALLA.
example : True := by
  fail_if_success (exact (rfl : @SinWTs.shapeUn = @SinWTs.shapeBin))
  trivial

-- POSITIVO: `rfl` sobre `def` SI atraviesa cuando el cuerpo coincide.
example (c : Term) : ENS.hasWit c = Formula.ex (SinWTs.isTC1 (.var 0) (liftTerm 0 c)) := rfl

-- y los DOS tienen efectivamente ese tipo (que el negativo no falle por tipos distintos).
example : (@SinWTs.shapeUn : Term → Nat → Formula) = SinWTs.shapeUn := rfl
example : (@SinWTs.shapeBin : Term → Nat → Formula) = SinWTs.shapeBin := rfl

/-! ## §2.10 · TRAS BORRAR LAS SIETE COPIAS DE `ENS`, LOS USOS SIGUEN CUADRANDO.

    Los ocho usos internos de `ENS` (:1435, :1441, :1446, :1453, :1459, :1573, :1580,
    :1599) y los cuatro de `impT`/`prf_or_elim_imp` (:1657, :1704, :1723, :1729) estan
    TODOS por debajo del `open SinWTs` de :1412, asi que reconducen solos. Aqui se mide
    que el enunciado que quedaria en juego es el mismo, uno por uno. -/

section TrasBorrado
open SinWTs
example (k : Nat) (wT Y : Term) :
    liftFormula k (argsIn wT Y) = argsIn (liftTerm k wT) (liftTerm k Y) := liftF_argsIn k wT Y
example (v : Nat) (s wT Y : Term) :
    substFormula v s (argsIn wT Y) = argsIn (substTerm v s wT) (substTerm v s Y) :=
  substF_argsIn v s wT Y
example (k : Nat) (wT X : Term) :
    liftFormula k (isTermCodeE1 wT X) = isTermCodeE1 (liftTerm k wT) (liftTerm k X) :=
  liftF_isTermCodeE1 k wT X
example (v : Nat) (s wT X : Term) :
    substFormula v s (isTermCodeE1 wT X) = isTermCodeE1 (substTerm v s wT) (substTerm v s X) :=
  substF_isTermCodeE1 v s wT X
example (k : Nat) (w : Term) :
    liftFormula k (wfAll1 w) = wfAll1 (liftTerm k w) := liftF_wfAll1 k w
example {A B C : Formula} (h1 : Prf (A ⇒ B)) (h2 : Prf (B ⇒ C)) : Prf (A ⇒ C) := impT h1 h2
example {A B C : Formula} (h1 : Prf (A ⇒ C)) (h2 : Prf (B ⇒ C)) : Prf (lor A B ⇒ C) :=
  prf_or_elim_imp h1 h2
-- y resuelven a SinWTs, no a ENS (que es lo que quedara tras el borrado)
example : @liftF_argsIn = @SinWTs.liftF_argsIn := rfl
example : @impT = @SinWTs.impT := rfl
end TrasBorrado

end T2Dup

/-! ############################################################################
    # §3 · LOS DOCSTRINGS FALSOS — CENSO DE `env.constants`, NO GREP
    ############################################################################ -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let pats : List String :=
    ["DescMutua", "Paso2", "S_Descenso", "EvalSubsttc", "SubstfcEx",
     "CRIT_hasWit_lift", "prf_isTermCodeE1_of_In", "DESCENSO_hasWit"]
  for p in pats do
    let mut hits : Array Name := #[]
    for (n, _) in env.constants.toList do
      if !n.isInternal && (n.toString.splitOn p).length > 1 then
        hits := hits.push n
    let srt := hits.qsort (fun a b => a.toString < b.toString)
    IO.println s!"CENSO «{p}» : {srt.size} constantes"
    for n in srt do IO.println s!"        {n}"

/-! El censo de arriba es la MEDIDA de que el docstring de `CodeWitnessPrf.lean:77-82`
    miente en sus cuatro afirmaciones, y el de :1606 en la suya.

    `objList` tampoco lo aporta este modulo: es `Meta/Sigma1CorePrf.objList`. Puente: -/
example (L : List Term) :
    ROBINSON_PlusPlus.Meta.Sigma1CorePrf.objList L = objList L := rfl

/-! ## §3.1 · LA CLAUSULA DE FOOTPRINT DE LA CABECERA, MEDIDA.

    La cabecera (:51 y :68) dice «Footprint net-0 puro» y «Cero axiomas de Lean».
    `#print axioms` es el arbitro. -/

#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.HW.prf_hasWitF_real
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.HW.prf_isFC1_real
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.CRIT_hasWit_real
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTC1_tcodes
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_head
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_argsIn_tail

/-! ############################################################################
    # §4 · DOS DUPLICADOS MAS, QUE EL ENCARGO NO LISTABA
    ############################################################################ -/

namespace T2Extra

open ROBINSON_PlusPlus.Meta.CodeWitnessPrf

/-! ## §4.1 · `SinWTs.mem_of_getElem?` re-demuestra un lema del CORE de Lean.

    `List.mem_of_getElem?` ya lo da, y en general (para cualquier `α`). El del modulo es
    la instancia `α := Term`, probada a mano por induccion. -/

theorem mem_of_getElem?_es_el_del_core :
    @SinWTs.mem_of_getElem?
      = fun (L : List Term) (k : Nat) (x : Term) (h : L[k]? = some x) =>
          List.mem_of_getElem? h := rfl

/-! ## §4.2 · `SinWTs.prf_congr_liftc` / `PrfH_congr_liftc` re-demuestran los de
       `Meta/NumCodeClosedPrf.lean`, que YA estan en produccion Y YA estan en la raiz.
       Son EXACTAMENTE los dos nombres que impiden exportar el namespace entero. -/

theorem prf_congr_liftc_es_redundante {t₁ t₂ : Term} (v : Term) (h : Prf (t₁ =eq t₂)) :
    Prf (liftc v t₁ =eq liftc v t₂) :=
  ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc h

theorem PrfH_congr_liftc_es_redundante {Γ : List Formula} {t₁ t₂ : Term} (v : Term)
    (h : PrfH Γ (t₁ =eq t₂)) : PrfH Γ (liftc v t₁ =eq liftc v t₂) :=
  ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.PrfH_congr_liftc h

/-- Y en el otro sentido: el de produccion sale del de `SinWTs`. Equivalentes. -/
theorem prf_congr_liftc_ida {c a b : Term} (h : Prf (a =eq b)) :
    Prf (liftc c a =eq liftc c b) :=
  SinWTs.prf_congr_liftc c h

/-- Pero NO son la misma constante (el de `SinWTs` tiene `v` EXPLICITO): por eso
    exportar el de `SinWTs` a raiz seria una colision de verdad, no un alias inocuo. -/
example : True := by
  fail_if_success
    (exact (rfl : @SinWTs.prf_congr_liftc
                    = @ROBINSON_PlusPlus.Meta.NumCodeClosedPrf.prf_congr_liftc))
  trivial

#print axioms mem_of_getElem?_es_el_del_core
#print axioms prf_congr_liftc_es_redundante
#print axioms PrfH_congr_liftc_es_redundante

end T2Extra

#print axioms T2Dup.dup_1_liftF_argsIn
#print axioms T2Dup.dup_2_substF_argsIn
#print axioms T2Dup.dup_3_liftF_isTermCodeE1
#print axioms T2Dup.dup_4_substF_isTermCodeE1
#print axioms T2Dup.dup_5_liftF_wfAll1
#print axioms T2Dup.dup_6_impT
#print axioms T2Dup.dup_7_prf_or_elim_imp
