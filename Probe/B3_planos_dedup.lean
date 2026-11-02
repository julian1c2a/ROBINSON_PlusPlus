/- # `Probe/B3_planos_dedup.lean` — AUDITORIA DE DUPLICACION de `sondeos/SubstfcPlanos.lean`

   ANGULO (B). Para cada una de las **34** declaraciones del sondeo que no esta en produccion
   por nombre (39 en total, 5 ya estan), el cajon: (1) duplicado exacto ⇒ puente, no promover;
   (2) casi-duplicado; (3) genuinamente nuevo. Y la SUBSUNCION AL REVES (ADR-019).

   ## Este es el arnes 1 de 4. Los otros tres son los TESTS DE DESTINO:

   | fichero | `import` copiados de | que prueba |
   |---|---|---|
   | `Probe/B3_planos_dedup.lean` (este) | `Meta/LiftcCodePrf.lean` | `prf_substtc_binK_at` ⊐ `prf_substtc_binT_at` cabe en `LiftcCodePrf`; y la 8ª copia del patron `pcc_congr_*_code` |
   | `Probe/B3_planos_dedup_kit.lean` | `Meta/CodeCtorKit.lean` | `binK` ⊐ `binT` cabe en `CodeCtorKit`; y `pcc_congr_hole_code` cabe ahi y da el enunciado LITERAL de CINCO de las siete copias de produccion (las dos de `liftcT`/`liftscT` se declaran despues, mismo esquema) |
   | `Probe/B3_planos_dedup_funcc3.lean` | `Meta/EvalArithPrf.lean` | el KIT TERNARIO entero (9 decls) cabe en `EvalArithPrf` |
   | `Probe/B3_planos_dedup_opens.lean` | el SONDEO (barrel + sus 13 `open`) | los 5 duplicados exactos son drop-in bajo los `open` del sondeo; `binct` ⊐ SEIS ctores objeto |

   ## EL VEREDICTO, por cajones (34 declaraciones)

   **(1) DUPLICADO EXACTO — NO PROMOVER: 0 de las 34.** Los cinco duplicados que trae el sondeo
   lo son por NOMBRE, y por eso no estaban entre las 34; van en §3 y se verifican en el arnes de
   `open`s. De las 34 restantes, NINGUNA es un duplicado exacto con otro nombre ni con la
   orientacion invertida: se ha buscado por nombre, por cuerpo (md5 del texto de la declaracion)
   y por forma del enunciado familia por familia en los 109 modulos de produccion.

   **(2) CASI-DUPLICADO — 1.** `pcc_congr_substfcT_arg3_code` es la OCTAVA copia literal de un
   patron de 12 lineas del que produccion ya guarda SIETE. Ver §2 y el arnes `_kit`.

   **(3) GENUINAMENTE NUEVAS — 33.** El resto. Ver el desglose de §4.

   **SUBSUNCION AL REVES (ADR-019) — 3 lemas y 1 def del sondeo son MAS GENERALES que algo que
   produccion ya tiene** (son parte de las 33, pero NO van al modulo nuevo: van a BAJAR):
   `binK` ⊐ `binT`; `prf_congr_binK` ⊐ `prf_congr_binT`; y `prf_substtc_binK_at` ⊐ **tres**
   lemas a la vez (`prf_substtc_binT_at`, `prf_substtc_funccT_at`, `prf_substtc_binT`).
   Mas `binK_binT`, el puente. Ver §1 y el arnes `_kit`.
   Y una segunda, al nivel OBJETO: `binct` ⊐ `funcc`/`atomc`/`eqc`/`implc`/`andc`/`orc`
   (seis `def` de `Minimal/Axioms.lean`, los seis puentes por `rfl`) — pero esa **NO obliga a
   bajar nada**, porque lo que subsume son definiciones, no lemas duplicados. Ver el arnes
   de `open`s §3.

   ⚠️ **Citas por NOMBRE, no por linea.** Las mediciones de texto son sobre
   `sondeos/SubstfcPlanos.lean` con **581 lineas** y **md5 `d1ec711199d5099bbcac8d8dc0be0cf8`**.

   ⚠️ **LA LISTA DE `import` DE ESTE FICHERO ES, BYTE A BYTE, LA DE
   `ROBINSON_PlusPlus/Meta/LiftcCodePrf.lean`** (25 modulos de `Meta/`, NI el barrel
   `ROBINSON_PlusPlus.Meta` NI nada aguas abajo). Consecuencia deliberada: lo que
   `LiftcCodePrf` DECLARA (`prf_substtc_termCode_closed`, `prf_substtc_binT_at`, `liftcT`…)
   NO esta visible; lo que hace falta de ahi se REDECLARA en §1.0 con prefijo `L_`, copiado
   verbatim, marcando que en el modulo real ya existe sobre la linea de insercion.

   CERO axiomas de Lean nuevos, CERO `sorry`. -/
import ROBINSON_PlusPlus.Meta.ArithPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.Godel
import ROBINSON_PlusPlus.Meta.Hilbert
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.LineWFTrackedPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.Provability
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf ROBINSON_PlusPlus.Meta.EvalLtPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.HilbertDeduction ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf ROBINSON_PlusPlus.Meta.TrackedCorePrf
open ROBINSON_PlusPlus.Meta.LineWFTrackedPrf ROBINSON_PlusPlus.Meta.EvalRunFnPrf

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace B3PlanosDedup

/-! ## §1 · SUBSUNCION AL REVES — `prf_substtc_binK_at` ⊐ `prf_substtc_binT_at`
        (destino: `Meta/LiftcCodePrf.lean`, junto al lema que subsume)

    Produccion tiene, en `Meta/LiftcCodePrf.lean` y con este enunciado exacto:

      `theorem prf_substtc_binT_at (m v : Nat) (W a b : Term) :`
      `    Prf (substtc (numeral v) W (binT m a b)`
      `      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b))`

    El del sondeo es el MISMO con la etiqueta abstracta y CERRADA (`hT`) en vez del `numeralM m`
    concreto. Su prueba es la de produccion palabra por palabra salvo el primer paso, donde
    `prf_substtc_termCode_numeralM v m W` se cambia por `prf_substtc_termCode_closed n W T hT`
    — y el primero es, en produccion, un corolario del segundo. Generalizacion ESTRICTA.

    ⛔ ADR-019: `LiftcCodePrf` es aguas ARRIBA del modulo donde caeria el sondeo, asi que
    NO se puede reescribir `prf_substtc_binT_at` como corolario desde alli. Hay que **BAJAR
    el general** a `LiftcCodePrf` (y anadirlo a su bloque `export`, que hoy lista
    `prf_substtc_unT_at prf_substtc_binT_at prf_substtc_varcT_at prf_substtc_funccT_at`).

    ⚠️ Y al bajarlo hay que quitar `prf_substtc_binK_at` del sondeo: si se promueve el sondeo
    con su copia, son DOS constantes distintas con el mismo enunciado. -/

/-! ### §1.0 · Lo que `LiftcCodePrf` ya declara ARRIBA del punto de insercion (verbatim) -/

theorem L_prf_substtc_termCode_closed (v : Nat) (W t : Term)
    (ht : ∀ c : Nat, liftTerm c t = t) :
    Prf (substtc (numeral v) W (termCode t) =eq termCode t) := by
  have h := prf_substtc_arith_open v W t
  rwa [substCodeT_closed v W t ht] at h

theorem L_prf_substtc_termCode_numeralM (v m : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode (numeralM m)) =eq termCode (numeralM m)) :=
  L_prf_substtc_termCode_closed v W (numeralM m) (fun c => liftTerm_numeralM c m)

theorem L_prf_substtc_termCode_zero (v : Nat) (W : Term) :
    Prf (substtc (numeral v) W (termCode zero) =eq termCode zero) :=
  L_prf_substtc_termCode_closed v W zero (fun _ => rfl)

/-! ### §1.1 · `binK` y el lema GENERAL del sondeo, aqui

     (El test de destino de `binK` mismo NO es este fichero sino `B3_planos_dedup_kit.lean`,
     que importa lo de `CodeCtorKit`: ahi es donde vive `binT` y donde `binK` debe bajar.) -/

def binK (H a b : Term) : Term := consT H (consT a (consT b (termCode nil)))

/-- Puente del sondeo con el `binT` REAL de produccion: `rfl`. -/
theorem binK_binT (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

theorem prf_congr_binK {H a a' b b' : Term} (ha : Prf (a =eq a')) (hb : Prf (b =eq b')) :
    Prf (binK H a b =eq binK H a' b') :=
  prf_congr_consT (prf_refl _) (prf_congr_consT ha (prf_congr_consT hb (prf_refl _)))

theorem prf_substtc_binK_at (T : Term) (hT : ∀ c : Nat, liftTerm c T = T)
    (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode T) a b)
      =eq binK (termCode T) (substtc (numeral n) W a) (substtc (numeral n) W b)) := by
  unfold binK consT
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_eq_trans (prf_congr_cons_head (L_prf_substtc_termCode_closed n W T hT)) ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  refine prf_congr_funcc2 ?_
  refine prf_congr_cons_tail (prf_congr_cons_head ?_)
  refine prf_eq_trans (prf_substtc_funcc2 _ _ _ _ _) ?_
  exact prf_congr_funcc2
    (prf_congr_cons_tail (prf_congr_cons_head (L_prf_substtc_termCode_zero n W)))

/-- **CONTROL ADR-019 (a)** — el enunciado LITERAL de `LiftcCodePrf.prf_substtc_binT_at`
    sale del general en UN paso. Esta es la reescritura propuesta del lema de produccion,
    que hoy son 12 lineas de `refine`. El descenso no pide ninguna constante que
    `LiftcCodePrf` no tenga ya: este fichero importa SOLO lo que importa `LiftcCodePrf`. -/
theorem CTRL_prf_substtc_binT_at_desde_binK (m v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT m a b)
      =eq binT m (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) v W a b

/-- **CONTROL (b)** — con `m := 1` cae tambien `prf_substtc_funccT_at`, porque
    `funccT = binT 1` por definicion (`LiftcCodePrf.funccT_eq_binT`). Dos lemas del `export`
    de `LiftcCodePrf` por el precio de uno. -/
theorem CTRL_prf_substtc_funccT_at_desde_binK (v : Nat) (W a b : Term) :
    Prf (substtc (numeral v) W (binT 1 a b)
      =eq binT 1 (substtc (numeral v) W a) (substtc (numeral v) W b)) :=
  prf_substtc_binK_at (numeralM 1) (fun c => liftTerm_numeralM c 1) v W a b

/-- **CONTROL (c)** — y `numeral 0` es `zero`, asi que el general cubre tambien el caso a
    nivel `zero`, que es `CodeCtorKit.prf_substtc_binT`. TRES lemas de produccion. -/
theorem CTRL_prf_substtc_binT_zero_desde_binK (m : Nat) (W a b : Term) :
    Prf (substtc zero W (binT m a b) =eq binT m (substtc zero W a) (substtc zero W b)) :=
  prf_substtc_binK_at (numeralM m) (fun c => liftTerm_numeralM c m) 0 W a b

/-- **CONTROL (d) — la generalidad es ESTRICTA**: `binK` acepta etiquetas que no son
    `termCode (numeralM m)` (aqui, el codigo de una cadena), y el lema general las cubre.
    `binT` no las alcanza. -/
theorem CTRL_generalidad_estricta (n : Nat) (W a b : Term) :
    Prf (substtc (numeral n) W (binK (termCode (strCode "liftc")) a b)
      =eq binK (termCode (strCode "liftc"))
        (substtc (numeral n) W a) (substtc (numeral n) W b)) :=
  prf_substtc_binK_at (strCode "liftc") (fun c => liftTerm_strCode c _) n W a b

/-! ## §2 · CASI-DUPLICADO — `pcc_congr_substfcT_arg3_code` es la OCTAVA copia del patron.

    Produccion guarda SIETE copias de la misma prueba de 12 lineas, cambiando solo el contexto:

      `CodeCtorKit`  : `pcc_congr_binT_2_code`, `pcc_congr_binT_1_code`, `pcc_congr_unT_code`
      `LiftcCodePrf` : `pcc_congr_liftcT_arg2_code`, `pcc_congr_liftscT_arg2_code`,
                       `pcc_congr_consT_arg2_code`, `pcc_congr_consT_arg1_code`

    El sondeo trae la octava. Aqui se compila el lema GENERICO `pcc_congr_hole_code` (el
    contexto entra como `F : Term → Term`) y se deriva de el la del sondeo. En
    `Probe/B3_planos_dedup_kit.lean` se comprueba, con los imports de `CodeCtorKit`, que el
    generico cabe ahi y que de el salen CINCO de las siete de produccion con enunciado literal
    (las dos de `liftcT`/`liftscT` no se pueden probar alli porque `liftcT` se declara
    despues, pero son el mismo esquema).

    ⚠️ **No es un duplicado**: el enunciado del sondeo es sobre `substfcT`, que no existe en
    produccion. Es un casi-duplicado de PRUEBA. Recomendacion: promover el generico a
    `CodeCtorKit` y dejar la del sondeo como corolario de tres lineas — pero eso es una
    reescritura de produccion, no una promocion, y va en su propio commit. -/

def substfcT (v s f : Term) : Term :=
  funcc (strCode "substfc") (cons v (cons s (cons f nil)))

theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

theorem prf_substtc_funcc3 (v W sc x y z : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) (cons (substtc v W z) nil)))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_substtsc_cons v W z nil)
                (prf_congr_cons_tail (prf_substtsc_nil v W))))))))

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))

/-- **EL LEMA GENERICO** que subsume las ocho copias. -/
theorem pcc_congr_hole_code (F : Term → Term) (X Y : Term)
    (hinv : ∀ W, Prf (substtc zero W (F X) =eq F X))
    (hhole : ∀ w, Prf (substtc zero w (F (varc (numeral 0))) =eq F w)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (F X) (F Y))) := by
  let Ac : Term := eqc (F X) (F (varc (numeral 0)))
  have hcomp : ∀ w : Term, Prf (substfc zero w Ac =eq eqc (F X) (F w)) := by
    intro w
    refine prf_eq_trans (prf_substfc_eq zero w (F X) (F (varc (numeral 0)))) ?_
    exact prf_congr_eqCodeFn (hinv w) (hhole w)
  have hAX : Prf (provFromCode (substfc zero X Ac)) :=
    prf_mp (prf_provCode_congr (prf_eq_symm (hcomp X)))
      (prf_provFromCode_eqCodeFn_refl (F X))
  refine prf_deduction ?_
  exact PrfH.mp _ _ _ (prf_to_prfH (prf_provCode_congr (hcomp Y)) _)
    (PrfH_leibniz_apply Ac X Y (prfH_hyp_self _) (prf_to_prfH hAX _))

/-- **CONTROL** — el enunciado LITERAL de `SFPlanos.pcc_congr_substfcT_arg3_code`, derivado
    del generico en tres lineas en vez de las doce del sondeo. -/
theorem CTRL_pcc_congr_substfcT_arg3_code_desde_hole (A B X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hB : ∀ W, Prf (substtc zero W B =eq B))
    (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (substfcT A B X) (substfcT A B Y))) :=
  pcc_congr_hole_code (fun s => substfcT A B s) X Y
    (substtc_inv_substfcT hA hB hX)
    (fun w => prf_eq_trans (prf_substtc_substfcT zero w A B (varc (numeral 0)))
      (prf_congr_substfcT (hA w) (hB w) (prf_substtc_varc0 w)))

/-- **CONTROL** — y las de produccion que SI se pueden nombrar aqui salen igual. Se toma
    `pcc_congr_binT_2_code` con el `binT` REAL: mismo enunciado, otra prueba. -/
theorem CTRL_pcc_congr_binT_2_code_desde_hole (m : Nat) (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m A X) (binT m A Y))) :=
  pcc_congr_hole_code (fun s => binT m A s) X Y
    (substtc_inv_binT hA hX)
    (fun w => prf_eq_trans (prf_substtc_binT m w A (varc (numeral 0)))
      (prf_congr_binT (hA w) (prf_substtc_varc0 w)))

/-- Y la de produccion prueba lo mismo: `Prf : Formula → Prop`, luego son la misma
    proposicion y el cambio es net-0. -/
example (m : Nat) (A X Y : Term)
    (hA : ∀ W, Prf (substtc zero W A =eq A)) (hX : ∀ W, Prf (substtc zero W X =eq X)) :
    Prf (provFromCode (eqc X Y) ⇒ provFromCode (eqc (binT m A X) (binT m A Y))) :=
  pcc_congr_binT_2_code m A X Y hA hX

/-! ## §3 · LOS CINCO DUPLICADOS EXACTOS POR NOMBRE — NO PROMOVER, BORRAR DEL SONDEO

    | del sondeo | ya en | promovido en |
    |---|---|---|
    | `prf_substtc_termCode_closed`   | `Meta/LiftcCodePrf.lean` | B1 |
    | `prf_substtc_termCode_numeralM` | `Meta/LiftcCodePrf.lean` | B1 |
    | `prf_substtc_termCode_zero`     | `Meta/LiftcCodePrf.lean` | B1 |
    | `pcc_thm_inst4`                 | `Meta/MpCodePrf.lean` §N+1 | **2026-08-31, DESDE ESTE MISMO SONDEO** |
    | `pcc_axiom_inst4`               | `Meta/MpCodePrf.lean` §N+1 | **2026-08-31, DESDE ESTE MISMO SONDEO** |

    Los cinco son identicos al byte (md5 del texto de la declaracion). Los cinco estan en el
    `export` de su modulo, o sea accesibles a nivel raiz.

    ⚠️ **El docstring del sondeo MIENTE**: dice «`pcc_thm_inst4` / `pcc_axiom_inst4` — no
    existian en produccion (solo hasta `inst3`)». Es falso desde el 2026-08-31; el propio
    `Meta/MpCodePrf.lean` §N+1 dice «promovido de `sondeos/SubstfcPlanos.lean`». Al promover
    hay que corregir esa frase o se propaga al libro.

    La comprobacion de que borrarlos es drop-in **bajo los `open` del sondeo** esta en
    `Probe/B3_planos_dedup_opens.lean`, que es el unico de los cuatro arneses donde se puede
    hacer entera: los tres `prf_substtc_termCode_*` los DECLARA `LiftcCodePrf`, y este fichero
    importa exactamente lo que `LiftcCodePrf` importa, o sea que aqui NO son visibles (por eso
    §1.0 los redeclara con prefijo `L_`). Los dos de `MpCodePrf` si llegan, y se recompilan. -/

example (φ : Formula) (h : Prf (forall_4 φ)) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  pcc_thm_inst4 φ h w₁ w₂ w₃ w₄

example (φ : Formula) (hmem : forall_4 φ ∈ axioms) (w₁ w₂ w₃ w₄ : Term) :
    Prf (provFromCode (substfc zero w₄ (substfc (numeral 1) (liftc zero w₃)
      (substfc (numeral 2) (liftc zero (liftc zero w₂))
        (substfc (numeral 3) (liftc zero (liftc zero (liftc zero w₁))) (formCode φ)))))) :=
  pcc_axiom_inst4 φ hmem w₁ w₂ w₃ w₄

/-! ## §4 · LAS 30 GENUINAMENTE NUEVAS, y donde caen

    Sin homonimo, sin sinonimo y sin orientacion invertida en los 109 modulos de produccion.
    Agrupadas por bloque, con el destino que se ha COMPILADO (o, cuando no, dicho como tal):

    **(a) KIT TERNARIO — 9, destino `Meta/EvalArithPrf.lean`, COMPILADO en
    `Probe/B3_planos_dedup_funcc3.lean` con los imports exactos de ese modulo:**
    `prf_substtc_funcc3` `prf_congr_funcc3` `substfcT` `substfcT_termCode`
    `prf_congr_substfcT` `prf_substtc_substfcT` `substtc_inv_substfcT`
    `liftTerm_substfcT` `substTerm_substfcT`.
    Produccion tiene `prf_substtc_funcc1`/`_funcc2` y para en dos argumentos; `liftcT`/
    `liftscT` son BINARIOS. Nada ternario existe. Este bloque es ademas el COMPARTIDO:
    `sondeos/SubstfcEx.lean` y `sondeos/EvalSubstfcPrf.lean` traen las nueve byte a byte
    (md5 identico), y `sondeos/EvalSubsttc.lean` las dos primeras.

    **(b) `binct` y su familia — 8:** `binct` `binct_implc` `binct_andc` `binct_orc`
    `AXBIN_BODY` `AXBIN_impl` `AXBIN_and` `AXBIN_or`, mas `AXBOT_BODY` `AXBOT_BODY_ok`
    (10 con esos dos). Nuevas, pero ver el arnes de `open`s: **`binct` subsume por `rfl` SEIS
    constructores de `Minimal/Axioms.lean`** (`funcc` tag 1, `atomc` 3, `eqc` 4, `implc` 5,
    `andc` 7, `orc` 8), no los tres que el sondeo puentea. Si se promueve, su sitio es
    `Minimal/Axioms.lean`.
    ⚠️ Convencion: produccion nombra estos cuerpos por el AXIOMA (`LIFTC_FUNC_BODY`,
    `LIFTSC_CONS_BODY`, `AX26_BODY`). `AXBOT_BODY`/`AXBIN_BODY` se salen de ella; los nombres
    de produccion serian `SUBSTFC_BOTTOM_BODY` / `SUBSTFC_BIN_BODY`. No hay colision con
    ningun `_BODY` existente.

    **(c) El frente propiamente dicho — 10:** `evalSubstfcCode` `substTerm_evalSubstfcCode`
    `liftTerm_evalSubstfcCode` `pcc_substfc_bottom_dot` `paso2_caso_bottom`
    `pcc_substfc_bin_dot` `paso2_caso_bin` `paso2_caso_impl` `paso2_caso_and` `paso2_caso_or`.
    ✅ El trio `evalSubstfcCode`/`substTerm_`/`liftTerm_` es el SEXTO miembro de una familia
    que produccion ya tiene con esa convencion exacta —`evalAddCode` (`Meta/EvalArithPrf.lean`),
    `evalMulCode` (`EvalMulPrf`), `evalLencCode` (`EvalListPrf`), `evalNthcCode` (`EvalNthcPrf`),
    `evalPredCode` (`EvalPredPrf`)—, todos `eqCodeFn (⟨ctor⟩T (tcFn …)) (tcFn (⟨op⟩ …))` con sus
    dos companeras probadas por el mismo `simp only`. No hay divergencia de convencion.
    (`targetLift`/`targetLiftsc` de `LiftcCodePrf` son la OTRA moneda —`Formula`, ya envuelta en
    `provFromCode`— y conviven con esta desde B2; no hay que elegir.)
    ⚠️ **Nombres `paso2_caso_*`**: son nombres de SONDEO. No existe ningun `paso2_` en
    produccion; la convencion de ahi seria `pcc_eval_substfc_bottom` etc.
    ⚠️ `paso2_caso_bottom` y `pcc_substfc_bin_dot` difieren de sus gemelos en
    `sondeos/EvalSubstfcPrf.lean` **solo en lineas de comentario** (verificado por diff): son
    la misma prueba, y al promover uno hay que borrar el otro.

    **(d) Fontaneria del `binK` — 4:** `binK` `binK_binT` `prf_congr_binK`
    `prf_substtc_binK_at`. Nuevas, pero las que llevan la SUBSUNCION AL REVES: §1.
    **(e) `pcc_congr_substfcT_arg3_code` — 1**, el casi-duplicado de §2.

    9 + 10 + 10 + 4 + 1 = 34. -/

/-! ## §5 · CONTROLES NEGATIVOS -/

set_option linter.unusedVariables false in
/-- `binK` con etiqueta ABSTRACTA no colapsa a `binT` de ningun tag: la generalidad no es
    cosmetica. -/
example (H a b : Term) : True := by
  fail_if_success exact (rfl : binK H a b = binT 5 a b)
  fail_if_success exact (rfl : binK H a b = binT 7 a b)
  trivial

set_option linter.unusedVariables false in
/-- Y el titular del sondeo NO es una reflexividad disfrazada. -/
example (v s f : Term) : True := by
  fail_if_success exact (rfl : substfcT (tcFn v) (tcFn s) (tcFn f) = tcFn (substfc v s f))
  trivial

/-- El puente `binK`↔`binT` vale SOLO en la etiqueta `termCode (numeralM m)`: no son el mismo
    `def` con dos nombres. -/
example (m : Nat) (a b : Term) : binK (termCode (numeralM m)) a b = binT m a b := rfl

end B3PlanosDedup

/-! ## CONTROL DE FOOTPRINT — todo net-0 (`[propext, Classical.choice, Quot.sound]`). -/

#print axioms B3PlanosDedup.binK_binT
#print axioms B3PlanosDedup.prf_congr_binK
#print axioms B3PlanosDedup.prf_substtc_binK_at
#print axioms B3PlanosDedup.CTRL_prf_substtc_binT_at_desde_binK
#print axioms B3PlanosDedup.CTRL_prf_substtc_funccT_at_desde_binK
#print axioms B3PlanosDedup.CTRL_prf_substtc_binT_zero_desde_binK
#print axioms B3PlanosDedup.CTRL_generalidad_estricta
#print axioms B3PlanosDedup.pcc_congr_hole_code
#print axioms B3PlanosDedup.CTRL_pcc_congr_substfcT_arg3_code_desde_hole
#print axioms B3PlanosDedup.CTRL_pcc_congr_binT_2_code_desde_hole
