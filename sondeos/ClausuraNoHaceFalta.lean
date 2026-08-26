/-
# ¿HACE FALTA LA CLAUSURA DEL TESTIGO BAJO SUSTITUCIÓN?

Sondeo de la pregunta más barata del frente `substfc`: ¿alguna parte de la maquinaria de
`lineWF` / `premsOf` / `lineOk` / `chainOk` exige buena‑formación del RESULTADO de un
`substfc`/`liftfc`?

    lake env lean Probe/HaceFaltaClausura.lean

RESPUESTA MEDIDA (todo lo de abajo compila):

* §1 — La CADENA nunca pide buena‑formación de una conclusión. Todo lo que hace con la
  conclusión de una línea anterior es MEMBRESÍA (`In`), nunca un predicado de forma.
* §2 — Las dos reglas que CONSUMEN conclusiones anteriores (`mp`, `gen`) ya están cerradas en
  producción, y sus reflectores se instancian sin problema en una línea cuya casilla es
  literalmente un `substfc`. Compilado abajo. ⟹ no hay clausura aguas abajo.
* §3 — PERO hay DOS sitios donde el 3er argumento de `substfc`/`liftfc` NO es una casilla sino
  el RESULTADO de otro `liftfc`: `ax_lineWF_ind` y `ax_lineWF_listInd`. Ahí, y sólo ahí, la
  evaluación provable pide buena‑formación de un resultado.
* §4 — La salida barata: en esos dos sitios el valor anidado ES un `formCode` (puente
  `prf_liftFormula_arith`, ya en producción), así que el ENCODER puede descargar un conjunto
  extra `isFormCode (liftfc …)` sin ningún teorema de clausura.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf

namespace HaceFaltaClausura

/-! ## §1 · La cadena sólo hace MEMBRESÍA con las conclusiones anteriores

Cada `rfl` de abajo es un censo de forma: exhibe el enunciado LITERAL del `def` de producción.
Si alguno llevara un predicado de buena‑formación sobre `carc`, el `rfl` no cerraría con este
lado derecho. -/

/-- `lineOk` = bien‑formación de la línea ∧ premisas en contexto. Sin predicado de forma. -/
theorem lineOk_shape (c line : Term) :
    lineOk c line = land (lineWF line) (allIn c (premsOf line)) := rfl

/-- `allIn` recurre con `In`: pertenencia pura. -/
theorem allIn_cons_shape : ax_allIn_cons =
    forall_3 (allIn (.var 2) (cons (.var 1) (.var 0)) ⇔
      land (In (.var 1) (.var 2)) (allIn (.var 2) (.var 0))) := rfl

/-- `chainOk` acumula `carc line` en el contexto con `concat`; no lo somete a ningún predicado. -/
theorem chainOk_cons_shape : ax_chainOk_cons =
    forall_3 (chainOk (.var 2) (cons (.var 1) (.var 0)) ⇔
      land (lineOk (.var 2) (.var 1))
        (chainOk (concat (.var 2) (cons (carc (.var 1)) nil)) (.var 0))) := rfl

/-- Las 7 reglas de sustitución no aportan premisas: su conclusión entra al acumulador y nadie
    vuelve a mirarla salvo por `In`. -/
theorem premsOf_q1_nil : ax_premsOf_q1 =
    forall_3 (premsOf (cons (.var 2) (cons (numeralM 9) (cons (.var 1) (cons (.var 0) nil))))
      =eq nil) := rfl
theorem premsOf_ind_nil : ax_premsOf_ind =
    forall_2 (premsOf (cons (.var 1) (cons (numeralM 18) (cons (.var 0) nil))) =eq nil) := rfl
theorem premsOf_listInd_nil : ax_premsOf_listInd =
    forall_2 (premsOf (cons (.var 1) (cons (numeralM 20) (cons (.var 0) nil))) =eq nil) := rfl

/-- `mp` — la regla que consume DOS conclusiones anteriores. Su `lineWF` es SÓLO la longitud:
    ninguna condición sobre la forma de las premisas ni de la conclusión. -/
theorem lineWF_mp_shape : ax_lineWF_mp =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 16)
      (lineWF (.var 0) ⇔ (lenc (.var 0) =eq numeralM 3))) := rfl

/-- `premsOf` de `mp`: las premisas se exigen por `In` (vía `allIn`), no por buena‑formación. -/
theorem premsOf_mp_shape : ax_premsOf_mp =
    forall_2 (premsOf (cons (.var 1) (cons (numeralM 16) (cons (.var 0) nil))) =eq
      cons (implc (.var 0) (.var 1)) (cons (.var 0) nil)) := rfl

/-- `gen` — la otra regla que consume una conclusión anterior. La condición es una ECUACIÓN
    (`carc = forallc casilla`), no un predicado de forma. -/
theorem lineWF_gen_shape : ax_lineWF_gen =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 17)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 3)
        ((carc (.var 0)) =eq forallc (nthc (.var 0) (numeralM 2))))) := rfl

/-- `thy` — el único `lineWF` con un átomo no ecuacional sobre la conclusión, y es `In`
    (pertenencia a la lista de axiomas), no buena‑formación. -/
theorem lineWF_thy_shape : ax_lineWF_thy =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 15)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 2)
        (In (carc (.var 0)) axiomsCodeT))) := rfl

/-! ## §2 · PRUEBA POSITIVA: los consumidores de conclusiones ya están cerrados

`gen` y `mp` son las dos únicas reglas cuya casilla/premisa puede ser la conclusión de una línea
`q1` (y por tanto contener un `substfc`). Sus reflectores punteados **ya existen en producción**.
Se instancian aquí en líneas cuya casilla es LITERALMENTE un `substfc` sobre argumentos
abstractos: si la maquinaria pidiera clausura, esto no tiparía. -/

/-- Línea `gen` cuya premisa es la conclusión de una `q1`: `⟨∀(A[t]), 17, A[t]⟩`. -/
def lineaGenSobreSubstfc (v s f : Term) : Term :=
  cons (forallc (substfc v s f)) (cons (numeralM 17) (cons (substfc v s f) nil))

/-- ✅ El reflector de `gen` se instancia sin pedir NADA sobre `substfc v s f`. -/
theorem gen_no_pide_bf (v s f : Term) :
    Prf (lineWF (lineaGenSobreSubstfc v s f) ⇒
      ((nthc (lineaGenSobreSubstfc v s f) (succ zero) =eq numeralM 17) ⇒
        provFromCode (lineWFCodeFn (tcFn (lineaGenSobreSubstfc v s f))))) :=
  pcc_lineWF_tracked_gen_imp _

/-- Línea `mp` cuyas dos premisas son conclusiones con `substfc` dentro. -/
def lineaMpSobreSubstfc (v s f g : Term) : Term :=
  cons (substfc v s g) (cons (numeralM 16) (cons (substfc v s f) nil))

/-- ✅ Idem para `mp`. -/
theorem mp_no_pide_bf (v s f g : Term) :
    Prf (lineWF (lineaMpSobreSubstfc v s f g) ⇒
      ((nthc (lineaMpSobreSubstfc v s f g) (succ zero) =eq numeralM 16) ⇒
        provFromCode (lineWFCodeFn (tcFn (lineaMpSobreSubstfc v s f g))))) :=
  pcc_lineWF_tracked_mp_imp _

/-- ✅ Y `thy`: su condición `In (carc X) axiomsCodeT` tampoco pide forma. -/
theorem thy_no_pide_bf (v s f : Term) :
    Prf (lineWF (cons (substfc v s f) (cons (numeralM 15) nil)) ⇒
      ((nthc (cons (substfc v s f) (cons (numeralM 15) nil)) (succ zero) =eq numeralM 15) ⇒
        provFromCode (lineWFCodeFn (tcFn (cons (substfc v s f) (cons (numeralM 15) nil)))))) :=
  pcc_lineWF_tracked_thy_imp _

/-! ## §3 · DÓNDE SÍ: el argumento anidado de `ind` y `listInd`

En 5 de los 7 esquemas el 3er argumento de `substfc` (y el 2º de `liftfc`) es una CASILLA
`nthc #0 i`, cuya buena‑formación la da directamente la enmienda. En `ind` y `listInd` NO: es el
resultado de otro `liftfc`. Los `rfl` de abajo lo exhiben. -/

/-! ### Los 5 planos (argumento = casilla) -/

/-- `q1`: `substfc 0 (nthc #0 3) (nthc #0 2)` — 3er argumento = casilla. -/
theorem q1_arg_es_casilla : ax_lineWF_q1 =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 9)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 4)
        ((carc (.var 0)) =eq implc (forallc (nthc (.var 0) (numeralM 2)))
          (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2)))))) := rfl

/-- `q2`: idem. -/
theorem q2_arg_es_casilla : ax_lineWF_q2 =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 10)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 4)
        ((carc (.var 0)) =eq
          implc (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2)))
            (exc (nthc (.var 0) (numeralM 2)))))) := rfl

/-- `q3`: `liftfc 0 (nthc #0 3)` — 2º argumento = casilla. -/
theorem q3_arg_es_casilla : ax_lineWF_q3 =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 11)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 4)
        ((carc (.var 0)) =eq
          implc (forallc (implc (nthc (.var 0) (numeralM 2))
                   (liftfc zero (nthc (.var 0) (numeralM 3)))))
            (implc (exc (nthc (.var 0) (numeralM 2))) (nthc (.var 0) (numeralM 3)))))) := rfl

/-- `leibniz`: DOS `substfc`, ambos sobre la misma casilla. -/
theorem leibniz_arg_es_casilla : ax_lineWF_leibniz =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 13)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 5)
        ((carc (.var 0)) =eq
          implc (eqc (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 4)))
            (implc (substfc zero (nthc (.var 0) (numeralM 3)) (nthc (.var 0) (numeralM 2)))
                   (substfc zero (nthc (.var 0) (numeralM 4)) (nthc (.var 0) (numeralM 2))))))) :=
  rfl

/-- `qconf`: `liftfc 0 (nthc #0 2)` — 2º argumento = casilla. -/
theorem qconf_arg_es_casilla : ax_lineWF_qconf =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 19)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 4)
        ((carc (.var 0)) =eq
          implc (forallc (implc (liftfc zero (nthc (.var 0) (numeralM 2)))
                                (nthc (.var 0) (numeralM 3))))
            (implc (nthc (.var 0) (numeralM 2)) (forallc (nthc (.var 0) (numeralM 3))))))) := rfl

/-! ### Los 2 anidados — AQUÍ y SÓLO AQUÍ aparece la clausura -/

/-- El 3er argumento del `substfc` del paso de `ind`. **No es una casilla**: es un `liftfc`. -/
def indArgAnidado : Term := liftfc (succ zero) (nthc (.var 0) (numeralM 2))

/-- ⚠️ `ax_lineWF_ind` (`Minimal/Axioms.lean:1143‑1145`) aplica `substfc` al RESULTADO de un
    `liftfc`. Para evaluarlo con `pcc_eval_substfc` haría falta la buena‑formación de
    `indArgAnidado`, que NO es ninguna casilla de la línea. -/
theorem ind_anida_liftfc : ax_lineWF_ind =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 18)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 3)
        ((carc (.var 0)) =eq
          implc (substfc zero (termCodeM zero) (nthc (.var 0) (numeralM 2)))
            (implc (forallc (implc (nthc (.var 0) (numeralM 2))
                      (substfc zero (termCodeM (succ (.var 0))) indArgAnidado)))
                   (forallc (nthc (.var 0) (numeralM 2))))))) := rfl

/-- El argumento anidado de `listInd`: DOS `liftfc` encadenados. -/
def listIndArgAnidado1 : Term := liftfc (succ zero) (nthc (.var 0) (numeralM 2))
def listIndArgAnidado2 : Term := liftfc (succ (succ zero)) listIndArgAnidado1

/-- ⚠️ `ax_lineWF_listInd` (`Minimal/Axioms.lean:1155‑1157`): `liftfc` sobre el resultado de
    `liftfc`, y `substfc` sobre el resultado de eso. Dos niveles de clausura. -/
theorem listInd_anida_liftfc : ax_lineWF_listInd =
    forall_ (Formula.impl (nthc (.var 0) (succ zero) =eq numeralM 20)
      (lineWF (.var 0) ⇔ Formula.and (lenc (.var 0) =eq numeralM 3)
        ((carc (.var 0)) =eq
          implc (substfc zero (termCodeM nil) (nthc (.var 0) (numeralM 2)))
            (implc (forallc (forallc (implc listIndArgAnidado1
                      (substfc zero (termCodeM (cons (.var 1) (.var 0))) listIndArgAnidado2))))
                   (forallc (nthc (.var 0) (numeralM 2))))))) := rfl

/-! ## §4 · LA SALIDA: el valor anidado ES un `formCode`

En la dirección del ENCODER la casilla `nthc L 2` vale `formCode A` para una fórmula META `A`.
Entonces el argumento anidado vale `formCode (liftFormula 1 A)` — otra vez un código de fórmula
REAL, con testigo por la vía (2). Es decir: si la enmienda añade el conjunto extra
`isFormCode (liftfc 1 (nthc L 2))`, el encoder lo descarga con el puente de abajo, **sin ningún
teorema de clausura y sin mapear ningún testigo**. -/

/-- El anidado de `ind` es un `formCode`. (Es `prf_liftFormula_arith`, ya en producción.) -/
theorem anidado_ind_es_formCode (A : Formula) :
    Prf (liftfc (numeral 1) (formCode A) =eq formCode (liftFormula 1 A)) :=
  prf_liftFormula_arith 1 A

/-- El doble anidado de `listInd` también. -/
theorem anidado_listInd_es_formCode (A : Formula) :
    Prf (liftfc (numeral 2) (liftfc (numeral 1) (formCode A))
      =eq formCode (liftFormula 2 (liftFormula 1 A))) :=
  prf_eq_trans
    (ROBINSON_PlusPlus.Meta.ArithPrf.prf_congr_liftfc_arg2 (prf_liftFormula_arith 1 A))
    (prf_liftFormula_arith 2 (liftFormula 1 A))

/-- Y el `substfc` exterior sobre ese anidado, cerrado hasta `formCode`: el encoder nunca ve un
    `substfc`/`liftfc` sin evaluar. -/
theorem paso_ind_es_formCode (A : Formula) :
    Prf (substfc (numeral 0) (termCode (succ (.var 0))) (liftfc (numeral 1) (formCode A))
      =eq formCode (substFormula 0 (succ (.var 0)) (liftFormula 1 A))) :=
  prf_eq_trans (prf_congr_substfc_arg3 (prf_liftFormula_arith 1 A))
    (prf_substFormula_arith 0 (succ (.var 0)) (liftFormula 1 A))

/-! ## §5 · EL SITIO DE VERDAD: los dos casos con BINDER de `substfc`

Los §3‑§4 son el hallazgo superficial. El profundo está **dentro** del propio `pcc_eval_substfc`,
y no depende de qué esquema se enmiende.

`substfc` es la ÚNICA de las cuatro familias de ecuaciones cuyo paso recursivo cambia un
parámetro por una **aplicación de función definida**: bajo `∀`/`∃` el sustituyendo `s` pasa a ser
`liftc 0 s`. En `liftfc`/`liftc`/`substtc`/`substtsc`/`liftsc` el parámetro que cambia es siempre
`succ ·` — un CONSTRUCTOR, que se dota gratis (`pcc_dot_succ`).

Consecuencia: al recorrer `f` dentro de `Prov`, en el caso `forallc` hay que identificar
`liftcT 0̇ ṡ` (código de la EXPRESIÓN, que es lo que produce dotar `ax_substfc_forall`) con
`tcFn (liftc 0 s)` (código del VALOR, que es lo que pide la HI instanciada). Ese puente es
`pcc_eval_liftc`, que exige `isTermCode s`; y a la siguiente profundidad de binder exige
`isTermCode (liftc 0 s)` — es decir, **CLAUSURA de `isTermCode` bajo `liftc`**. -/

/-- ⚠️ `substfc` bajo `∀`: el sustituyendo pasa de `s` a `liftc 0 s` — función DEFINIDA. -/
theorem substfc_forall_cambia_sustituyendo : ax_substfc_forall =
    forall_3 (substfc (.var 2) (.var 1) (forallc (.var 0))
      =eq forallc (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))) := rfl

/-- ⚠️ Idem bajo `∃`. -/
theorem substfc_ex_cambia_sustituyendo : ax_substfc_ex =
    forall_3 (substfc (.var 2) (.var 1) (exc (.var 0))
      =eq exc (substfc (succ (.var 2)) (liftc zero (.var 1)) (.var 0))) := rfl

/-- ✅ CONTRASTE: `liftfc` bajo `∀` sólo cambia el NIVEL, y por un `succ` (constructor). Por eso
    `pcc_eval_liftfc` NO necesita clausura de nada. -/
theorem liftfc_forall_solo_sube_nivel : ax_liftfc_forall =
    forall_2 (liftfc (.var 1) (forallc (.var 0)) =eq forallc (liftfc (succ (.var 1)) (.var 0))) :=
  rfl

/-- ✅ CONTRASTE: `liftfc` bajo `∃`, igual. -/
theorem liftfc_ex_solo_sube_nivel : ax_liftfc_ex =
    forall_2 (liftfc (.var 1) (exc (.var 0)) =eq exc (liftfc (succ (.var 1)) (.var 0))) := rfl

/-- ✅ CONTRASTE: en `liftc` sobre términos el nivel tampoco se anida. -/
theorem liftc_func_no_anida : ax_liftc_func =
    forall_3 (liftc (.var 2) (funcc (.var 1) (.var 0)) =eq funcc (.var 1) (liftsc (.var 2) (.var 0))) :=
  rfl

/-- ✅ CONTRASTE: en `substtc` sobre términos el sustituyendo se pasa INTACTO. -/
theorem substtc_func_pasa_intacto : ax_substtc_func =
    forall_4 (substtc (.var 3) (.var 2) (funcc (.var 1) (.var 0))
      =eq funcc (.var 1) (substtsc (.var 3) (.var 2) (.var 0))) := rfl

/-! ### La buena noticia para la vía del TESTIGO: `liftsc` ES `map liftc`

La objeción «no existe map sobre listas objeto» es demasiado fuerte para la lista de términos:
`liftsc` y `substtsc` son literalmente el map de `liftc`/`substtc` sobre una lista de códigos de
TÉRMINO — y ya son axiomas. La lista‑testigo de la familia de términos (`wT`) es HOMOGÉNEA
(sólo códigos de término), así que su versión levantada es exactamente `liftsc c wT`. -/

theorem liftsc_es_map_liftc : ax_liftsc_cons =
    forall_3 (liftsc (.var 2) (cons (.var 1) (.var 0))
      =eq cons (liftc (.var 2) (.var 1)) (liftsc (.var 2) (.var 0))) := rfl

theorem substtsc_es_map_substtc : ax_substtsc_cons =
    forall_4 (substtsc (.var 3) (.var 2) (cons (.var 1) (.var 0))
      =eq cons (substtc (.var 3) (.var 2) (.var 1)) (substtsc (.var 3) (.var 2) (.var 0))) := rfl

/-! ## §6 · Footprint (y prueba de que el fichero se elabora de verdad) -/

#print axioms gen_no_pide_bf
#print axioms mp_no_pide_bf
#print axioms thy_no_pide_bf
#print axioms ind_anida_liftfc
#print axioms listInd_anida_liftfc
#print axioms anidado_listInd_es_formCode
#print axioms paso_ind_es_formCode

end HaceFaltaClausura
