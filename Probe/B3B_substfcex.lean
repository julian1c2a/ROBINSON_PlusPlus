/-
# B3B · MEDIDA de `sondeos/SubstfcEx.lean` — el DESCENSO del KIT DE IMAGEN DOTADA.

## QUE MIDE ESTE FICHERO

`sondeos/SubstfcEx.lean` (4590 l., md5 12e621fb0e610ee7a5f2ab89a0302e09, 464
declaraciones repartidas en 350 nombres distintos) tiene 104 nombres que no existen en
produccion. De esos 104, **33 son la REJILLA del kit de imagen dotada**: seis
constructores (`substfcT`, `substtcT`, `substtscT`, `liftcT`, `liftfcT`, `liftscT`) por
ocho filas (`def`, `_termCode`, `prf_congr_`, `prf_substtc_`, `substtc_inv_`,
`prf_liftc_`, `liftTerm_`, `substTerm_`), mas los dos escalones genericos
`prf_liftc_funcc2` / `prf_liftc_funcc3`.

La pregunta de ADR-019 es: ¿esa rejilla necesita un MODULO NUEVO al fondo del arbol, o
BAJA? Este fichero contesta que BAJA HASTA `Meta/EvalArithPrf.lean` — **entera, las 48
casillas**, incluidas las 10 que hoy viven mas abajo, en `Meta/LiftcCodePrf.lean`.

## EL ARNES

Los `import` de este fichero son **EXACTAMENTE los cuatro `import` de
`Meta/EvalArithPrf.lean`** (SubstCodeOpenPrf, MpCodePrf, Sigma1AtomPrf,
NumCodeClosedPrf), y los `open` son los suyos. NO se importa el barrel
`ROBINSON_PlusPlus.Meta`, ni `EvalArithPrf` mismo, ni nada aguas abajo:
**`CodeCtorKit`, `LiftcCodePrf`, `EvalCarcNthcPrf`, `EvalLiftcPrf`, `CodeWitnessPrf` y
`SubstfcCodePrf` NO estan en la clausura transitiva de estos cuatro imports** (medido:
la clausura de `EvalArithPrf` son 60 modulos y ninguno de esos seis esta en ella).
Por tanto, si esto compila, todo lo de aqui cabe DENTRO de `EvalArithPrf`.

§0 reprueba las tres piezas que `EvalArithPrf` ya declara y que aqui no puedo importar
sin ciclo (`prf_substtc_funcc2`, `prf_substtc_funcc3`, `prf_congr_funcc3`): son copias
LITERALES de `Meta/EvalArithPrf.lean` (namespace `ROBINSON_PlusPlus.Meta.EvalArithPrf`)
y estan aqui solo para simular el interior del modulo destino. NO son declaraciones que
se propongan: ya existen.

## LO QUE SE MIDE, CASILLA A CASILLA

*  7 casillas ya en `EvalArithPrf` (la fila entera de `substfcT` salvo `prf_liftc_`)
                                                           -> nada que hacer
* 10 casillas hoy en `LiftcCodePrf` (`liftcT` y `liftscT`, cinco filas cada uno: def,
  `_termCode`, congr, substtc, inv)                        -> **DESCENSO propuesto**
* 31 casillas que faltan: las filas `substtcT`, `substtscT` y `liftfcT` enteras salvo
  su `prf_liftc_` (3 x 7 = 21), mas la fila `prf_liftc_` COMPLETA de los seis (6), mas
  `liftTerm_`/`substTerm_` de `liftcT` y `liftscT` (4)     -> **ALTA en `EvalArithPrf`**
* + 2 escalones genericos `prf_liftc_funcc2` / `prf_liftc_funcc3` -> **ALTA en `EvalArithPrf`**

  7 + 10 + 31 = 48 casillas; 31 + 2 = 33, que son exactamente las 33 de las 104 que
  faltan en produccion y que este fichero cierra.

Todas las pruebas son copias LITERALES: del sondeo, o —para las 10 de `LiftcCodePrf`—
de `Meta/LiftcCodePrf.lean`. No se ha reescrito ni una tactica.

⛔ Ninguna ecuacion de recursion de `substfcT`/`substtcT`/`substtscT`/`liftcT`/`liftfcT`/
`liftscT` se postula: los seis son DEFINICIONES y sus unicos puentes son `:= rfl`.
CERO axiomas de Lean nuevos, CERO `sorry`.

  lake env lean Probe/B3B_substfcex.lean
-/
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.DerivCondPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace B3B

/-! ## §0 · YA EXISTEN EN `EvalArithPrf` — copias literales, solo para simular su interior.
    NO son propuestas. -/

theorem prf_substtc_funcc2 (v W sc x y : Term) :
    Prf (substtc v W (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (substtc v W x) (cons (substtc v W y) nil))) :=
  prf_eq_trans (prf_substtc_func v W sc (cons x (cons y nil)))
    (prf_congr_funcc2
      (prf_eq_trans (prf_substtsc_cons v W x (cons y nil))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_substtsc_cons v W y nil)
            (prf_congr_cons_tail (prf_substtsc_nil v W))))))

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

theorem prf_congr_funcc3 {sc x x' y y' z z' : Term}
    (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) (hz : Prf (z =eq z')) :
    Prf (funcc sc (cons x (cons y (cons z nil)))
      =eq funcc sc (cons x' (cons y' (cons z' nil)))) :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_eq_trans (prf_congr_cons_head hy)
      (prf_congr_cons_tail (prf_congr_cons_head hz)))))

/-! ## §1 · LOS DOS ESCALONES GENERICOS QUE FALTAN — el hueco `prf_liftc_funccN`.
    Produccion tiene `prf_substtc_funcc1/2/3` pero NINGUN `prf_liftc_funccN`.
    Copia literal del sondeo (namespace `Paso2`, §0). -/

theorem prf_liftc_funcc2 (c sc x y : Term) :
    Prf (liftc c (funcc sc (cons x (cons y nil)))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) nil))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y nil)))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y nil))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y nil)
            (prf_congr_cons_tail (prf_liftsc_nil c))))))

theorem prf_liftc_funcc3 (c sc x y z : Term) :
    Prf (liftc c (funcc sc (cons x (cons y (cons z nil))))
      =eq funcc sc (cons (liftc c x) (cons (liftc c y) (cons (liftc c z) nil)))) :=
  prf_eq_trans (prf_liftc_func c sc (cons x (cons y (cons z nil))))
    (prf_congr_funcc2
      (prf_eq_trans (prf_liftsc_cons c x (cons y (cons z nil)))
        (prf_congr_cons_tail
          (prf_eq_trans (prf_liftsc_cons c y (cons z nil))
            (prf_congr_cons_tail
              (prf_eq_trans (prf_liftsc_cons c z nil)
                (prf_congr_cons_tail (prf_liftsc_nil c))))))))

/-! ## §2 · FILA `def` — los SEIS constructores.
    `substfcT` ya esta en `EvalArithPrf`; `liftcT`/`liftscT` estan hoy en `LiftcCodePrf`
    (version de 1084 lineas) — se copian LITERALES para medir que NO necesitan nada de
    `LiftcCodePrf`. `substtcT`/`substtscT`/`liftfcT` son las que faltan. -/

def substfcT  (v s f  : Term) : Term := funcc (strCode "substfc")  (cons v (cons s (cons f nil)))
def substtcT  (v s t  : Term) : Term := funcc (strCode "substtc")  (cons v (cons s (cons t nil)))
def substtscT (v s ts : Term) : Term := funcc (strCode "substtsc") (cons v (cons s (cons ts nil)))
def liftcT    (c t    : Term) : Term := funcc (strCode "liftc")    (cons c (cons t nil))
def liftfcT   (c f    : Term) : Term := funcc (strCode "liftfc")   (cons c (cons f nil))
def liftscT   (c ts   : Term) : Term := funcc (strCode "liftsc")   (cons c (cons ts nil))

/-! ## §3 · FILA `_termCode` — los seis puentes, por `rfl`. NO son ecuaciones postuladas. -/

theorem substfcT_termCode (v s f : Term) :
    substfcT (termCode v) (termCode s) (termCode f) = termCode (substfc v s f) := rfl
theorem substtcT_termCode (v s t : Term) :
    substtcT (termCode v) (termCode s) (termCode t) = termCode (substtc v s t) := rfl
theorem substtscT_termCode (v s ts : Term) :
    substtscT (termCode v) (termCode s) (termCode ts) = termCode (substtsc v s ts) := rfl
theorem liftcT_termCode (c t : Term) :
    liftcT (termCode c) (termCode t) = termCode (liftc c t) := rfl
theorem liftfcT_termCode (c f : Term) :
    liftfcT (termCode c) (termCode f) = termCode (liftfc c f) := rfl
theorem liftscT_termCode (c ts : Term) :
    liftscT (termCode c) (termCode ts) = termCode (liftsc c ts) := rfl

/-! ## §4 · FILA `prf_congr_` -/

theorem prf_congr_substfcT {v v' s s' f f' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (hf : Prf (f =eq f')) :
    Prf (substfcT v s f =eq substfcT v' s' f') := prf_congr_funcc3 hv hs hf
theorem prf_congr_substtcT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtcT v s t =eq substtcT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_substtscT {v v' s s' t t' : Term}
    (hv : Prf (v =eq v')) (hs : Prf (s =eq s')) (ht : Prf (t =eq t')) :
    Prf (substtscT v s t =eq substtscT v' s' t') := prf_congr_funcc3 hv hs ht
theorem prf_congr_liftcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftcT c t =eq liftcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))
theorem prf_congr_liftfcT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftfcT c t =eq liftfcT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))
theorem prf_congr_liftscT {c c' t t' : Term} (hc : Prf (c =eq c')) (ht : Prf (t =eq t')) :
    Prf (liftscT c t =eq liftscT c' t') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hc)
    (prf_congr_cons_tail (prf_congr_cons_head ht)))

/-! ## §5 · FILA `prf_substtc_` — nivel ARBITRARIO -/

theorem prf_substtc_substfcT (v W x y z : Term) :
    Prf (substtc v W (substfcT x y z)
      =eq substfcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substfc") x y z
theorem prf_substtc_substtcT (v W x y z : Term) :
    Prf (substtc v W (substtcT x y z)
      =eq substtcT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtc") x y z
theorem prf_substtc_substtscT (v W x y z : Term) :
    Prf (substtc v W (substtscT x y z)
      =eq substtscT (substtc v W x) (substtc v W y) (substtc v W z)) :=
  prf_substtc_funcc3 v W (strCode "substtsc") x y z
theorem prf_substtc_liftcT (v W x y : Term) :
    Prf (substtc v W (liftcT x y) =eq liftcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftc") x y
theorem prf_substtc_liftfcT (v W x y : Term) :
    Prf (substtc v W (liftfcT x y) =eq liftfcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftfc") x y
theorem prf_substtc_liftscT (v W x y : Term) :
    Prf (substtc v W (liftscT x y) =eq liftscT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "liftsc") x y

/-! ## §6 · FILA `prf_liftc_` — LAS SEIS CASILLAS ESTAN VACIAS EN PRODUCCION.
    Ni siquiera `substfcT`, `liftcT` o `liftscT`, que ya existen, tienen su fila `liftc`. -/

theorem prf_liftc_substfcT (c x y z : Term) :
    Prf (liftc c (substfcT x y z) =eq substfcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substfc") x y z
theorem prf_liftc_substtcT (c x y z : Term) :
    Prf (liftc c (substtcT x y z) =eq substtcT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtc") x y z
theorem prf_liftc_substtscT (c x y z : Term) :
    Prf (liftc c (substtscT x y z) =eq substtscT (liftc c x) (liftc c y) (liftc c z)) :=
  prf_liftc_funcc3 c (strCode "substtsc") x y z
theorem prf_liftc_liftcT (c x y : Term) :
    Prf (liftc c (liftcT x y) =eq liftcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftc") x y
theorem prf_liftc_liftfcT (c x y : Term) :
    Prf (liftc c (liftfcT x y) =eq liftfcT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftfc") x y
theorem prf_liftc_liftscT (c x y : Term) :
    Prf (liftc c (liftscT x y) =eq liftscT (liftc c x) (liftc c y)) :=
  prf_liftc_funcc2 c (strCode "liftsc") x y

/-! ## §7 · FILA `substtc_inv_` — nivel `zero` -/

theorem substtc_inv_substfcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substfcT X Y Z) =eq substfcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substfcT zero W X Y Z) (prf_congr_substfcT (hX W) (hY W) (hZ W))
theorem substtc_inv_substtcT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtcT X Y Z) =eq substtcT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtcT zero W X Y Z) (prf_congr_substtcT (hX W) (hY W) (hZ W))
theorem substtc_inv_substtscT {X Y Z : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y))
    (hZ : ∀ W, Prf (substtc zero W Z =eq Z)) :
    ∀ W, Prf (substtc zero W (substtscT X Y Z) =eq substtscT X Y Z) := fun W =>
  prf_eq_trans (prf_substtc_substtscT zero W X Y Z) (prf_congr_substtscT (hX W) (hY W) (hZ W))
theorem substtc_inv_liftcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftcT X Y) =eq liftcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftcT zero W X Y) (prf_congr_liftcT (hX W) (hY W))
theorem substtc_inv_liftfcT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftfcT X Y) =eq liftfcT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftfcT zero W X Y) (prf_congr_liftfcT (hX W) (hY W))
theorem substtc_inv_liftscT {X Y : Term}
    (hX : ∀ W, Prf (substtc zero W X =eq X)) (hY : ∀ W, Prf (substtc zero W Y =eq Y)) :
    ∀ W, Prf (substtc zero W (liftscT X Y) =eq liftscT X Y) := fun W =>
  prf_eq_trans (prf_substtc_liftscT zero W X Y) (prf_congr_liftscT (hX W) (hY W))

/-! ## §8 · FILAS `liftTerm_` / `substTerm_` — conmutacion META.
    Solo `substfcT` las tiene en produccion; las otras CINCO no. -/

theorem liftTerm_substfcT (k : Nat) (v s f : Term) :
    liftTerm k (substfcT v s f) = substfcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substfcT (k : Nat) (u v s f : Term) :
    substTerm k u (substfcT v s f)
      = substfcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_substtcT (k : Nat) (v s f : Term) :
    liftTerm k (substtcT v s f) = substtcT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substtcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substtcT (k : Nat) (u v s f : Term) :
    substTerm k u (substtcT v s f)
      = substtcT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substtcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_substtscT (k : Nat) (v s f : Term) :
    liftTerm k (substtscT v s f) = substtscT (liftTerm k v) (liftTerm k s) (liftTerm k f) := by
  simp only [substtscT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_substtscT (k : Nat) (u v s f : Term) :
    substTerm k u (substtscT v s f)
      = substtscT (substTerm k u v) (substTerm k u s) (substTerm k u f) := by
  simp only [substtscT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftcT (k : Nat) (c t : Term) :
    liftTerm k (liftcT c t) = liftcT (liftTerm k c) (liftTerm k t) := by
  simp only [liftcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftcT (k : Nat) (u c t : Term) :
    substTerm k u (liftcT c t) = liftcT (substTerm k u c) (substTerm k u t) := by
  simp only [liftcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftfcT (k : Nat) (c t : Term) :
    liftTerm k (liftfcT c t) = liftfcT (liftTerm k c) (liftTerm k t) := by
  simp only [liftfcT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftfcT (k : Nat) (u c t : Term) :
    substTerm k u (liftfcT c t) = liftfcT (substTerm k u c) (substTerm k u t) := by
  simp only [liftfcT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]
theorem liftTerm_liftscT (k : Nat) (c t : Term) :
    liftTerm k (liftscT c t) = liftscT (liftTerm k c) (liftTerm k t) := by
  simp only [liftscT, funcc, cons, nil, zero, succ, liftTerm, liftTerms, liftTerm_strCode]
theorem substTerm_liftscT (k : Nat) (u c t : Term) :
    substTerm k u (liftscT c t) = liftscT (substTerm k u c) (substTerm k u t) := by
  simp only [liftscT, funcc, cons, nil, zero, succ, substTerm, substTerms, substTerm_strCode]

end B3B

/-! ## FOOTPRINT — las casillas que hoy viven en `LiftcCodePrf` y las que faltan,
    todas con la MISMA huella que el resto del frente. -/

#print axioms B3B.prf_liftc_funcc3
#print axioms B3B.prf_liftc_substfcT
#print axioms B3B.substtc_inv_liftcT
#print axioms B3B.substtc_inv_substtcT
#print axioms B3B.prf_substtc_liftfcT
#print axioms B3B.substTerm_liftscT
