/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ProofChain

/-!
## META — los 21 esquemas `lineWF`/`premsOf` a nivel `⊢` (Derives)

**Des-duplicación.** Estos 42 enunciados vivían en `Meta/ProofChain.lean`, **probados por segunda vez
desde los mismos axiomas** que sus gemelos `prf_*` de `Meta/ReprPrf.lean`. Aquí pasan a ser lo que
siempre fueron: el **transporte** de la versión finitaria por `prf_to_derives : Prf φ → axioms ⊢ φ`.

Los **enunciados son idénticos** a los de `ProofChain` (extraídos literalmente), así que sus
consumidores —`Representability2` (D1) y `DerivCond` (D2)— sólo cambian un `import`. Se mantiene el
namespace `ProofChain` para que las referencias cualificadas sigan resolviendo.

**Por qué importa:** mantener dos juegos obligaba a pagar dos veces cualquier cambio en los esquemas
(y a mantenerlos en sync a mano). Es justo el precio que la reformulación a accesores (§44) iba a
cobrar — y por eso se hace ANTES.
-/

theorem lineWF_mp (concl premA : Term) :
    axioms ⊢ lineWF (cons concl (cons (numeralM 16) (cons premA nil))) :=
  prf_to_derives (prf_lineWF_mp concl premA)

theorem premsOf_mp (concl premA : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 16) (cons premA nil))) =eq
      cons (implc premA concl) (cons premA nil)) :=
  prf_to_derives (prf_premsOf_mp concl premA)

theorem lineWF_gen (concl body : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 17) (cons body nil))) ⇔
      (concl =eq forallc body)) :=
  prf_to_derives (prf_lineWF_gen concl body)

theorem premsOf_gen (concl body : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 17) (cons body nil))) =eq cons body nil) :=
  prf_to_derives (prf_premsOf_gen concl body)

theorem lineWF_thy (concl : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 15) nil)) ⇔ In concl axiomsCodeT) :=
  prf_to_derives (prf_lineWF_thy concl)

theorem premsOf_thy (concl : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 15) nil)) =eq nil) :=
  prf_to_derives (prf_premsOf_thy concl)

theorem lineWF_p1 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 0) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (implc b a))) :=
  prf_to_derives (prf_lineWF_p1 concl a b)

theorem premsOf_p1 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 0) (cons a (cons b nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_p1 concl a b)

theorem lineWF_p2 (concl a b c : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 1) (cons a (cons b (cons c nil))))) ⇔
      (concl =eq implc (implc a (implc b c)) (implc (implc a b) (implc a c)))) :=
  prf_to_derives (prf_lineWF_p2 concl a b c)

theorem premsOf_p2 (concl a b c : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 1) (cons a (cons b (cons c nil))))) =eq nil) :=
  prf_to_derives (prf_premsOf_p2 concl a b c)

theorem lineWF_c1 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 2) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (implc b (andc a b)))) :=
  prf_to_derives (prf_lineWF_c1 concl a b)

theorem premsOf_c1 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 2) (cons a (cons b nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_c1 concl a b)

theorem lineWF_c2 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 3) (cons a (cons b nil)))) ⇔
      (concl =eq implc (andc a b) a)) :=
  prf_to_derives (prf_lineWF_c2 concl a b)

theorem premsOf_c2 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 3) (cons a (cons b nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_c2 concl a b)

theorem lineWF_c3 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 4) (cons a (cons b nil)))) ⇔
      (concl =eq implc (andc a b) b)) :=
  prf_to_derives (prf_lineWF_c3 concl a b)

theorem premsOf_c3 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 4) (cons a (cons b nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_c3 concl a b)

theorem lineWF_j1 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 5) (cons a (cons b nil)))) ⇔
      (concl =eq implc a (orc a b))) :=
  prf_to_derives (prf_lineWF_j1 concl a b)

theorem premsOf_j1 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 5) (cons a (cons b nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_j1 concl a b)

theorem lineWF_j2 (concl a b : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 6) (cons a (cons b nil)))) ⇔
      (concl =eq implc b (orc a b))) :=
  prf_to_derives (prf_lineWF_j2 concl a b)

theorem premsOf_j2 (concl a b : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 6) (cons a (cons b nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_j2 concl a b)

theorem lineWF_j3 (concl a b c : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 7) (cons a (cons b (cons c nil))))) ⇔
      (concl =eq implc (orc a b) (implc (implc a c) (implc (implc b c) c)))) :=
  prf_to_derives (prf_lineWF_j3 concl a b c)

theorem premsOf_j3 (concl a b c : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 7) (cons a (cons b (cons c nil))))) =eq nil) :=
  prf_to_derives (prf_premsOf_j3 concl a b c)

theorem lineWF_efq (concl a : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 8) (cons a nil))) ⇔ (concl =eq implc botc a)) :=
  prf_to_derives (prf_lineWF_efq concl a)

theorem premsOf_efq (concl a : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 8) (cons a nil))) =eq nil) :=
  prf_to_derives (prf_premsOf_efq concl a)

theorem lineWF_eqrefl (concl t : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 12) (cons t nil))) ⇔ (concl =eq eqc t t)) :=
  prf_to_derives (prf_lineWF_eqrefl concl t)

theorem premsOf_eqrefl (concl t : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 12) (cons t nil))) =eq nil) :=
  prf_to_derives (prf_premsOf_eqrefl concl t)

theorem lineWF_p3 (concl a : Term) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 14) (cons a nil))) ⇔
      (concl =eq implc (implc (implc a botc) botc) a)) :=
  prf_to_derives (prf_lineWF_p3 concl a)

theorem premsOf_p3 (concl a : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 14) (cons a nil))) =eq nil) :=
  prf_to_derives (prf_premsOf_p3 concl a)

theorem lineWF_q1 (concl A t : Term) (hwA : Prf (hasWitF A)) (hwt : Prf (hasWit t)) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 9) (cons A (cons t nil)))) ⇔
      (concl =eq implc (forallc A) (substfc zero t A))) :=
  prf_to_derives (prf_lineWF_q1 concl A t hwA hwt)

theorem premsOf_q1 (concl A t : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 9) (cons A (cons t nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_q1 concl A t)

theorem lineWF_q2 (concl A t : Term) (hwA : Prf (hasWitF A)) (hwt : Prf (hasWit t)) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 10) (cons A (cons t nil)))) ⇔
      (concl =eq implc (substfc zero t A) (exc A))) :=
  prf_to_derives (prf_lineWF_q2 concl A t hwA hwt)

theorem premsOf_q2 (concl A t : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 10) (cons A (cons t nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_q2 concl A t)

theorem lineWF_q3 (concl A B : Term) (hwB : Prf (hasWitF B)) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 11) (cons A (cons B nil)))) ⇔
      (concl =eq implc (forallc (implc A (liftfc zero B))) (implc (exc A) B))) :=
  prf_to_derives (prf_lineWF_q3 concl A B hwB)

theorem premsOf_q3 (concl A B : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 11) (cons A (cons B nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_q3 concl A B)

theorem lineWF_leibniz (concl A t₁ t₂ : Term) (hwA : Prf (hasWitF A))
    (hwt1 : Prf (hasWit t₁)) (hwt2 : Prf (hasWit t₂)) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 13) (cons A (cons t₁ (cons t₂ nil))))) ⇔
      (concl =eq implc (eqc t₁ t₂) (implc (substfc zero t₁ A) (substfc zero t₂ A)))) :=
  prf_to_derives (prf_lineWF_leibniz concl A t₁ t₂ hwA hwt1 hwt2)

theorem premsOf_leibniz (concl A t₁ t₂ : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 13) (cons A (cons t₁ (cons t₂ nil))))) =eq nil) :=
  prf_to_derives (prf_premsOf_leibniz concl A t₁ t₂)

theorem lineWF_ind (concl a : Term) (hwa : Prf (hasWitF a)) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 18) (cons a nil))) ⇔
      (concl =eq implc (substfc zero (termCodeM zero) a)
        (implc (forallc (implc a (substfc zero (termCodeM (succ (.var 0))) (liftfc (succ zero) a))))
               (forallc a)))) :=
  prf_to_derives (prf_lineWF_ind concl a hwa)

theorem premsOf_ind (concl a : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 18) (cons a nil))) =eq nil) :=
  prf_to_derives (prf_premsOf_ind concl a)

theorem lineWF_listInd (concl a : Term) (hwa : Prf (hasWitF a)) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 20) (cons a nil))) ⇔
      (concl =eq implc (substfc zero (termCodeM nil) a)
        (implc (forallc (forallc (implc (liftfc (succ zero) a)
                  (substfc zero (termCodeM (cons (.var 1) (.var 0)))
                    (liftfc (succ (succ zero)) (liftfc (succ zero) a))))))
               (forallc a)))) :=
  prf_to_derives (prf_lineWF_listInd concl a hwa)

theorem premsOf_listInd (concl a : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 20) (cons a nil))) =eq nil) :=
  prf_to_derives (prf_premsOf_listInd concl a)

theorem lineWF_qconf (concl P C : Term) (hwP : Prf (hasWitF P)) :
    axioms ⊢ (lineWF (cons concl (cons (numeralM 19) (cons P (cons C nil)))) ⇔
      (concl =eq implc (forallc (implc (liftfc zero P) C)) (implc P (forallc C)))) :=
  prf_to_derives (prf_lineWF_qconf concl P C hwP)

theorem premsOf_qconf (concl P C : Term) :
    axioms ⊢ (premsOf (cons concl (cons (numeralM 19) (cons P (cons C nil)))) =eq nil) :=
  prf_to_derives (prf_premsOf_qconf concl P C)

end ROBINSON_PlusPlus.Meta.ProofChain
