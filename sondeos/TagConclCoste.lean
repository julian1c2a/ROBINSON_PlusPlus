import ROBINSON_PlusPlus

/-!
# SONDEO · ¿cuánto cuesta de verdad la causa **(c′)** de `DEUDA_chainNeg`?

**Fecha**: 2026‑09‑21. **Pregunta**: el cierre de (c′) (`stepConcl ≠ f`) va por
`derives_lineWF_neg_of_tag k concl args e (h : tagConcl k args = some e) (hne : ⊢ ¬ concl ≐ e)`,
y `hne` sale de `formCode_ne` **sólo si se identifica `e` como el código de una fórmula**.
Hacen falta, pues, las **21 ecuaciones** `tagConcl k ⟦args⟧ = ⌜concl⌝`. La cotización que yo
mismo había escrito decía «19 ecuaciones que hoy sólo viven como subtérminos anónimos dentro de
un `cases` de 169 líneas». **Esa cotización era una ESTIMACIÓN sin etiqueta.** Esto la mide.

## Resultado

| grupo | tags | coste MEDIDO |
|---|---|---|
| proposicionales y triviales | 0, 2, 8, 12, 14, 17 (muestra de 6) | **`rfl`**, sin más |
| cuantificadores | 9, 10, 11 (muestra de 3) | **tres líneas**, y **net‑0 puras** |

⛔⛔ **Y la parte que cambia el plan**: los tags de cuantificador llevan `substfc`/`liftfc`, que
son **símbolos OBJETO y no reducen** ⇒ `rfl` **falla** (comprobado abajo, en el bloque comentado).
Eso parecía el **muro de `substfc`** (`project_substfc_wall`, «B.3c, 7 tags» — y son exactamente
esos siete: 9, 10, 11, 13, 18, 19, 20).

**No lo es: el muro ya estaba derribado.** `prf_substFormula_arith` y `prf_liftFormula_arith`
(`Meta/ArithPrf.lean:355` y `:443`) son **exactamente** las dos ecuaciones que hacen falta, están
escritas, y son recursiones estructurales sobre la fórmula. Cada tag de cuantificador se cierra
componiéndolas con `prf_congr_bin1`/`prf_congr_bin2`/`prf_congr_un`.

🔑 Van **DIEZ** de «antes de construir, buscar», y ésta es la más cara de las diez: la estimación
que desmiente llevaba un frente entero marcado como «el grueso».
⚠️ **Sin medir todavía**: los tags **13, 18, 19 y 20**. 18 y 20 (`ind`/`listInd`) anidan
`substfc` **dentro** de `liftfc` y son los únicos que no se parecen a los tres de abajo.

## Cómo re‑ejecutarlo

    lake env lean sondeos/TagConclCoste.lean      # desde la raíz de RPP, NUNCA desde FOL/
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.CodeArith
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.HilbertSeq

namespace TagConclCoste

/-! ## 1 · Los proposicionales: `rfl` y nada más -/

example (A B : Formula) :
    tagConcl 0 [formCode A, formCode B] = some (formCode (A ⇒ (B ⇒ A))) := rfl

example (A B : Formula) :
    tagConcl 2 [formCode A, formCode B] = some (formCode (A ⇒ (B ⇒ (Formula.and A B)))) := rfl

example (A : Formula) : tagConcl 8 [formCode A] = some (formCode (Formula.bottom ⇒ A)) := rfl

example (A : Formula) :
    tagConcl 14 [formCode A] = some (formCode (((A ⇒ Formula.bottom) ⇒ Formula.bottom) ⇒ A)) := rfl

/-- ⚠️ Éste lleva `termCode`, no `formCode`, y aun así es `rfl`. -/
example (t : Term) : tagConcl 12 [termCode t] = some (formCode (Formula.eq t t)) := rfl

example (A : Formula) : tagConcl 17 [formCode A] = some (formCode (Formula.forall A)) := rfl

/-! ## 2 · ⛔ Los de cuantificador: `rfl` **FALLA**

    example (A : Formula) (t : Term) :
        tagConcl 9 [formCode A, termCode t]
          = some (formCode (Formula.forall A ⇒ substFormula 0 t A)) := rfl
    -- error: Type mismatch — `substfc` es símbolo OBJETO y NO reduce.

Y ése es el punto: la igualdad que hace falta **no es de Lean, es de la TEORÍA**. Por eso se
enuncia en `Prf` y por eso `prf_substFormula_arith` la resuelve. -/

/-- tag 9 (`q1`) — el que `rfl` no cierra. **Tres líneas.** -/
theorem tagConcl9_code (A : Formula) (t : Term) :
    Prf (implc (forallc (formCode A)) (substfc zero (termCode t) (formCode A))
          =eq formCode (Formula.forall A ⇒ substFormula 0 t A)) := by
  have h := prf_substFormula_arith 0 t A
  simp only [numeral] at h
  exact prf_congr_bin2 h

/-- tag 10 (`q2`) — el espejo del anterior. -/
theorem tagConcl10_code (A : Formula) (t : Term) :
    Prf (implc (substfc zero (termCode t) (formCode A)) (exc (formCode A))
          =eq formCode (substFormula 0 t A ⇒ Formula.ex A)) := by
  have h := prf_substFormula_arith 0 t A
  simp only [numeral] at h
  exact prf_congr_bin1 h

/-- tag 11 (`q3`) — éste lleva `liftfc`, no `substfc`, y sale igual de barato. -/
theorem tagConcl11_code (A B : Formula) :
    Prf (implc (forallc (implc (formCode A) (liftfc zero (formCode B))))
               (implc (exc (formCode A)) (formCode B))
          =eq formCode ((Formula.forall (A ⇒ liftFormula 0 B)) ⇒ (Formula.ex A ⇒ B))) := by
  have h := prf_liftFormula_arith 0 B
  simp only [numeral] at h
  exact prf_congr_bin1 (prf_congr_un (prf_congr_bin2 h))

end TagConclCoste

#print axioms TagConclCoste.tagConcl9_code
#print axioms TagConclCoste.tagConcl10_code
#print axioms TagConclCoste.tagConcl11_code
