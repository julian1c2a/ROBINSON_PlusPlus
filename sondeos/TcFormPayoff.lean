/-
MEDICIÓN de `prf_tc_form` (2026-08-23) — la TERCERA sub-familia de la cuarentena.

`prf_tc_form (φ) : Prf (tcFn (formCode φ) =eq termCode (formCode φ))` era meta-recursión sobre la
estructura CONCRETA de φ. Sus hojas (`prf_tc_numeral`, `prf_tc_zero`) siguen vivas; lo que murió es
el paso recursivo `prf_tc_of_cons`, que es `prf_tc_cons` + congruencia.

## RESULTADO: no es un muro. Dos piezas, y la segunda es la que importa.

1. **El sustituto directo es UNA LÍNEA y net-0**: la vía numeral da el mismo puente con el código
   estático cambiado (`termCode (formCode φ)` ⟶ `termCode (numeral (codeNat φ))`).

2. ⚠️ **Pero el lado derecho NO es negociable.** `inDot φ` está fijado por `D3DottedPrf` —que ya
   está ACTIVO y es net-0— como `substfc 0 (tcFn #0) (formCode (In (formCode φ) (runFn nil #0)))`.
   Ese código **ES el objetivo de D3**: viene de la definición de `provCodeC'`. Cambiarlo no es
   "refundar un enunciado", es cambiar el teorema.

   **La salida**: los dos códigos son los de dos términos objeto **provablemente iguales**
   (`prf_formCode_numeral`), y **D1 dota cualquier teorema `Prf`**. Así que el puente entre las dos
   formas sale DENTRO de `Prov`, gratis:

       repr_pos'_prf (prf_eq_symm (prf_formCode_numeral φ))
         : Prf (provFromCode (eqc ⌜numeral (codeNat φ)⌝ ⌜formCode φ⌝))

   …que es exactamente el `heq` que `pcc_rw` / `pcc_rw_imp` piden.

## ⇒ ESTRATEGIA RECOMENDADA: no tocar las definiciones, convertir en la FRONTERA

Probar por dentro en forma NUMERAL (donde `prf_tc_form_numeral` funciona) y aplicar
`pcc_to_formCode_imp` al final. Así los enunciados públicos de `D3InDotPrf` —`inDot`,
`bddCarcDotAt`, `hI_dot`, `d3_prf_of_chainOkDot`— quedan **intactos**, y `D3DottedPrf` sigue
encajando sin tocarse.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ArithPrf ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

namespace TcFormDev

/-- **El sustituto de `prf_tc_form`.** Misma función, código estático CAMBIADO:
    el lado derecho pasa de `termCode (formCode φ)` a `termCode (numeral (codeNat φ))`. -/
theorem prf_tc_form_numeral (φ : Formula) :
    Prf (tcFn (formCode φ) =eq termCode (numeral (codeNat φ))) :=
  prf_eq_trans (prf_congr_tcFn (prf_formCode_numeral φ)) (prf_tc_numeral (codeNat φ))

/-- Y su variante para `termCode` de término (la que pedía `prf_tc_term`). -/
theorem prf_tc_term_numeral (t : Term) :
    Prf (tcFn (termCode t) =eq termCode (numeral (codeNatTerm t))) :=
  prf_eq_trans (prf_congr_tcFn (prf_termCode_numeral t)) (prf_tc_numeral (codeNatTerm t))

/-- ¿Sobrevive la invariancia `substtc`, que es lo que los consumidores realmente usan? -/
theorem substtc_inv_termCode_numeral (φ : Formula) :
    ∀ W, Prf (substtc zero W (termCode (numeral (codeNat φ)))
              =eq termCode (numeral (codeNat φ))) := fun W =>
  prf_eq_trans (prf_congr_substtc3 (prf_eq_symm (prf_tc_numeral (codeNat φ))))
    (prf_eq_trans (prf_substtc_tcFn W (numeral (codeNat φ))) (prf_tc_numeral (codeNat φ)))

end TcFormDev

#print axioms TcFormDev.prf_tc_form_numeral
#print axioms TcFormDev.substtc_inv_termCode_numeral

/-! ## LA MEDICIÓN QUE IMPORTA

`inDot φ` está **fijado** por `D3DottedPrf` (activo, net‑0): lleva `termCode (formCode φ)`, no
`termCode (numeral (codeNat φ))`. Así que **no vale cambiar el enunciado**: ese código ES el
objetivo de D3.

Pero los dos códigos son los de dos términos objeto **provablemente iguales**
(`prf_formCode_numeral`), y **D1 (`repr_pos'_prf`) dota cualquier teorema `Prf`**. Así que el
puente entre las dos formas debería salir DENTRO de `Prov`, y componerse con `pcc_rw_imp`. -/

namespace TcFormDev2
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

/-- **EL PUENTE**: `⊢ Prov(⌜ formCode φ = numeral (codeNat φ) ⌝)`.
    Es D1 aplicada a `prf_formCode_numeral`. Si esto compila, la vía `prf_tc_form` está abierta. -/
theorem pcc_formCode_numeral (φ : Formula) :
    Prf (provCodeC' (Formula.eq (formCode φ) (numeral (codeNat φ)))) :=
  repr_pos'_prf (prf_formCode_numeral φ)

end TcFormDev2

#print axioms TcFormDev2.pcc_formCode_numeral
#check @TcFormDev2.pcc_formCode_numeral

namespace TcFormDev3
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf ROBINSON_PlusPlus.Meta.DotConsPrf
open ROBINSON_PlusPlus.Meta.CodeNumeralPrf

/-- ¿UNIFICA? `provCodeC' (a =eq b)` debe ser `provFromCode (eqc ⌜a⌝ ⌜b⌝)` para que
    `pcc_rw`/`pcc_rw_imp` lo acepten como `heq`. Si este `example` pasa, encaja. -/
example (φ : Formula) :
    Prf (provFromCode (eqCodeFn (termCode (numeral (codeNat φ))) (termCode (formCode φ)))) :=
  repr_pos'_prf (prf_eq_symm (prf_formCode_numeral φ))

/-- **EL CONVERTIDOR.** De la forma NUMERAL a la forma `formCode`, dentro de `Prov`, en
    cualquier hueco. Es `pcc_rw` con el puente de D1. -/
theorem pcc_to_formCode (φ : Formula) (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s))
    (h : Prf (provFromCode (G (termCode (numeral (codeNat φ)))))) :
    Prf (provFromCode (G (termCode (formCode φ)))) :=
  pcc_rw G hG _ _ (repr_pos'_prf (prf_eq_symm (prf_formCode_numeral φ))) h

/-- Y su forma IMPLICACIÓN, para los sitios que viven en `PrfH`. -/
theorem pcc_to_formCode_imp (φ : Formula) (G : Term → Term)
    (hG : ∀ s : Term, Prf (substfc zero s (G (varc (numeral 0))) =eq G s)) :
    Prf (provFromCode (G (termCode (numeral (codeNat φ))))
       ⇒ provFromCode (G (termCode (formCode φ)))) :=
  pcc_rw_imp G hG _ _ (repr_pos'_prf (prf_eq_symm (prf_formCode_numeral φ)))

end TcFormDev3

#print axioms TcFormDev3.pcc_to_formCode
#print axioms TcFormDev3.pcc_to_formCode_imp
