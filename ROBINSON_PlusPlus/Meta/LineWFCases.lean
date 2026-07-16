/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.LineWFCases

/-!
## META — NIVEL D real (§44): los 21 TAGS de `lineWF`, uniformizados (módulo B de `PLAN-NEGVERIFIER.md`)

Tabla **ejecutable** de los 21 esquemas de línea, indexada por la etiqueta `k`, más los envoltorios
uniformes que despachan a los `prf_lineWF_<tag>`/`prf_premsOf_<tag>` de `Meta/ReprPrf.lean` (que ya
existían, uno por tag). El valor de este módulo es **la uniformización**: permite a sus dos consumidores
hacer un case-split mecánico sobre `k` en vez de escribir 21 casos a mano.

🔗 **COMPARTIDO por los dos frentes** (`PLAN-NEGVERIFIER.md` §5), en direcciones opuestas:
* **D3 / `hC_dot`** (positiva): `lineWF X ⇒ Prov ⌜lineWF Ẋ⌝` — reflejar la ecuación estructural y
  aplicar el bicondicional **codificado** vía `pcc_thm_inst` sobre `ax_lineWF_<tag>`.
* **`NegVerifier` / módulo C** (negativa): `¬lineWF X ⇒ ⊢ ¬lineWF X` — vía `prf_lineWF_inv`
  (`Meta/Sigma1AtomPrf.lean`, da los 21 disyuntos) + refutar la ecuación con la distinción de códigos.

### ⚠️ Los 21 esquemas NO son uniformes: `tagConcl` cubre 19, no 21

Leyendo `Minimal/Axioms.lean`:
* **19 ESTRUCTURALES** (los 18 de esquema **y `gen`**): `lineWF ⟨concl, k, args…⟩ ⇔ (concl =eq <expr>(args))`.
  Éstos son los que `tagConcl` tabula.
* **`thy` (15)**: `lineWF ⟨concl, 15⟩ ⇔ **In concl axiomsCodeT**` — el RHS **no es una ecuación**, es una
  pertenencia ⟹ fuera de `tagConcl` (`none`).
* **`mp` (16)**: `lineWF` es **INCONDICIONAL** (no hay `⇔`); queda ligado por `premsOf` ⟹ fuera de
  `tagConcl` (`none`). Es exactamente lo que el sondeo de solidez constató (`PLAN-NEGVERIFIER.md` §🔬 A).

⚠️ **Ojo al matiz** frente al módulo A: allí los «raros» eran `thy`/`mp`/`gen` (codificación *lossy*);
aquí son **`thy`/`mp`** — `gen` **sí** es estructural. **No es el mismo corte.**

`tagPrems`, en cambio, **sí cubre los 21** (`mp`/`gen` son los únicos con premisas; el resto, `nil`).
-/

/-- Aridad de los argumentos del justif por tag. -/
def tagArity : Nat → Nat
  | 0 => 2 | 1 => 3 | 2 => 2 | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 3
  | 8 => 1 | 9 => 2 | 10 => 2 | 11 => 2 | 12 => 1 | 13 => 3 | 14 => 1
  | 15 => 0 | 16 => 1 | 17 => 1 | 18 => 1 | 19 => 2 | 20 => 1
  | _ => 0

/-- Reconstrucción estructural de la conclusión por tag. `none` para `thy` (15) y `mp` (16),
    cuyos esquemas NO son una ecuación (`In`/incondicional). -/
def tagConcl : Nat → List Term → Option Term
  | 0, [a, b]        => some (implc a (implc b a))
  | 1, [a, b, c]     => some (implc (implc a (implc b c)) (implc (implc a b) (implc a c)))
  | 2, [a, b]        => some (implc a (implc b (andc a b)))
  | 3, [a, b]        => some (implc (andc a b) a)
  | 4, [a, b]        => some (implc (andc a b) b)
  | 5, [a, b]        => some (implc a (orc a b))
  | 6, [a, b]        => some (implc b (orc a b))
  | 7, [a, b, c]     => some (implc (orc a b) (implc (implc a c) (implc (implc b c) c)))
  | 8, [a]           => some (implc botc a)
  | 9, [A, t]        => some (implc (forallc A) (substfc zero t A))
  | 10, [A, t]       => some (implc (substfc zero t A) (exc A))
  | 11, [A, B]       => some (implc (forallc (implc A (liftfc zero B))) (implc (exc A) B))
  | 12, [t]          => some (eqc t t)
  | 13, [A, t₁, t₂]  => some (implc (eqc t₁ t₂) (implc (substfc zero t₁ A) (substfc zero t₂ A)))
  | 14, [a]          => some (implc (implc (implc a botc) botc) a)
  | 17, [body]       => some (forallc body)
  | 18, [a]          => some (implc (substfc zero (termCodeM zero) a)
      (implc (forallc (implc a (substfc zero (termCodeM (succ (.var 0))) (liftfc (succ zero) a))))
             (forallc a)))
  | 19, [P, C]       => some (implc (forallc (implc (liftfc zero P) C)) (implc P (forallc C)))
  | 20, [a]          => some (implc (substfc zero (termCodeM nil) a)
      (implc (forallc (forallc (implc (liftfc (succ zero) a)
                (substfc zero (termCodeM (cons (.var 1) (.var 0)))
                  (liftfc (succ (succ zero)) (liftfc (succ zero) a))))))
             (forallc a)))
  | _, _ => none

/-- **Envoltorio UNIFORME de los 21 esquemas**: despacha a los `prf_lineWF_<tag>` existentes. -/
theorem prf_lineWF_tag (k : Nat) (concl : Term) (args : List Term) (e : Term)
    (h : tagConcl k args = some e) :
    Prf (lineWF (cons concl (cons (numeralM k) (objList args))) ⇔ (concl =eq e)) := by
  unfold tagConcl at h
  split at h
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_p1 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_p2 concl _ _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_c1 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_c2 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_c3 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_j1 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_j2 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_j3 concl _ _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_efq concl _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_q1 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_q2 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_q3 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_eqrefl concl _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_leibniz concl _ _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_p3 concl _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_gen concl _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_ind concl _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_qconf concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_lineWF_listInd concl _
  · simp at h


/-- Premisas de contexto por tag. A diferencia de `tagConcl`, ésta cubre **los 21**:
    `mp` y `gen` son los únicos con premisas; el resto (incl. `thy`) tiene `nil`. -/
def tagPrems : Nat → Term → List Term → Option Term
  | 0, _, [_, _]     => some nil
  | 1, _, [_, _, _]  => some nil
  | 2, _, [_, _]     => some nil
  | 3, _, [_, _]     => some nil
  | 4, _, [_, _]     => some nil
  | 5, _, [_, _]     => some nil
  | 6, _, [_, _]     => some nil
  | 7, _, [_, _, _]  => some nil
  | 8, _, [_]        => some nil
  | 9, _, [_, _]     => some nil
  | 10, _, [_, _]    => some nil
  | 11, _, [_, _]    => some nil
  | 12, _, [_]       => some nil
  | 13, _, [_, _, _] => some nil
  | 14, _, [_]       => some nil
  | 15, _, []        => some nil                                  -- thy
  | 16, concl, [a]   => some (cons (implc a concl) (cons a nil))  -- mp  ← las dos premisas
  | 17, _, [body]    => some (cons body nil)                      -- gen ← la premisa
  | 18, _, [_]       => some nil
  | 19, _, [_, _]    => some nil
  | 20, _, [_]       => some nil
  | _, _, _ => none

/-- **Envoltorio UNIFORME de los 21 `premsOf`**. -/
theorem prf_premsOf_tag (k : Nat) (concl : Term) (args : List Term) (L : Term)
    (h : tagPrems k concl args = some L) :
    Prf (premsOf (cons concl (cons (numeralM k) (objList args))) =eq L) := by
  unfold tagPrems at h
  split at h
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_p1 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_p2 concl _ _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_c1 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_c2 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_c3 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_j1 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_j2 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_j3 concl _ _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_efq concl _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_q1 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_q2 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_q3 concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_eqrefl concl _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_leibniz concl _ _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_p3 concl _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_thy concl
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_mp concl _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_gen concl _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_ind concl _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_qconf concl _ _
  · injection h with h; subst h; simpa only [objList] using prf_premsOf_listInd concl _
  · simp at h

end ROBINSON_PlusPlus.Meta.LineWFCases

export ROBINSON_PlusPlus.Meta.LineWFCases (
  tagArity tagConcl tagPrems prf_lineWF_tag prf_premsOf_tag
)
