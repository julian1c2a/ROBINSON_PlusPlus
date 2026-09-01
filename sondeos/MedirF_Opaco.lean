/- MF_opaco.lean — MEDICION: ¿esta MUERTO el «Bloqueo 2» del PLAN-NEGVERIFIER (2026-07-14)?

   El plan afirma, literalmente (§B del veredicto del sondeo):

     «`axiomsCodeT := Term.func "axiomsCodeT" []` es un atomo totalmente opaco, con SOLO
      direccion positiva (`ax_inAxC`/`prf_inAxC`). NO EXISTE ninguna forma de REFUTAR
      `In v0 axiomsCodeT`. [...] ==> `NegVerifier` NO es demostrable mientras `axiomsCodeT`
      sea opaco.»

   Este fichero MIDE esa afirmacion contra el arbol de HOY. Todo lo de abajo COMPILA.

   RESUMEN DE LO MEDIDO
   --------------------
   §1  El puente `formCode` / `formCodeM` existe (`formCodeM_eq`) y NO es `rfl` (es induccion).
   §2  La cadena del encargo CIERRA, y con la hipotesis META MAS DEBIL (`¬ List.Mem φ axioms`),
       reconstruida aqui DESDE CERO. -> `neg_In_axiomsCodeT_of_notMem`
   §3  Ya estaba en produccion, con hipotesis AUN mas comoda (`¬ Prf φ`):
       `Meta/AxiomListCode.lean:70  neg_In_axiomsCodeT`.
   §4  LA MEDIDA FUERTE: la refutacion NO se limita a codigos de formulas. Para un termino
       ARBITRARIO `x` (invariante por sustitucion) basta distinguirlo puntualmente de los 141
       axiomas. -> `neg_In_axiomsCodeT_gen`.  El atomo NO es opaco en ninguna direccion.
   §5  CASO BASURA CONCRETO, cerrado: `axioms ⊢ ¬ (nil ∈ axiomsCodeT)` — un `x` que NO es
       `formCode` de nada. Esto es exactamente lo que el plan declaraba IMPOSIBLE.
   §6  EL CONSUMIDOR: `derives_lineWF_neg_thy` enchufado. El caso `thy` del modulo C queda
       cerrado (a) para toda φ no demostrable, (b) para toda φ no-axioma, (c) para basura.
   §7  `#print axioms` de todo: footprint = la base sancionada. CERO axiomas nuevos, CERO sorry. -/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.CodeDistinct
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.AxiomListCode
open ROBINSON_PlusPlus.Meta.LineWFCases
open ROBINSON_PlusPlus.Meta.OmegaReflect

namespace MF_opaco

/-! ## §1 · `formCode` vs `formCodeM` — el puente EXISTE y NO es `rfl` -/

/-- El puente esta en produccion: `Meta/Representability.lean:166`. -/
example (φ : Formula) : formCodeM φ = formCode φ := formCodeM_eq φ

/-- Y NO son la misma constante por `rfl`: son DOS definiciones (una en `Minimal/Axioms`, otra en
    `Meta/Provability`) y el puente es una INDUCCION. Lo comprobamos negativamente: si fuese `rfl`
    la prueba de abajo por `formCodeM_eq` seria innecesaria; la afirmacion medida es que el puente
    ES NECESARIO Y ESTA. (No hay residuo: se usa a diario en el arbol.) -/
example (φ : Formula) : listFormCodeM [φ] = cons (formCode φ) nil := by
  simp only [listFormCodeM, formCodeM_eq]

/-! ## §2 · La cadena DEL ENCARGO, reconstruida DESDE CERO

El encargo pedia exactamente esto, con la hipotesis META `¬ List.Mem φ axioms`. Cierra. -/

/-- **LO QUE EL ENCARGO PEDIA CONSTRUIR.** Reconstruido aqui sin usar el `neg_In_axiomsCodeT` del
    arbol: `prf_not_In_listFormCodeM` + transporte Leibniz por el ancla `ax_axiomsCodeT_eq`.
    ⚠️ La Leibniz es `Derives.subst` (nivel `⊢`), y el ancla va SIMETRIZADA
    (`derive_eq_symm`: el ancla dice `axiomsCodeT =eq listFormCodeM axioms`, y sustituimos
    `listFormCodeM axioms |-> axiomsCodeT`, luego hace falta la direccion contraria). -/
theorem neg_In_axiomsCodeT_of_notMem (φ : Formula) (h : ¬ List.Mem φ axioms) :
    axioms ⊢ neg (In (formCode φ) axiomsCodeT) := by
  have key : ∀ t : Term,
      substFormula 0 t (neg (In (formCode φ) (.var 0))) = neg (In (formCode φ) t) := by
    intro t
    rw [← formCodeM_eq φ]
    simp [neg, In, substFormula, substTerm, substTerms, substTerm_formCodeM]
  have hpos : axioms ⊢ substFormula 0 (listFormCodeM axioms) (neg (In (formCode φ) (.var 0))) := by
    rw [key]; exact prf_not_In_listFormCodeM φ axioms h
  have hsub := Derives.subst axioms (listFormCodeM axioms) axiomsCodeT
    (neg (In (formCode φ) (.var 0))) (FOL.derive_eq_symm ax_axiomsCodeT_eq) hpos
  rwa [key] at hsub

/-! ## §3 · Y YA ESTABA EN PRODUCCION, con hipotesis mas comoda -/

/-- `Meta/AxiomListCode.lean:70`. Toma `¬ Prf φ` (no `¬ List.Mem`), que es EXACTAMENTE la hipotesis
    que `NegVerifier` tiene disponible. Es decir: no solo el bloqueo esta muerto — la pieza esta
    montada en la forma que el consumidor necesita. -/
example (φ : Formula) (hnp : ¬ Prf φ) : axioms ⊢ neg (In (formCode φ) axiomsCodeT) :=
  neg_In_axiomsCodeT φ hnp

/-- Coherencia: la version del encargo se deriva de la del arbol (via `prf_ax`), y al reves no
    hace falta. Ambas conviven. -/
example (φ : Formula) (hnp : ¬ Prf φ) : axioms ⊢ neg (In (formCode φ) axiomsCodeT) :=
  neg_In_axiomsCodeT_of_notMem φ (fun hmem => hnp (prf_ax hmem))

/-! ## §4 · LA MEDIDA FUERTE — la refutacion vale para TERMINOS ARBITRARIOS

El plan decia «no existe NINGUNA forma de refutar `In v0 axiomsCodeT`». Falso: el ancla convierte
la pregunta en 141 desigualdades puntuales, y nada obliga a que `x` sea un `formCode`. -/

/-- Negativo GENERICO sobre una lista concreta: si `x` es provablemente distinto de cada elemento,
    la teoria refuta la pertenencia. Generaliza `prf_not_In_listFormCodeM` quitandole el
    `x = formCode φ`. -/
theorem neg_In_listFormCodeM_gen (x : Term) :
    ∀ (L : List Formula), (∀ f, List.Mem f L → axioms ⊢ neg (x =eq formCodeM f)) →
      axioms ⊢ neg (In x (listFormCodeM L))
  | [], _ => by simpa [listFormCodeM] using prf_not_in_nil_D x
  | f :: fs, hne => by
      have hhead : axioms ⊢ neg (x =eq formCodeM f) := hne f (List.mem_cons.mpr (Or.inl rfl))
      have htail : axioms ⊢ neg (In x (listFormCodeM fs)) :=
        neg_In_listFormCodeM_gen x fs (fun g hg => hne g (List.mem_cons.mpr (Or.inr hg)))
      show axioms ⊢ neg (In x (cons (formCodeM f) (listFormCodeM fs)))
      apply raa; intro h_in
      have h_disj := iff_mp (prf_in_cons_iff_D x (formCodeM f) (listFormCodeM fs)) h_in
      apply FOL.MetaRules.or_elim h_disj
      · intro h_eq; exact mp hhead h_eq
      · intro h_in_tail; exact mp htail h_in_tail

/-- **EL ATOMO NO ES OPACO EN NINGUNA DIRECCION.** Para CUALQUIER termino `x` invariante por
    sustitucion (todo codigo cerrado lo es), refutar `x ∈ axiomsCodeT` se reduce a 141
    desigualdades puntuales. Ninguna hipotesis sobre `x` mas alla de eso. -/
theorem neg_In_axiomsCodeT_gen (x : Term)
    (hxs : ∀ (v : Nat) (s : Term), substTerm v s x = x)
    (hne : ∀ f, List.Mem f axioms → axioms ⊢ neg (x =eq formCodeM f)) :
    axioms ⊢ neg (In x axiomsCodeT) := by
  have key : ∀ t : Term, substFormula 0 t (neg (In x (.var 0))) = neg (In x t) := by
    intro t
    simp [neg, In, substFormula, substTerm, substTerms, hxs]
  have hpos : axioms ⊢ substFormula 0 (listFormCodeM axioms) (neg (In x (.var 0))) := by
    rw [key]; exact neg_In_listFormCodeM_gen x axioms hne
  have hsub := Derives.subst axioms (listFormCodeM axioms) axiomsCodeT
    (neg (In x (.var 0))) (FOL.derive_eq_symm ax_axiomsCodeT_eq) hpos
  rwa [key] at hsub

/-! ## §5 · CASO BASURA CONCRETO — `nil` NO es un axioma, y la teoria LO SABE

Esto es lo que el plan declaraba imposible: refutar `In x axiomsCodeT` para un `x` que no es
`formCode` de ninguna formula. Se cierra sin nada nuevo: todo `formCode` es un `cons`, y
`nil_ne_cons` (nivel ⊢, `Meta/CodeDistinct.lean:67`) hace el resto. -/

/-- META: todo codigo de formula es un `cons` (los 8 constructores llevan tag). -/
theorem formCode_is_cons (f : Formula) : ∃ h t, formCode f = cons h t := by
  cases f with
  | bottom      => exact ⟨_, _, rfl⟩
  | atom _ _    => exact ⟨_, _, rfl⟩
  | eq _ _      => exact ⟨_, _, rfl⟩
  | impl _ _    => exact ⟨_, _, rfl⟩
  | «forall» _  => exact ⟨_, _, rfl⟩
  | and _ _     => exact ⟨_, _, rfl⟩
  | or _ _      => exact ⟨_, _, rfl⟩
  | ex _        => exact ⟨_, _, rfl⟩

/-- `nil` es provablemente distinto del codigo de CUALQUIER formula. -/
theorem neg_nil_eq_formCodeM (f : Formula) : axioms ⊢ neg (nil =eq formCodeM f) := by
  rw [formCodeM_eq]
  obtain ⟨h, t, he⟩ := formCode_is_cons f
  rw [he]
  exact ROBINSON_PlusPlus.Meta.CodeDistinct.nil_ne_cons h t

/-- **LA REFUTACION QUE EL PLAN DECLARABA IMPOSIBLE.** -/
theorem neg_In_nil_axiomsCodeT : axioms ⊢ neg (In nil axiomsCodeT) :=
  neg_In_axiomsCodeT_gen nil (fun _ _ => rfl) (fun f _ => neg_nil_eq_formCodeM f)

/-! ## §6 · EL CONSUMIDOR — el caso `thy` del modulo C, CERRADO

`derives_lineWF_neg_thy` (`Meta/LineWFCases.lean:216`) pedia exactamente esta hipotesis. -/

/-- (a) Linea `thy` con conclusion NO DEMOSTRABLE: REFUTADA. (Ya montado en el arbol como
    `derives_lineWF_neg_thy_of_not_prf`; se reproduce aqui via el consumidor para medir que
    el enchufe es directo.) -/
theorem thy_refutada_no_demostrable (φ : Formula) (hnp : ¬ Prf φ) :
    axioms ⊢ neg (lineWF (cons (formCode φ) (cons (numeralM 15) nil))) :=
  derives_lineWF_neg_thy (formCode φ) (neg_In_axiomsCodeT φ hnp)

/-- (b) Linea `thy` con conclusion que simplemente NO ES AXIOMA (hipotesis meta mas debil).
    Esto responde al punto 1 del encargo: para φ indemostrable pero NO-axioma, BASTA. -/
theorem thy_refutada_no_axioma (φ : Formula) (h : ¬ List.Mem φ axioms) :
    axioms ⊢ neg (lineWF (cons (formCode φ) (cons (numeralM 15) nil))) :=
  derives_lineWF_neg_thy (formCode φ) (neg_In_axiomsCodeT_of_notMem φ h)

/-- (c) Linea `thy` con conclusion BASURA (`nil`, que no codifica nada): REFUTADA.
    Es el caso que el modulo D necesita para cadenas basura. -/
theorem thy_refutada_basura :
    axioms ⊢ neg (lineWF (cons nil (cons (numeralM 15) nil))) :=
  derives_lineWF_neg_thy nil neg_In_nil_axiomsCodeT

/-- (d) Y generico: cualquier conclusion distinguible puntualmente de los 141 axiomas. -/
theorem thy_refutada_gen (x : Term)
    (hxs : ∀ (v : Nat) (s : Term), substTerm v s x = x)
    (hne : ∀ f, List.Mem f axioms → axioms ⊢ neg (x =eq formCodeM f)) :
    axioms ⊢ neg (lineWF (cons x (cons (numeralM 15) nil))) :=
  derives_lineWF_neg_thy x (neg_In_axiomsCodeT_gen x hxs hne)

/-! ## §7 · END-TO-END — una INSTANCIA REAL de la conclusion de `NegVerifier`, descargada

No es solo que el atomo sea refutable: la refutacion SUBE por la recursion del verificador hasta
la conclusion literal de `NegVerifier`. Testigo: la cadena de UNA linea `thy` basura. -/

/-- De `⊢ ¬lineWF L` a `⊢ ¬chainOk nil [L]`: recursion `ax_chainOk_cons` + proyecciones de `∧`. -/
theorem neg_chainOk_of_neg_lineWF (L : Term) (h : axioms ⊢ neg (lineWF L)) :
    axioms ⊢ neg (chainOk nil (cons L nil)) := by
  apply raa; intro hch
  have hand : axioms ⊢ land (lineOk nil L) (chainOk (concat nil (cons (carc L) nil)) nil) :=
    iff_mp (prf_to_derives (prf_chainOk_cons nil L nil)) hch
  have hlok : axioms ⊢ lineOk nil L := FOL.MetaRules.and_elim_left hand
  exact mp h (FOL.MetaRules.and_elim_left hlok)

/-- `⊢ ¬A` da `⊢ ¬(A ∧ B)`. -/
theorem neg_land_of_neg_left (A B : Formula) (h : axioms ⊢ neg A) :
    axioms ⊢ neg (land A B) := by
  apply raa; intro hab
  exact mp h (FOL.MetaRules.and_elim_left hab)

/-- El testigo basura ES un `StdChain` (todos sus elementos tienen forma de codigo). -/
theorem stdChain_testigo_basura :
    StdChain [cons nil (cons (numeralM 15) nil)] := by
  intro x hx
  rcases List.mem_cons.mp hx with he | hnil
  · subst he
    exact IsCodeShaped.cons IsCodeShaped.nil
      (IsCodeShaped.cons (IsCodeShaped.numeral 15) IsCodeShaped.nil)
  · cases hnil

/-- **INSTANCIA REAL DE LA CONCLUSION DE `NegVerifier`**, para TODA `φ` (ni siquiera hace falta
    `¬ Prf φ`) sobre este testigo estandar. Es exactamente la forma
    `axioms ⊢ neg (Verifies φ (objList l))` con `StdChain l`. -/
theorem negVerifier_en_testigo_basura (φ : Formula) :
    axioms ⊢ neg (Verifies φ (objList [cons nil (cons (numeralM 15) nil)])) :=
  neg_land_of_neg_left _ _
    (neg_chainOk_of_neg_lineWF _ thy_refutada_basura)

/-- Y con la conclusion `formCode ψ` de una `ψ` no demostrable: mismo cierre. -/
theorem negVerifier_en_testigo_thy_no_demostrable (φ ψ : Formula) (hnp : ¬ Prf ψ) :
    axioms ⊢ neg (Verifies φ (objList [cons (formCode ψ) (cons (numeralM 15) nil)])) :=
  neg_land_of_neg_left _ _
    (neg_chainOk_of_neg_lineWF _ (thy_refutada_no_demostrable ψ hnp))

/-! ## §8 · FOOTPRINT + tamaño real de la obligacion residual -/

-- Cuantas desigualdades puntuales pide `neg_In_axiomsCodeT_gen`: una por axioma objeto.
-- Sale 141: la obligacion residual es FINITA Y ENUMERADA, no un muro.
#eval axioms.length


#print axioms neg_In_axiomsCodeT_of_notMem
#print axioms neg_In_axiomsCodeT
#print axioms neg_In_listFormCodeM_gen
#print axioms neg_In_axiomsCodeT_gen
#print axioms neg_In_nil_axiomsCodeT
#print axioms thy_refutada_no_demostrable
#print axioms thy_refutada_no_axioma
#print axioms thy_refutada_basura
#print axioms thy_refutada_gen
#print axioms derives_lineWF_neg_thy_of_not_prf
#print axioms neg_chainOk_of_neg_lineWF
#print axioms negVerifier_en_testigo_basura
#print axioms negVerifier_en_testigo_thy_no_demostrable

end MF_opaco
