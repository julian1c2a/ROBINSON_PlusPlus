# Encargo: poner al día los comentarios de los `.lean` (ADR‑134, 2026‑10‑14)

**Last updated:** 2026-10-14 — registro (ADR‑134): copia tal cual de lo que se produjo ese día; no se actualiza. La marca está para el control `[E]` de `check-doc-sync.bash`, que mira todo `.md` versionado.

Repositorio: `E:/dropbox/github/lean4/ROBINSON_PlusPlus` (RPP). Eres uno de varios agentes que, a la vez y sobre
ficheros DISJUNTOS, corrigen los comentarios y docstrings que un verificador encontró falsos o caducados el
2026‑10‑14. El propietario ordenó: «Arreglar todos los comentarios erróneos o que haya que poner al día».
Tu lista de hallazgos está en tu fichero de grupo; el informe completo del verificador, por si necesitas contexto,
en `scratchpad/suelo/censo_lean_final.md` (misma carpeta padre que este fichero).

## Reglas duras

1. **Sólo comentarios**: `--`, `/- … -/`, `/-- … -/`, `/-! … -/`. Nunca código, nombres, firmas, `import`, `open`,
   atributos ni literales de cadena. Antes de cada edición, comprueba que el texto está DENTRO de un comentario.
2. **No introduzcas `/-` ni `-/`** en el texto nuevo: en Lean los comentarios de bloque se ANIDAN, y un `/-` dentro
   de un comentario abre otro y rompe el fichero entero. Deja emparejados los acentos graves (backticks).
3. **Sólo los ficheros de tu lista.** Ningún `.md` salvo que tu lista lo diga. Ningún otro `.lean`. No toques
   `sondeos/InduccionTitulares.lean` (lo edita el coordinador).
4. **No ejecutes** `lake`, `lean`, `lake env`, `leanchecker` ni `elan`: compila el coordinador al final, y varios
   `lake` a la vez agotan la memoria de la máquina. **Git, sólo de lectura** (`git log`, `git show`, `git blame`,
   `git grep`); nada de `add`, `commit`, `stash`, `restore`, `checkout`, `reset`.
5. **Conserva los finales de línea** del fichero (mira con `file <ruta>`; si es CRLF, el texto nuevo va en CRLF) y la
   codificación UTF‑8.
6. **Cada hallazgo se COMPRUEBA antes de editar**, contra el fuente: grep del nombre en todo el árbol, la firma, los
   usos. El verificador pudo equivocarse. Si al comprobarlo el hallazgo es falso, NO edites y repórtalo RECHAZADO
   con la evidencia. Los números de línea son del árbol de las 15:10 y pueden haberse movido unas líneas: localiza el
   texto por su contenido.
7. **Ninguna cifra ni afirmación nueva sin medirla.** «Nadie lo usa» exige un grep en `ROBINSON_PlusPlus/`,
   `sondeos/` y, si aplica, `../FOL`. Si no puedes medirla, no la escribas.
8. No escribas el nombre `prf_axiomsCodeT_eq` en texto nuevo (era el antiguo axioma del ancla; hoy no existe).

## Cómo se corrige: el estilo del proyecto

* Español, conciso, con el tono del fichero. Comillas «…». En «ADR‑134» y «2026‑10‑14» el guion es U+2011 (cópialo
  de aquí: ‑). Anchura de línea como la del bloque que tocas (≈ 100–120 columnas). No reformatees lo que no tocas.
* **(A) Fue cierto cuando se escribió y hoy no lo es** (un plan, un «pendiente», un «queda», «nada lo consume», un
  «hoy…» viejo): la historia NO se borra. Se añade junto a la frase, o al final del párrafo, una nota fechada:
  `(✏️ 2026‑10‑14, ADR‑134: <lo que es cierto hoy, con el nombre del teorema y dónde está>)`.
  Si es un bloque entero (una sección de plan, una tabla de pendientes), basta UNA nota en su cabecera:
  `✏️ 2026‑10‑14 (ADR‑134): registro — <el estado de hoy>; lo que sigue describe el de <fecha o ADR>.`
  Si el fichero ya tiene una nota ✏️ que cubre la frase, no añadas otra: amplía la existente si hace falta.
* **(B) Es un error en cualquier fecha** (una fórmula mal escrita, un nombre que nunca existió así, una cuenta mal
  hecha, un puntero `fichero:línea` desplazado): se corrige en el sitio. Si el cambio altera el sentido, añade
  `(✏️ 2026‑10‑14: decía «…»)`; si es un puntero o una errata, sin nota. Para un puntero, mejor citar por SÍMBOLO
  (`` `pcc_eval_add` ``) que por número de línea; si dejas número, compruébalo.
* Un nombre retirado: «`X` (retirado, ADR‑N)» o el nombre vigente que lo sustituye, comprobado con grep.
* Lo mínimo necesario. No reescribas párrafos enteros si basta una nota.

## Hechos de hoy (comprobados por el coordinador el 2026‑10‑14; úsalos, pero comprueba lo que cites)

* **`Prf`** (`Meta/Hilbert.lean:153`) es el cálculo de los titulares: `incl` (los 17 esquemas de `Prfᵢ`, entre ellos
  `thy`, los 142 axiomas de la lista `axioms`), `p3` (DNE), `ind`, `qconf`, `listInd`, `mp`, `gen`. Lo que deriva es
  `T_Prf` (`AXIOMS.md` §0): no es «Q++» ni IΣ₁; por lectura contiene a PA. **«La consistencia de los 142» es
  inexacto**: lo que se prueba es `ConsistentH` (= `¬ Prf ⊥`), la consistencia de `T_Prf` (los 142 CON los esquemas).
* **Gödel I y II, sin hipótesis, desde ADR‑120**: `consistencia : ConsistentH`, `goedel_I : ¬ Prf godelCN`,
  `goedel_II : ¬ Prf consistencyFormula'` (`Meta/Consistencia.lean:50/53/57`). Siguen existiendo las versiones con
  hipótesis, `goedel_first_prf (hcon : ConsistentH)` y `goedel_second_prf (hcon)` (`Meta/GodelTwoPrf.lean:212/222`).
* **Gödel I ENTERO desde ADR‑121**: `goedel_I_neg : ¬ Prf (neg godelCN)` (`Meta/SolidezVerificador.lean:558`), sin
  ω‑consistencia ni Rosser, por la solidez del verificador en el modelo `MNV V₀` (W1); `godelCN_indecidible` (:572)
  es la conjunción. **Tarski**: `tarski`, `tarski_semantico` (`Meta/TarskiPrf.lean:94/131`). **Rosser** (⊬R ∧ ⊬¬R
  sólo con la consistencia, para teorías arbitrarias) sigue ⬜ (T01).
* **El modelo**: `MNV V₀` satisface los 142 (`MN_axioms`) y es `Estandar` (`estandar_MN`); `prf_sound`
  (`Meta/SolidezPrf.lean`) da la solidez de `Prf` en todo modelo estándar (ADR‑119/120). Control negativo:
  `control_tc_cons` (`Meta/ModeloCodificacion.lean:391`), el modelo refuta `ax_tc_cons` (ADR‑124).
* **C3 CERRADO el 2026‑09‑10**: `pcc_lineWF_tracked` (`Meta/SubstTreeReflect.lean:1157`), los 21 tags, SIN
  HIPÓTESIS. `pcc_eval_liftfc` existe (`Meta/EvalLiftfcPrf.lean:1241`).
* **D3 PROBADA el 2026‑09‑10**: `d3_prf_real` (`Meta/PremsBdAllPrf.lean:1300`) =
  `d3_prf_of_halves φ hA_lineWFDotAt hB_premsDotAt` (`Meta/D3ChainDotPrf.lean:1148`); el `axiom d3` se retiró.
  D1 = `repr_pos'_prf`, D2 = `d2_prf`.
* **ADR‑132 / T05**: `hI` y `hbI` son REFUTABLES (`sondeos/D3Sigma1Vacuo.lean`, compilado el 2026‑10‑12), así que
  `d3_prf_of_sigma1` (`Meta/ReflectionPrf.lean:80`) y `d3_prf_of_reflect_bounded` (`Meta/Sigma1BoundedPrf.lean:83`)
  son ciertos y VACUOS. En este commit NO se retiran: se marcan en sus docstrings.
* **ADR‑115 (2026‑10‑02)**: la capa `⊢` (`Derives`, `Provable`, `raa`, `MetaRules`, `NegVerifier`, `d3` sobre `⊢`,
  `godelCN_fixedpoint`, `goedel_first_numeral`, `Completeness`…) quedó RETIRADA de RPP.
* **ADR‑113**: `cons a b = σ (pair a b)`; en el modelo, `consN a b := triN (a + b) + b + 1`
  (`Minimal/Axioms.lean:642`). Antes era `cons a b = pair a (σ b)`.
* **ADR‑117/118**: el ancla es el axioma diagonal `ax_axiomsCodeT_def`; `prf_ancla`
  (`Meta/Representability2Prf.lean:157`) es TEOREMA; la clase `AnclaEq` y su instancia se retiraron con ADR‑118.
* **ADR‑012**: `ax_tc_cons` está fuera de la lista `axioms`. **ADR‑027**: `gen` no es la ω‑regla.
* **ADR‑020**: los esquemas de sustitución llevan las guardas DENTRO; varios lemas `prf_lineWF_*` y `pcc_*` piden
  guardas (`hwA`, `hwt`, `hwF`, `hwT`, `hwa`…): no son «para códigos arbitrarios» (mira la firma).
* **ADR‑129 (D7)**: los símbolos de FOL son `List Char` (macro `sym!`); ya no hay `String` en los símbolos.
* `validProofFn` tiene etiquetas de regla **0..20** (`numeralM 18` = `ax_vpf_ind`, 19 = `qconf`, 20 = `listInd`;
  `Minimal/Axioms.lean:1173‑1187`).
* `PrfH_mono` y `PrfH_w1` existen (`Meta/HilbertDeduction.lean:76/96`).
* Cuáles sondeos compilan: `sondeos/pasadas/tabla_adr129.txt` (formato `fichero|rc|segundos|error`; rc 0 = compila;
  medido el 2026‑10‑05). Las decisiones: `DECISIONS.md` (grep `^## ADR-`).

## Lo que entregas (tu último mensaje)

Por cada hallazgo de tu lista: el id, `fichero:línea` (después de editar), ACCIÓN = CORREGIDO | NOTA | RECHAZADO |
OMITIDO (con el motivo), la evidencia (`fichero:línea` del fuente que lo prueba) y el texto nuevo exacto.
Si al leer encuentras OTRA frase falsa o caducada en tus ficheros, corrígela con las mismas reglas y repórtala aparte
como NUEVA. Al final: la lista de ficheros tocados con `git diff --stat` de cada uno, y la comprobación de que el
número de `/-` y de `-/` de cada fichero tocado es el mismo antes y después (cuéntalos antes de empezar con
`grep -o -- '/-' <ruta> | wc -l` y `grep -o -- '-/' <ruta> | wc -l`, y otra vez al acabar).
