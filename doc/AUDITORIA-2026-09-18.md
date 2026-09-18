# Auditoría 2026-09-18 — el encargo A1-A5 y los cuatro planes de capa

**Last updated:** 2026-09-18
**Autor**: panel adversarial de 18 agentes (9 informes + 9 refutadores), orquestado en sesión.

> ⚠️ **CÓMO SE LEE ESTE DOCUMENTO.** Cada bloque trae el informe **y su refutación**. Cuando el
> refutador dice `SOBREVIVE=False`, **manda la refutación**, no el informe. Tres de los nueve
> informes fueron tumbados por cifras, y los cuatro planes de capa fueron tumbados enteros.
>
> ⚠️ **Y lo que NO es este documento**: no es una lista de tareas aprobada. Los agentes **miden
> bien y estiman mal** porque no compilan; toda afirmación sobre lo que costará algo es
> **hipótesis** hasta que pase el compilador. Lo que ya se ejecutó de aquí está en ADR-069 y
> ADR-070.
>
> 📐 **Lo que se hizo con esto, el mismo día**: A2 → 14 filas nuevas en `check-footprints`
> (147 → 161). A5 → retirada la cifra falsa «163 módulos / 3 902 declaraciones» del plan.
> Los planes de capa → el orden corregido de ADR-069.
>
> ⬜ **Lo que queda por adjudicar**: A1 (el control `[G.1]`), A3 (el CHANGELOG y el `[E]`
> desarmado en los DOS repos), A4 (fijar el SHA de FOL en la CI), y el resto de los 223 nombres
> de A2.

---

## Parte I · LA AUDITORÍA (A1-A5)

---

### A1 · Cabeceras que afirman una deuda YA PAGADA
**Veredicto del informe:** `CONFIRMADO` · **¿sobrevive a la refutación?** **⛔ NO**

**Resumen:** Barridos los 52 módulos `.lean` de FOL/ y TheoryFramework/ contrastando cada marca de deuda abierta contra los nombres que existen hoy: de las 24 líneas con ⬜ (en 16 ficheros), 20 están OBSOLETAS —la deuda que anuncian ya está pagada—, más 5 afirmaciones falsas sin ⬜; sólo 4 ⬜ siguen siendo ciertas.

#### Cifras

TODO LO SIGUIENTE ES MEDIDO leyendo el árbol (`grep`/`sed`/`git log`), sin ejecutar `lake`.

ALCANCE: 52 módulos `.lean` (`find FOL TheoryFramework -name "*.lean" | wc -l` = 52; FOL/ 40 + FOL/Theorems/ 6 + TheoryFramework/ 6).

MARCA ⬜: 24 líneas en 16 ficheros (`grep -rn "⬜" FOL/ TheoryFramework/ --include=*.lean | wc -l` = 24; `-rl | wc -l` = 16).
  · 20 de 24 OBSOLETAS (deuda ya pagada por un nombre que existe hoy) = 83 %.
  · 4 de 24 vigentes: Craig0:88, Enumeration:77, Lift0:41, SkolemHerbrand0:57.

AFIRMACIONES FALSAS SIN ⬜ (no las caza ningún patrón de marca): 5 — Fresh0:62, HenkinLimit0:74, NDtoLK0:18, NDtoLK0:200, TheoryFramework/Instances/FOL.lean:30.

TOTAL: 25 afirmaciones de deuda abierta que son falsas, repartidas en 16 de los 52 módulos (31 %).

CONTRA-MEDICIÓN DE FECHAS (`git log --format='%h' | grep -n`): en los dos casos comprobables el docstring es ANTERIOR al pago — 6b26b02 (Skolem0, pos. 21) < 83061d6 (SkolemN0, pos. 16); eff5672 (Sequent0/NDtoLK0, pos. 45) < 3af8ac8 (Hauptsatz0, pos. 43). No es que el autor mintiera: es que nadie vuelve a la cabecera cuando el vecino paga.

CIFRA FALSA ADICIONAL, medida: TheoryFramework/Instances/FOL.lean:30 dice «cinco `axiom` de `FOL/Completeness.lean`». `FOL/Completeness.lean` NO EXISTE, y `cuarentena/Completeness.lean` tiene UN `axiom` (`grep -nE "^axiom " cuarentena/Completeness.lean` → una sola línea, :756).

EFICACIA DEL [G] PROPUESTO, medida ejecutándolo en seco sobre el árbol de hoy:
  · [G.1] (objetivo, rompe): 3 roturas — Herbrand0:275 `HerbrandExtraction`, HerbrandBlock0:183 `HerbrandExtractionBlock`, Sequent0:504 `CutElim` — y CERO falsos positivos.
  · [G.2] (aviso): 11 avisos, de los cuales 2 verdaderos (`derives0_soundness` en Derives0:88, `prenex` en Prenex0:58), 1 discutible (`proves_iff_models`) y 8 falsos (Skolem0 cita `shiftEnv`/`updateEnv`/`exBlock`/`subst_exBlock` como cosas que SÍ existen). Por eso [G.2] avisa y no rompe.
  · Cobertura conjunta: 5 de los 25 sitios (20 %) los caza la máquina; los 20 restantes son prosa sin nombre citable y hoy no los caza nada.
Borrador ejecutable: C:/msys64/tmp/claude/e--dropbox-github-lean4-ROBINSON-PlusPlus/85b0df6c-1e14-407d-a9ae-04b9e8841ed5/scratchpad/g2.bash

#### Hallazgos

* **[alta]** Herbrand0 declara H3 abierta: «⛔ No está hecha» — y `herbrand_extraction` está DEMOSTRADO
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Herbrand0.lean:38 «| ⟹ | **demostración ⇒ certificado** (H3) | ⬜ **DEUDA**, enunciada como `Prop`, no postulada |»; :40 «⛔ **La ⟹ es H3 —la eliminación de cortes— y NO está.**»; :268 «/-- ⬜⬜ **LA DEUDA H3 — la extracción del certificado.**» y :271 «⛔ **No está hecha.**». EXISTE HOY: E:/dropbox/github/lean4/FOL/FOL/Hauptsatz0.lean:1227 «theorem herbrand_extraction : HerbrandExtraction :=» (incondicional). También :254 «-- §6 · ⬜ H3, ENUNCIADA — y su CONSUMIDOR»

* **[alta]** Sequent0 anuncia el Hauptsatz como «LA ÚNICA DEUDA QUE QUEDA», tres veces — y `hauptsatz` está probado
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Sequent0.lean:29 «CutElim                -- ⬜ LA ÚNICA DEUDA QUE QUEDA: el Hauptsatz»; :95 «## ⬜ La obligación que queda — enunciada, no postulada»; :100 «⇒ con `CutElim`, H3 y la vía H quedan cerradas»; :503 «/-- ⬜ LA ÚNICA DEUDA QUE QUEDA: el HAUPTSATZ. -/». EXISTE HOY: Hauptsatz0.lean:1208 «theorem hauptsatz : CutAdm := by» y :1224 «theorem cut_elimination : CutElim := cutElim_of hauptsatz». Orden de commits medido: eff5672 (Sequent0) es ANTERIOR a 3af8ac8 (Hauptsatz0)

* **[alta]** Skolem0 dice «⬜ MEDIDO que no existe nada de eso» del prefijo ∀ⁿ — y SkolemN0 lo tiene entero
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Skolem0.lean:84 «## ⬜ Lo que falta: el axioma bajo un PREFIJO de universales»; :90 «⬜ **MEDIDO que no existe nada de eso**: `FOL/Semantics.lean` tiene `shiftEnv`/`updateEnv` y sus conmutaciones, pero **nada iterado `k` veces** ni que reconstruya un entorno desde una lista»; :92 «⬜ ~200 l., riesgo **medio**». EXISTE HOY: SkolemN0.lean:73 «def envPush», :111 «theorem eval_allBlock_envPush», :209 «theorem skolem_conservative_n». Orden medido: 6b26b02 (Skolem0) ANTERIOR a 83061d6 (SkolemN0). ⚠️ Agravante: la falsedad va etiquetada «MEDIDO»

* **[alta]** Derives0 lista TRES cosas «que vienen después» y las TRES están hechas
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Derives0.lean:88 «## ⬜ Lo que viene después (y va en este orden)»; :90 «1. ⚠️⚠️ **`derives0_soundness : Γ ⊢₀ f → Γ ⊨ f`** — el agujero de verdad del repo»; :92 «2. El lema de **renombrado** sobre derivaciones»; :93 «3. Portar `cuarentena/Completeness.lean` a `Derives₀`». EXISTEN HOY: Soundness0.lean:80 «theorem derives0_soundness», Rename.lean:415 «theorem derives0_rename_iff», Canonical0.lean:563 «theorem completeness₀»

* **[alta]** Prenex0 dice que falta la función `prenex` «con su terminación» — y está, y sin terminación
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Prenex0.lean:58 «## ⬜ Lo que falta para la forma normal»; :60 «Falta la **función** `prenex : Formula → Formula` con su terminación y su teorema de corrección»; :62 «⬜ Estimado ~200 l., riesgo medio: lo que cuesta [...] es la **medida de terminación**». EXISTE HOY: PrenexNF0.lean:104 «def prenex», :299 «theorem prenex_iff», :398 «theorem prenex_isPrenex» — y su propia cabecera (PrenexNF0.lean:24) dice «## ⭐⭐ La terminación NO hace falta, y eso era lo que se daba por caro»

* **[alta]** Herbrand0 dice que la versión n-aria «⬜ No hecho, y dicho» — y HerbrandBlock0+BlockExtraction0 la tienen
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Herbrand0.lean:71 «La versión n‑aria es iteración rutinaria pero la aritmética de De Bruijn bajo binders anidados [...] pide su propia capa de lemas. ⬜ No hecho, y dicho.» EXISTE HOY: HerbrandBlock0.lean:183 «def HerbrandExtractionBlock» + BlockExtraction0.lean:503 «theorem herbrand_extraction_block : HerbrandExtractionBlock :=»

* **[alta]** Derives1 y Derives2 anuncian como «lo que sigue faltando para H3» cosas que sus vecinos pagaron
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Derives1.lean:76 «## ⬜ Lo que sigue faltando para H3» + :78 «`subst` — la regla de Leibniz» + :81 «Y después, el Hauptsatz» → Derives2.lean:18 «**`subst` es ADMISIBLE**», :279 «theorem eq_substFormula», :471 «theorem derives1_iff_derives2». E:/dropbox/github/lean4/FOL/FOL/Derives2.lean:85 «## ⬜ Lo que sigue faltando para H3» + :87 «**El Hauptsatz.**» → Hauptsatz0.lean:1208

* **[alta]** Propositional0: «⬜ Y falta lo gordo de la vía H: H3 [...] y H4, la extracción de testigos»
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Propositional0.lean:65 «⬜ Y falta lo gordo de la vía H: **H3**, la eliminación de cortes / normalización, y **H4**, la extracción de testigos.» EXISTEN HOY: Hauptsatz0.lean:1227 «theorem herbrand_extraction» (H3) y :1233 «theorem herbrand {φ : Formula} (hqf : QuantFree φ)» (H4)

* **[alta]** TheoryFramework/Instances/FOL.lean cita un fichero que NO EXISTE y una cifra de axiomas falsa por 5×
  · *Evidencia:* E:/dropbox/github/lean4/FOL/TheoryFramework/Instances/FOL.lean:30 «⚠️ `completeness` existe, pero se apoya en **cinco `axiom`** de `FOL/Completeness.lean`»; :47 «⬜ **`CompleteLogic Formula` tampoco se declara** [...] hay que adjudicar antes si los cinco axiomas de `Completeness.lean` son aceptables». MEDIDO: `FOL/Completeness.lean` no existe (ls: No such file); cuarentena/Completeness.lean tiene UN `axiom` (línea 756, `henkin_extension_lemma`), no cinco; y Canonical0.lean:563 da `completeness₀` con cero axiomas del proyecto. Último toque del fichero: b97ee6d, 2026-09-12

* **[alta]** Rename0 dice «la mitad del testigo fresco sigue abierta» y nombra `abstractConst`, que nunca existió
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Rename.lean:68 «## ⬜ Lo que esto NO es todavía»; :70 «Falta la otra mitad [...] el paso de **eigenvariable** — de `Γ ⊢₀ φ(c)` con `c` fresca concluir `Γ ⊢₀ ∀x φ(x)`»; :73 «Es otra operación (`abstractConst`)»; :77 «la mitad del testigo fresco sigue abierta». MEDIDO: `abstractConst` no está declarado en ninguna parte; la operación se llama `absTerm`/`absFormula` (Eigenvariable.lean:71) y el teorema es Eigenvariable.lean:448 «theorem derives0_gen_fresh»

* **[media]** Fresh0 y HenkinLimit0 repiten que el `if IsConsistent` de Lindenbaum «aún no ha entrado»
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Fresh0.lean:62 «ése es el `if IsConsistent …` de Lindenbaum (§6.3), y todavía no ha entrado.»; E:/dropbox/github/lean4/FOL/FOL/HenkinLimit0.lean:74 «ése es el `if IsConsistent …` de Lindenbaum (§6.3), que aún no ha entrado.» EXISTE HOY: FOL/Lindenbaum0.lean (`LindenbaumStep`, `lindenbaum_lemma`, `henkin_completion` :233) y Canonical0.lean:563 `completeness₀`. La frase está DUPLICADA en dos ficheros — el mismo patrón de multiplicación que [E] cazó en los .md

* **[media]** NDtoLK0 titula «H3 se queda con una sola deuda», dos veces
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/NDtoLK0.lean:18 «# `FOL.NDtoLK0` — **`NDtoLK` DEMOSTRADA**: H3 se queda con una sola deuda»; :200 «/-- ⭐⭐⭐⭐ **Y con ella, H3 se queda con UNA sola deuda: el Hauptsatz.** -/». El Hauptsatz está: Hauptsatz0.lean:1208

* **[baja]** HerbrandBlock0 se CONTRADICE a sí mismo: la cabecera dice PAGADA, el cuerpo sigue con ⬜
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/HerbrandBlock0.lean:50 «## 🏁 La mitad ⟹ — **PAGADA el 2026‑09‑18** en `FOL.BlockExtraction0` (ADR‑064)» frente a :181 «/-- ⬜ La extracción para bloques. **No se postula**: se enuncia [...] La obstrucción está medida en la cabecera del módulo. -/». La corrección a mano tocó la cabecera y no el docstring del `def`

* **[baja]** Lindenbaum0 anuncia como «siguiente tramo» los cuatro `max_cons_*` que ya están escritos
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Lindenbaum0.lean:37 «⬜ El resto de la familia (`and`, `or`, `ex`, `forall`) va con el modelo canónico, que es el siguiente tramo.» EXISTEN HOY: Canonical0.lean:110 `max_cons_and`, :123 `max_cons_or`, :324 `max_cons_ex`, :335 `max_cons_forall`

* **[baja]** Las CUATRO ⬜ que sí son ciertas (para que el arreglo no las borre)
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL/Craig0.lean:88 «⬜ No medido» (puente HACIA `LKp`) — sólo existe la dirección contraria, Craig0.lean:122 «theorem lkp_to_lk0»; E:/dropbox/github/lean4/FOL/FOL/SkolemHerbrand0.lean:57 «⬜ **no medido**»; E:/dropbox/github/lean4/FOL/FOL/Lift0.lean:41 «⬜ **No se ha hecho, y la razón es de riesgo, no de gusto**» (decisión de NO hacer, correctamente protegida); E:/dropbox/github/lean4/FOL/FOL/Enumeration.lean:77 «⬜ Si el propietario prefiere la corta» (oferta, no deuda)

#### Acción propuesta

SÍ, JUSTIFICA UN CONTROL [G] NUEVO — y con holgura: 25 hallazgos en 16 de 52 módulos, no 1. Pero el [G] hay que escribirlo sabiendo lo que NO puede hacer: sólo 5 de los 25 son mecanizables hoy (medido). Así que la acción es doble.

(1) ARREGLO PUNTUAL, ya: las 20 ⬜ obsoletas + las 5 frases sin ⬜. Es edición de docstrings, sin tocar código, y hay que respetar las 4 ⬜ vigentes (Craig0:88, Enumeration:77, Lift0:41, SkolemHerbrand0:57). Prioridad por gravedad: Herbrand0 (4 sitios), Sequent0 (3+1), Skolem0 (3, y una etiquetada «MEDIDO»), Derives0, Prenex0, TheoryFramework/Instances/FOL.lean (que además cita un fichero inexistente y una cifra falsa por 5×).

(2) CONTROL [G] en check-doc-sync.bash, en el estilo de [A]..[F]: [G.1] OBJETIVO que ROMPE, [G.2] AVISO. Va después de [F] y antes del RESUMEN. Código concreto, ya probado en seco (3 roturas, 0 falsos positivos):

# ─── [G] DEUDAS DE CABECERA YA PAGADAS ──────────────────────────────────────
# ⛔⛔ AÑADIDO EL 2026-09-18, y por un barrido que midió VEINTE cabeceras mintiendo.
# [E] mira la FECHA del titular; [B] mira los símbolos que los .md citan. NADIE miraba lo que
# el docstring de un MÓDULO .lean AFIRMA que falta. Precedente: `SkolemNF0` y `HerbrandBlock0`
# anunciaban abiertas deudas ya pagadas y se corrigieron A MANO, porque quien las escribió se
# acordó. 🔑 Un control que depende de la memoria del autor no es un control.
echo
echo "════ [G] DEUDAS DE CABECERA YA PAGADAS ════"
G_FAIL=0
GSRC="FOL/ TheoryFramework/"
DEBT='⬜|\bDEUDA\b|No está hecha|NO está hecha|no ha entrado|No hecho|No medido|LA ÚNICA DEUDA'

# ── [G.1] una deuda enunciada como `Prop` que YA tiene testigo INCONDICIONAL ──
# 🔑 El idioma del proyecto es exacto —*una deuda se ENUNCIA como `Prop`, nunca se postula*— y
# se paga con `theorem X : ESA_PROP := …`. Eso se compara a máquina sin leer prosa.
# ⚠️ El testigo tiene que ser INCONDICIONAL: `herbrandExtraction_of (hcut) (htr)` NO paga nada,
# es el CONSUMIDOR. Por eso el patrón exige `: NOMBRE :=` sin binders delante. Sin esa
# restricción, [G.1] daría rojo el día que se escribe el consumidor — o sea, siempre.
GPROPS=$(mktemp)
grep -rnE "^def +[A-Za-z_][A-Za-z0-9_'₀₁₂ⁿ]* *: *Prop" $GSRC --include=*.lean > "$GPROPS"
while IFS= read -r p; do
  [ -z "$p" ] && continue
  GF=${p%%:*}; grest=${p#*:}; GL=${grest%%:*}
  GNAME=$(printf '%s' "$grest" | sed 's/^[0-9]*://' | awk '{print $2}')
  [ -z "$GNAME" ] && continue
  # el docstring INMEDIATAMENTE anterior, delimitado por `-/` y NO por línea en blanco:
  # ⚠️ medido — un docstring largo lleva blancos DENTRO, y cortando ahí se pierde justo la
  # línea del ⬜ (le pasó a `Herbrand0.lean:268`, que quedaba fuera por dos líneas).
  i=$((GL-1)); BLK=""
  while [ "$i" -gt 0 ]; do
    ln=$(sed -n "${i}p" "$GF")
    case "$ln" in *"-/"*) [ -n "$BLK" ] && break ;; esac
    [ -z "${ln// /}" ] && [ -z "$BLK" ] && break
    BLK="$ln
$BLK"; i=$((i-1))
  done
  printf '%s' "$BLK" | grep -qE "$DEBT" || continue
  WIT=$(grep -rnE "^theorem +[A-Za-z_][A-Za-z0-9_'₀₁₂ⁿ]* *: *$GNAME *:=" $GSRC --include=*.lean | head -1)
  if [ -n "$WIT" ]; then
    echo "  ✗ $GF:$GL — \`$GNAME\` se marca como DEUDA y YA TIENE TESTIGO INCONDICIONAL:"
    echo "        $WIT" | cut -c1-140
    G_FAIL=1
  fi
done < "$GPROPS"
rm -f "$GPROPS"

# ── [G.2] AVISO: un párrafo ⬜ que cita un nombre YA declarado ────────────────
# ⚠️ Es AVISO y no rompe, y está medido por qué: de 11 avisos sobre el árbol de hoy, 2 son
# ciertos (`derives0_soundness`, `prenex`) y 8 son legítimos — `Skolem0` cita `shiftEnv`,
# `updateEnv`, `exBlock` y `subst_exBlock` para decir «esto SÍ está, lo otro no». Distinguirlos
# exige leer la frase. 🔑 Un control que grita lobo se deja de mirar.
echo "  ── [G.2] nombres citados en un párrafo ⬜ y ya declarados — AVISO ──"
GDECLS=$(mktemp)
grep -rhoE "^(theorem|def|abbrev|noncomputable def) +[A-Za-z_][A-Za-z0-9_'₀₁₂ⁿ]*" $GSRC --include=*.lean \
  | awk '{print $NF}' | sort -u > "$GDECLS"
G2=0
while IFS= read -r hit; do
  [ -z "$hit" ] && continue
  GF=${hit%%:*}; grest=${hit#*:}; GL=${grest%%:*}
  # ⚠️ el identificador se extrae SIN exigir la comilla de cierre: el idioma del proyecto
  # escribe `derives0_soundness : Γ ⊢₀ f → Γ ⊨ f` dentro de UN solo par de comillas, y un
  # patrón que pida `…` cerrando pegado al nombre no casa NUNCA. Era el fallo de la v1.
  for sym in $(sed -n "${GL},$((GL+6))p" "$GF" | grep -oE '`[a-z][A-Za-z0-9_₀₁₂ⁿ]{4,}' | tr -d '`' | sort -u); do
    grep -qxF "$sym" "$GDECLS" || continue
    grep -qE "^(theorem|def|abbrev|noncomputable def) +$sym\b" "$GF" && continue
    echo "  ⚠️  $GF:$GL cita \`$sym\`, declarado en $(grep -rlE "^(theorem|def|abbrev) +$sym\b" $GSRC --include=*.lean | head -1)"
    G2=$((G2+1))
  done
done <<< "$(grep -rn '⬜' $GSRC --include=*.lean)"
rm -f "$GDECLS"
[ "$G2" = "0" ] && echo "  ✓ ningún párrafo ⬜ cita un nombre ya declarado"
if [ "$G_FAIL" = "0" ]; then
  echo "  ✓ [G.1] ninguna deuda enunciada tiene ya testigo"
else
  echo "  ❌ [G.1] una deuda PAGADA sigue anunciada como abierta — corregir la cabecera."
  FAIL=1
fi

(3) Y LO QUE [G] NO CUBRE, que es el 80 % — decirlo en el propio script en lugar de dejar que el verde lo tape: los 20 sitios restantes son prosa («falta el Hauptsatz», «H3 NO está», «aún no ha entrado») sin `Prop` que casar. La única defensa barata es una CONVENCIÓN nueva, que sí se puede exigir a máquina: **toda línea ⬜ lleva entre comillas el NOMBRE que la saldará**. Con eso [G.2] pasa de aviso a control objetivo. Sin ella, [G] es parcial y hay que anunciarlo así, porque «✅ [G] sin deudas pagadas anunciadas» sobre un árbol con 20 cabeceras mintiendo sería exactamente la novena causa de [[feedback-controles-que-no-comprueban]].

⛔ NO he ejecutado `lake` en ningún momento; todos los números salen de leer el árbol. No he editado ningún fichero de los repos.

#### ⚖️ La refutación — **MANDA ÉSTA**

EL NÚCLEO DEL HALLAZGO ES CIERTO Y LO HE RE-MEDIDO YO. Cuadran las tres cifras de alcance (`find FOL TheoryFramework -name "*.lean" | wc -l` = 52; `grep -rn "⬜" … | wc -l` = 24; `-rl | wc -l` = 16) y cuadran TODOS los testigos citados: Hauptsatz0.lean:1208 `hauptsatz`, :1224 `cut_elimination`, :1227 `herbrand_extraction`, :1233 `herbrand`; SkolemN0.lean:73 `envPush`, :209 `skolem_conservative_n`; Soundness0.lean:80 `derives0_soundness`; Rename.lean:415 `derives0_rename_iff`; Canonical0.lean:563 `completeness₀`, :110/:123/:324/:335 los cuatro `max_cons_*`; PrenexNF0.lean:104 `prenex`, :299 `prenex_iff`; BlockExtraction0.lean:503 `herbrand_extraction_block`; Derives2.lean:279/:471; Lindenbaum0.lean:233 `henkin_completion`; Eigenvariable.lean:71 `absTerm`, :448 `derives0_gen_fresh`. Y `abstractConst` sólo aparece en la prosa de Rename.lean:73, en ningún `def`. También confirmo el [G.1]: los tres `def … : Prop` con marca de deuda y testigo incondicional existen (Herbrand0:275, HerbrandBlock0:183, Sequent0:504) y sus tres testigos también. Y confirmo «antes de construir, buscar»: `check-doc-sync.bash` tiene sólo [A], [A2], [E], [B], [C], [D], [F] — ninguno mira lo que un docstring de módulo .lean AFIRMA que falta. El control [G] es genuinamente nuevo.

NO SOBREVIVE POR LAS CIFRAS, y el fallo no es cosmético: la acción propuesta (1) borraría una deuda VIVA.

[1] MISCLASIFICACIÓN MEDIDA — `TheoryFramework/Instances/FOL.lean:47` está contada entre las 20 OBSOLETAS (la aritmética lo obliga: 24 ⬜ − 4 declaradas vigentes = 20, y mi recuento línea a línea de las 20 la incluye), y es VIGENTE. Medido: `grep -rn "CompleteLogic" --include=*.lean .` devuelve la clase (Logic.lean:59), sus usos (MetaTheorems.lean:30/:36/:49) y esa línea :47 — NINGUNA instancia `CompleteLogic Formula`. Y no puede pagarla `completeness₀`: la instancia `folSystem` (Instances/FOL.lean:62) declara `derives := fun Γ f => Derives Γ f`, el `Derives` CONTAMINADO, mientras que Canonical0.lean:563 prueba `completeness₀` sobre `Derives₀`. La deuda sigue abierta; lo caduco es sólo su JUSTIFICACIÓN. ⇒ 20 → 19 obsoletas (79 %, no 83 %), 4 → 5 vigentes, TOTAL 25 → 24.

[2] CITA DE LÍNEA FALSA — el resumen dice «TheoryFramework/Instances/FOL.lean:30» tres veces. `grep -n` la sitúa en :33. Off-by-3 en una cifra presentada como medida.

[3] EL CENSO NO ES EXHAUSTIVO PERO SE PRESENTA COMO «TOTAL» — la MISMA cifra falsa («cinco `axiom`» de un `FOL/Completeness.lean` que no existe) aparece además en `TheoryFramework/Logic.lean:56` (docstring de la clase `CompleteLogic`, con los nombres `formula_enum`, `formula_enum_surj`) y en `Instances/FOL.lean:48`, y ninguna de las dos está contada. «TOTAL: 25» es una COTA INFERIOR vestida de censo — justo el patrón de [[feedback-estimacion-sin-etiqueta]].

[4] CONFUSIÓN MEDICIÓN / JUICIO, que es la regla 1 del proyecto — el bloque va encabezado por «TODO LO SIGUIENTE ES MEDIDO», pero mezcla dos capas: los CONTEOS (24, 16, 52, los testigos) sí son medidos; la ADJUDICACIÓN «obsoleta vs vigente» es interpretación de prosa, y [1] demuestra que esa capa falla. Al menos tres ⬜ contadas como falsas son rótulos de sección LOCALMENTE VERDADEROS: Herbrand0:38 («⬜ DEUDA, enunciada como `Prop`, no postulada») y :254 («§6 · ⬜ H3, ENUNCIADA — y su CONSUMIDOR») describen con exactitud lo que ESE módulo contiene hoy (Herbrand0:275 enuncia `HerbrandExtraction` y no la prueba); lo falso es sólo el categórico de :40 y :271. Igual Sequent0:95.

[5] EL «AGRAVANTE» DE Skolem0 ESTÁ INVERTIDO — el hallazgo subraya que «la falsedad va etiquetada MEDIDO» (Skolem0:90). Medido: `grep -rln "def envPush" FOL/` → sólo `FOL/SkolemN0.lean`. Es decir, la frase etiquetada MEDIDO («`FOL/Semantics.lean` tiene shiftEnv/updateEnv pero nada iterado `k` veces») SIGUE SIENDO CIERTA; lo caduco es el rótulo :84 y la estimación :92. El agravante retórico no resiste la medición.

LENTE DE VACUIDAD (ADR-067): el hallazgo NO es vacuo. Cada par (afirmación, nombre existente) es falsable y se evaporaría en un árbol con las cabeceras al día. Pero sí hay vacuidad LOCAL en el entregable: [G.2] produce 11 avisos de los que 8 son falsos positivos sobre el árbol de hoy (el propio hallazgo lo dice) — un aviso que acierta 2 de 11 es candidato a la novena causa de [[feedback-controles-que-no-comprueban]], y el hallazgo lo reconoce pero aun así lo propone para entrar en el script.

**Lo correcto:**

LO CORRECTO, y lo que debe sustituir al veredicto entregado:

(A) EL HALLAZGO DE FONDO SE MANTIENE, con cifras corregidas: de las 24 líneas ⬜ en 16 de los 52 módulos, **19 anuncian una deuda ya pagada y 5 siguen vigentes**. Las cinco vigentes son Craig0:88, Enumeration:77, Lift0:41, SkolemHerbrand0:57 **y TheoryFramework/Instances/FOL.lean:47**. Más **≥7 afirmaciones falsas sin ⬜** (Fresh0:62, HenkinLimit0:74, NDtoLK0:18, NDtoLK0:200, Instances/FOL.lean:33, Instances/FOL.lean:48, Logic.lean:56). TOTAL ≥26, y va etiquetado **COTA INFERIOR MEDIDA**, no «total»: el barrido cazó sólo lo que casa con sus patrones, y la tercera aparición de «cinco `axiom`» se le escapó.

(B) ⛔ NO EJECUTAR LA ACCIÓN (1) TAL COMO ESTÁ. Reescribir `Instances/FOL.lean:47` como deuda pagada declararía cerrada una obligación que está ABIERTA y cuya razón de fondo el hallazgo no vio: `folSystem` instancia `derives := Derives`, no `Derives₀`, luego `completeness₀` (Canonical0:563) **no paga** `CompleteLogic Formula`. Lo que hay que corregir ahí es la JUSTIFICACIÓN, en tres sitios y no en uno (Instances:33, Instances:48, Logic.lean:56): `FOL/Completeness.lean` no existe y `cuarentena/Completeness.lean` tiene UN `axiom` (`henkin_extension_lemma`, :756, verificado) — y añadir por qué la decisión sigue pendiente pese a `completeness₀`: **porque la instancia va sobre `Derives`**. Eso es un hallazgo MEJOR que el entregado y el barrido lo pasó por alto.

(C) EL CONTROL [G] SÍ ESTÁ JUSTIFICADO y no duplica nada (medido: check-doc-sync.bash sólo tiene A/A2/E/B/C/D/F). Pero entra **sólo [G.1]** (3 roturas estructuralmente verificadas, 0 falsos positivos) y **[G.2] NO entra en el script** mientras acierte 2 de 11: se queda como sonda manual, o espera a la convención propuesta (toda línea ⬜ lleva entre comillas el nombre que la saldará), que es lo que la convertiría en objetiva. Y el texto que [G] imprima debe decir su cobertura: **5 de ~26 sitios**, el resto es prosa sin `Prop` que casar.

(D) Antes de tocar ninguna cabecera, aplicar a cada ⬜ el criterio que este hallazgo no separó: **¿la línea afirma algo sobre EL REPO (global) o describe lo que ESE módulo contiene (local)?** Las locales (Herbrand0:38, :254; Sequent0:95) son ciertas y no se tocan; lo que se corrige son los categóricos globales (Herbrand0:40, :71, :271; Sequent0:29, :503; Skolem0:84, :92; Derives0:88-93; Derives1:76; Derives2:85; Prenex0:58-62; Propositional0:65; Rename:68-77; NDtoLK0:18, :200; Fresh0:62; HenkinLimit0:74; Lindenbaum0:37; HerbrandBlock0:181).

---

### A2 · Titulares entregados FUERA de `check-footprints`
**Veredicto del informe:** `CONFIRMADO` · **¿sobrevive a la refutación?** **SÍ**

**Resumen:** Comparé los 356 titulares cuyo footprint imprimen los dos árboles contra las 147 filas de check-footprints.bash: 223 se imprimen y NO están declarados, y de ellos 41 son titulares de verdad (33 en FOL, 8 en RPP), 15 de ellos con el footprint YA PUBLICADO por nombre en la documentación.

#### Cifras

TODAS MEDIDAS leyendo el árbol y las dos capturas. Ninguna estimación.

── 0 · VALIDEZ DE LA CAPTURA (lo primero que había que comprobar) ──
FOL: `grep -c "depends on axioms|does not depend" axioms_fol.txt` = 171.
  Árbol: `grep -rn "#print axioms" FOL/*.lean` = 174, menos 1 en `cuarentena/Inconsistencia.lean`
  (fuera del build) y 2 que son TEXTO DE COMENTARIO (`FOL/Lindenbaum0.lean:70`,
  `FOL/DecEq.lean:25`) ⇒ 171. CUADRA EXACTO.
RPP: capturadas 186. Árbol (sólo `ROBINSON_PlusPlus/`, descontando comentarios) = 186,
  verificado módulo a módulo (24 módulos, suma 2+1+2+19+…+2 = 186). CUADRA EXACTO.
⇒ la capturas SON completas; la diferencia que sigue no es un artefacto de caché.

── 1 · LA DIFERENCIA ──
  impresos distintos .......... 356   (171 + 186 − 1 duplicado:
                                       `SubstfcWitnessPrf.prf_nil_or_cons` se imprime dos veces,
                                       en su módulo y en `EvalLiftcPrf.lean:912`)
  filas de la tabla ........... 147   (check-footprints.bash líneas 24–170, sin duplicados)
  solapamiento ................ 133
  (a) impresos y NO en tabla .. 223   = 40 FOL + 183 RPP
  (b) en tabla y NO impresos ..  14   ← TODOS LEGÍTIMOS (comprobado uno a uno: los 14 existen
                                       como declaración de nivel superior; sus módulos
                                       simplemente no los `#print`ean y el control los mide
                                       con el fichero Lean que él mismo genera)
  356 − 223 = 133 = 147 − 14  ✓

── 2 · LISTA (b) COMPLETA — 14, ninguno es defecto ──
FOL.derive_atom_congr (FOL/Eq.lean:417) · FOL.derive_eq_func_congr (Eq.lean:396) ·
FOL.substTerm_liftTerm (Eq.lean:29) · FOL.Metamath.Enumeration.natToFormula_surj
(Enumeration.lean:374) · FOL.Metamath.Semantics.{shift_updateEnv_comm:138,
eval_liftFormula_ext:164, eval_substFormula_ext:205, contextSatisfies_lift_zero:254} ·
FOL.PrenexNF0.iffAll_trans:137 · FOL.Propositional0.derives0_em_prop:370 ·
FOL.Sequent0.quantFree_subst:158 · FOL.SequentSound0.eqInstance_valid:114 ·
ROBINSON_PlusPlus.Meta.Provability.charsCode (Provability.lean:34) ·
ROBINSON_PlusPlus.Minimal.Axioms.axiomsCodeT (Axioms.lean:990).

── 3 · LISTA (a), PARTE FOL — 40, con footprint MEDIDO y clasificación ──
TITULARES (33):
 T·G1 footprint PUBLICADO POR NOMBRE en la doc y que ningún control re-mide (6):
  FOL.Craig0.predF_lift ................. net-0   [REFERENCE.md:585 + DECISIONS.md:4910 «sin ningun axioma»]
  FOL.Finitary0.lkc_empty_of_no_bot ..... net-0   [DECISIONS.md:4771 «net-0 PURO»]
  FOL.Finitary0.lkc_not_empty_fin ....... propext,Quot.sound  [DECISIONS.md:4772 «idem»]
  FOL.SkolemNF0.occurs_prenex ........... propext             [DECISIONS.md:4844 `[propext]`]
  FOL.SkolemNF0.skolemizeF_shape ........ propext,Quot.sound  [DECISIONS.md:4845]
  FOL.Skolem0.evalTerm_updateFunc ....... net-0   [REFERENCE.md:582 «el lema de coincidencia, sin axiomas»]
 T·G2 familia CERRADA que la doc publica entera y la tabla cubre a medias (6):
  FOL.Prenex0.and_ex / or_ex / impl_ex_left / impl_forall_right  (todas propext,Quot.sound)
    [REFERENCE.md:588 «las OCHO equivalencias de desplazamiento» — la tabla tiene 4 de 8]
  FOL.Eq0.derives0_eq_symm / derives0_eq_trans  (propext,Quot.sound)
    [REFERENCE.md:568 «las CUATRO piezas de la igualdad» — la tabla tiene 2 de 4]
 T·G3 control M-11 de recursores, incompleto (1):
  LKh.rec ............................... net-0 — y `Derives₀.rec`, `Derives₁.rec`,
    `Derives₂.rec` y `LK₀.rec` SÍ están en la tabla. `LKh` es el tipo del HAUPTSATZ.
 T·G4 gemelo del que sí está declarado, mismo papel (20):
  derives0_raa (propext) · FOL.Canonical0.derives0_peirce (choice) ·
  FOL.Compacity0.consistency_of_satisfiable₀ (choice) · FOL.Compacity0.model_existence_countable₀ (choice) ·
  FOL.Finitary0.lk0_no_bot · FOL.Finitary0.lkc_no_bot · FOL.Finitary0.derives0_not_P_fin ·
  FOL.Fresh0.cst_bound_formula (choice) · FOL.HenkinLimit0.hen_consistent (choice) ·
  FOL.Herbrand0.ex_tercio · FOL.HerbrandBlock0.derives0_exBlock_of_inst ·
  FOL.HerbrandBlock0.derives0_exBlock_of_disj · FOL.Lindenbaum0.derivesSet0_intro_impl (choice) ·
  FOL.Lindenbaum0.max_cons_contains (choice) · FOL.PrenexNF0.mergeAnd_iff · mergeImpl_iff ·
  FOL.SequentSound0.lk0_sound (choice) · FOL.SequentSound0.lk0_to_derives2 (choice) ·
  FOL.SkolemHerbrand0.impAll_neg_allBlock · FOL.SkolemNF0.derives0_skolemize
ANDAMIO (7) — lemas internos, sin cifra publicada ni gemelo declarado:
  FOL.BlockExtraction0.herbrandExtractionBlock_of (paso condicionado; el incondicional
  `herbrand_extraction_block` SÍ está) · BlockExtraction0.instB_snoc · quantFree_of_blockInv
  (invariante interno) · FOL.NDtoLK0.viaEqImpl (net-0, «el patrón de las tres congruencias») ·
  FOL.Propositional0.elim_atoms (motor de Kalmár) · FOL.Skolem0.evalTerm_new (net-0, lema
  puntual) · FOL.SkolemHerbrand0.impAll_ex_neg_not_forall («la mitad intuicionista»).

── 4 · LISTA (a), PARTE RPP — 183, agrupada por módulo ──
TITULARES (8):
  OmegaStrength.derives_completo ...... [propext,Classical.choice,Quot.sound,raa]
     ⛔ ES EL ÚNICO DE LOS 356 CON UN AXIOMA DEL PROYECTO EN SU FOOTPRINT, y no está declarado.
  GodelTwo.d3 (fue `axiom` hasta 09-10g) · GodelTwoPrf.prf_godelCN_fixedpoint (sus dos hermanos
  `goedel_first_prf` y `goedel_second_prf` SÍ están) · SubstTreeReflect.pcc_lineWF_tracked (C3) ·
  VerifierSound.verifier_sound · VerifierSound.negVerifier_of_deudas · ChainNegPrf.deuda_inNeg ·
  PremsBdAllPrf.d3_prf_real [doc/REFERENCE-Incompleteness.md:5353 publica su footprint].
ANDAMIO (175) — maquinaria de la aritmetización, por familia de prefijo MEDIDA:
  pcc_* 68 · prf_* 25 · refl_* 19 · DESCENSO* 9 · d3_prf_of* 8 · PHI* 6 · caso* 6 · h*/deuda* 22 ·
  resto 12. Por módulo: ChainNegPrf 2, CodeWitnessPrf 1, D3BodyPrf 2, D3ChainDotPrf 19,
  Delta0ReflectPrf 1, DotConsPrf 1, EvalLiftcPrf 21, EvalLiftfcPrf 20, EvalNthcPrf 1,
  EvalSubstfcPrf 5, EvalSubsttcPrf 7, GodelTwo 1, GodelTwoPrf 1, HasWitFTrackedPrf 7,
  HasWitTcFnPrf 3, HasWitTrackedPrf 7, LiftcCodePrf 34, LiftfcWitnessPrf 4, LineWFGuardPrf 3,
  ListEtaPrf 2, OmegaStrength 1, PremsBdAllPrf 8, PremsOfDotPrf 3, PremsOfTagPrf 4,
  SubstfcWitnessPrf 6, SubstTreeReflect 13, TrackedAtomsPrf 4, VerifierSound 2. (suma = 183)
  ⚠️ ÁMBITO: la tabla sólo declara 4 nombres de RPP, así que este 175 NO es un fallo — es que el
  control tiene alcance FOL. Lo que sí es fallo son los 8 titulares.

── 5 · LOS SEIS MÓDULOS NUEVOS, uno a uno (impresos / en tabla / faltan) ──
  SkolemN0 ............ 5 / 5 / 0   ✅ COMPLETO
  Craig0 .............. 7 / 6 / 1   → `predF_lift` (footprint PUBLICADO, net-0)
  SkolemNF0 ........... 12 / 9 / 3  → `derives0_skolemize`, `occurs_prenex`, `skolemizeF_shape`
                                      (los DOS últimos con footprint publicado en ADR-065)
  BlockExtraction0 .... 7 / 4 / 3   → los tres andamio
  SkolemHerbrand0 ..... 4 / 2 / 2   → `impAll_neg_allBlock` (titular), `impAll_ex_neg_not_forall`
  DecEq.lean .......... 2 / 2 / 0   ✅
  ⛔ Y el hallazgo de ADR-068 que NO sale de la diferencia porque NO SE IMPRIME NADA:
  `FOL/FOL.lean` —donde viven `TermG` (línea 27) y `FormulaG` (línea 32), el núcleo genérico
  nuevo— NO CONTIENE NI UN `#print axioms` (medido: `grep -rn "#print axioms" FOL/FOL.lean` = 0
  resultados). De los 15 `inductive` de FOL, el control M-11 de recursores cubre 4
  (`Derives₀/₁/₂.rec`, `LK₀.rec`); `LKh.rec` se mide y no se declara; y `TermG.rec`,
  `FormulaG.rec`, `LKc.rec`, `LKp.rec` no se miden en ninguna parte.

── 6 · CIFRA EXACTA PEDIDA ──
  TITULARES ENTREGADOS QUE FALTAN POR DECLARAR: **41** (33 FOL + 8 RPP).
  De ellos **15 de gravedad ALTA** (footprint ya publicado por nombre, o familia cerrada
  publicada a medias, o el control M-11, o el único con axioma del proyecto):
  predF_lift, lkc_empty_of_no_bot, lkc_not_empty_fin, occurs_prenex, skolemizeF_shape,
  evalTerm_updateFunc, and_ex, or_ex, impl_ex_left, impl_forall_right, derives0_eq_symm,
  derives0_eq_trans, LKh.rec, OmegaStrength.derives_completo, PremsBdAllPrf.d3_prf_real.
  Andamio legítimo: 182 (7 FOL + 175 RPP). 41 + 182 = 223 ✓
  ⚠️ NOTA DE MÉTODO: los 223 y los 14 son MEDIDOS (diferencia de conjuntos). El reparto
  41/182 lleva JUICIO en la franja G4/andamio; el núcleo de 15 no lo lleva, porque la cifra
  la publica la propia documentación del proyecto y yo sólo la he contrastado.

#### Hallazgos

* **[alta]** 223 titulares entregados fuera de la tabla, y el control no puede verlos por construcción
  · *Evidencia:* E:/dropbox/github/lean4/ROBINSON_PlusPlus/check-footprints.bash:228 — «done <<< "$TABLA"»: el único bucle del script recorre la tabla, nunca la salida del build. Medido: 356 nombres impresos, 147 filas, 223 impresos y no declarados.

* **[alta]** derives_completo es el ÚNICO titular con un axioma del proyecto en su footprint — y no está declarado
  · *Evidencia:* scratchpad/axioms_rpp.txt — «ROBINSON_PlusPlus/Meta/OmegaStrength.lean:170:0: 'ROBINSON_PlusPlus.Meta.OmegaStrength.derives_completo' depends on axioms: [propext, Classical.choice, Quot.sound, raa]». `grep -c raa` sobre las 147 filas de la tabla = 0.

* **[alta]** Seis footprints ya PUBLICADOS por nombre que ningún control re-mide
  · *Evidencia:* E:/dropbox/github/lean4/FOL/REFERENCE.md:585 — «⭐ `lkp_to_lk0`, `predF_lift` y `predF_subst` **sin ningún axioma**»; `predF_subst` y `lkp_to_lk0` están en la tabla, `predF_lift` no. Igual en DECISIONS.md:4844 «| `qdepth_subst`, `occurs_prenex` | `[propext]` |» y :4845 para `skolemizeF_shape`.

* **[alta]** Dos familias que la doc publica CERRADAS y la tabla cubre a medias
  · *Evidencia:* E:/dropbox/github/lean4/FOL/REFERENCE.md:588 — «| `Prenex0.lean` | 🏁 **capa prenexa**: las ocho equivalencias de desplazamiento | ``propext, Quot.sound`` |»: la tabla declara 4 (and_forall, or_forall, impl_ex_right, impl_forall_left) y faltan and_ex, or_ex, impl_ex_left, impl_forall_right. REFERENCE.md:568 «las cuatro piezas de la **igualdad**»: la tabla declara 2 de 4.

* **[alta]** El control M-11 de recursores está incompleto: LKh.rec se mide y no se declara
  · *Evidencia:* FOL/Hauptsatz0.lean:1241 «#print axioms LKh.rec» ⇒ «does not depend on any axioms»; la tabla tiene Derives₀.rec, Derives₁.rec, Derives₂.rec y LK₀.rec, y no LKh.rec. LKh (Hauptsatz0.lean:138) es el tipo del HAUPTSATZ.

* **[alta]** ADR-068: el núcleo genérico nuevo no tiene NINGÚN footprint, ni impreso ni declarado
  · *Evidencia:* E:/dropbox/github/lean4/FOL/FOL.lean:27 «inductive TermG (S : Type) where» y :32 «inductive FormulaG (S : Type) where»; `grep -rn "#print axioms" FOL/FOL.lean` devuelve 0 resultados. De los 15 inductivos de FOL sólo 5 tienen su recursor medido.

* **[media]** ADR-061 publica lkc_empty_of_no_bot como «net-0 PURO» y lkc_not_empty_fin con su footprint; ninguno de los dos está en la tabla, mientras sus gemelos lk0_* sí
  · *Evidencia:* E:/dropbox/github/lean4/ROBINSON_PlusPlus/DECISIONS.md:4770-4773 — «lk0_empty_of_no_bot … net-0 PURO / lkc_empty_of_no_bot : idem para LKc … net-0 PURO / lk0_not_empty_fin : ¬ LK₀ [] [] [propext, Quot.sound] / lkc_not_empty_fin : idem». Medido hoy: lkc_empty_of_no_bot net-0 ✓, lkc_not_empty_fin [propext, Quot.sound] ✓ — las cifras son correctas, lo que falta es el control.

* **[baja]** Los 14 nombres de la tabla que no se imprimen son legítimos — comprobado uno a uno
  · *Evidencia:* check-footprints.bash:170-180 genera su propio fichero Lean («echo "#print axioms $NOMBRE"»); los 14 existen como declaración de nivel superior (p.ej. FOL/Eq.lean:417 derive_atom_congr, ROBINSON_PlusPlus/Minimal/Axioms.lean:990 axiomsCodeT). No hay filas muertas en la tabla.

* **[media]** De los seis módulos nuevos, SkolemN0 es el único COMPLETO; los otros cinco dejan 9 titulares/andamio sin declarar
  · *Evidencia:* Medido por módulo (impresos/tabla): SkolemN0 5/5, Craig0 7/6, SkolemNF0 12/9, BlockExtraction0 7/4, SkolemHerbrand0 4/2, DecEq 2/2. Cita: FOL/SkolemNF0.lean:478 «theorem occurs_prenex» y :210 «theorem skolemizeF_shape», ambos con footprint publicado en DECISIONS.md:4844-4845 y ausentes de la tabla.

* **[media]** El reparto titular/andamio de los 183 nombres de RPP lleva juicio, no medición: la tabla sólo declara 4 nombres de RPP y ese alcance no está escrito en ninguna parte  ⚠️ **NO MEDIDO — es juicio**
  · *Evidencia:* check-footprints.bash líneas 24-170: 143 filas FOL + 4 RPP (goedel_first_prf, goedel_second_prf, Provability.charsCode, Minimal.Axioms.axiomsCodeT). El encabezado del script (líneas 1-17) no dice que el alcance sea FOL.

#### Acción propuesta

HAY QUE ESCRIBIR UN CONTROL [G] NUEVO, no arreglar puntualmente la tabla. Razón medida: el fallo no es que falten 41 filas — es que `check-footprints.bash` sólo sabe recorrer su propia tabla (`done <<< "$TABLA"`, línea 228) y por construcción NO PUEDE detectar un titular entregado. Es exactamente la causa del 09-17 (85→88), y volverá a pasar con el séptimo módulo nuevo.

[G] propuesto — `check-titulares-declarados.bash`, dirección CONTRARIA:
  1. `lake build FOL TheoryFramework` (desde la raíz de RPP, NUNCA `cd FOL`), capturar stdout.
  2. Extraer con `grep -oE "'[^']+' (depends on axioms|does not depend)"` los nombres impresos.
  3. `comm -23 impresos tabla` ⇒ ROMPE si la diferencia no está en una LISTA BLANCA explícita
     de andamio, versionada en el propio script con una línea de justificación por entrada.
  ⇒ así un `#print axioms` nuevo obliga a decidir: o entra en la tabla, o se justifica por escrito.
  ⚠️ El script debe imprimir las DOS cifras (impresos, declarados) y romper si la lista blanca
  crece sin tocar la tabla — si sólo imprime «✅ los N cuadran», repite el error de hoy.

ARREGLOS PUNTUALES que además hay que hacer (son 41 filas, el footprint ya está medido arriba):
  (i) URGENTE — `ROBINSON_PlusPlus.Meta.OmegaStrength.derives_completo|Classical.choice,Quot.sound,propext,raa`.
      Es el único titular del ecosistema cuyo footprint contiene un axioma del proyecto y hoy
      nadie lo vigila: si `raa` se retirara, o si entrara un segundo axioma, el verde no se movería.
  (ii) Las 6 del grupo G1: la documentación ya publica esas cifras (REFERENCE.md:568/582/585/588,
      DECISIONS.md:4771/4772/4844/4845). Publicar una cifra y no re-medirla es literalmente lo
      que el encabezado del propio script llama «una medición falsa» (líneas 11–13).
  (iii) Cerrar las dos familias que la doc publica ENTERAS: las 8 equivalencias de `Prenex0`
      (faltan 4) y las 4 piezas de la igualdad de `Eq0` (faltan 2).
  (iv) `LKh.rec`, y de paso decidir si el criterio M-11 debe cubrir `TermG.rec`/`FormulaG.rec`:
      ADR-068 metió DOS inductivos nuevos bajo todo el núcleo y `FOL/FOL.lean` no imprime NADA.
      Eso no es una fila que falte: es un módulo sin control, y es lo más reciente.
  (v) Los 7 restantes de RPP (d3, prf_godelCN_fixedpoint, pcc_lineWF_tracked, verifier_sound,
      negVerifier_of_deudas, deuda_inNeg, d3_prf_real) — o se declaran, o se escribe en el script
      que el alcance de la tabla es FOL y RPP sólo vigila los 4 de Gödel. Hoy no está escrito.

⛔ NO he ejecutado ningún build: todo sale de leer las dos capturas ya existentes y el árbol.

#### ⚖️ La refutación

SOBREVIVE EL NÚCLEO, y sobrevive porque lo he vuelto a medir yo, no porque me lo crea.

QUÉ PARTE SOBREVIVE EXACTAMENTE (todo reproducido con mis propios grep/comm):
1. La validez de las capturas. FOL: 171 footprints en la captura = 174 ocurrencias de `#print axioms` en el árbol − 1 en `cuarentena/` − 2 que son texto de comentario (`FOL/DecEq.lean:25`, `FOL/Lindenbaum0.lean:70`). RPP: 186 = 195 en `ROBINSON_PlusPlus/` − 9 comentarios. Cuadra exacto en los dos, y el reparto de comentarios lo he localizado línea a línea.
2. La aritmética de conjuntos. 356 nombres distintos (357 con el único duplicado, `SubstfcWitnessPrf.prf_nil_or_cons`), 147 filas únicas en la tabla (líneas 24–170), y `comm` da 223 / 14 / 133 con 40 FOL + 183 RPP. La lista (b) de 14 que él publica es IDÉNTICA nombre a nombre a la que devuelve mi `comm`, y he comprobado cinco de ellas en el árbol con sus números de línea (PrenexNF0:137, Propositional0:370, Sequent0:158, SequentSound0:114, Axioms:990): existen como declaración de nivel superior.
3. El hallazgo estructural, que es el de fondo. `check-footprints.bash:228` es `done <<< "$TABLA"` y es el ÚNICO bucle de comparación; el fichero Lean que el script mide lo genera él mismo desde la misma tabla (líneas 172–180). Por construcción el control no puede ver un `#print axioms` nuevo. Esto es verdad del script, no una tautología: `check-warnings.bash` demuestra que la dirección contraria es implementable en este repo.
4. Los quince de gravedad alta, uno a uno. `predF_lift` net-0 (Craig0.lean:843) contra REFERENCE.md:585 «sin ningún axioma»; `lkc_empty_of_no_bot` net-0 y `lkc_not_empty_fin` `[propext, Quot.sound]` contra DECISIONS.md:4770-4773; `occurs_prenex`/`skolemizeF_shape` contra DECISIONS.md:4844-4845; Prenex0 tiene 4 de 8 en la tabla (faltan and_ex, or_ex, impl_ex_left, impl_forall_right) frente a REFERENCE.md:588 «las ocho equivalencias»; Eq0 tiene 2 de 4 frente a REFERENCE.md:568 «las cuatro piezas»; `LKh.rec` se imprime net-0 en Hauptsatz0.lean:1241 y no está, mientras Derives₀/₁/₂.rec y LK₀.rec sí.
5. `derives_completo` como ÚNICO caso con axioma del proyecto: he barrido TODOS los footprints distintos de las dos capturas y el único que sale de {propext, Classical.choice, Quot.sound} es `[propext, Classical.choice, Quot.sound, raa]` (OmegaStrength.lean:170). `grep -c raa` sobre las 147 filas = 0. La afirmación de unicidad es medida, no retórica.
6. ADR-068: `FOL/FOL.lean` tiene 0 `#print axioms` con `TermG` en 27 y `FormulaG` en 32; 15 `inductive` en `FOL/` y sólo 5 recursores medidos.

LENTE DE VACUIDAD (ADR-067), aplicada en serio: NO es vacuo. Las cifras son contingentes en las dos direcciones — si el proyecto declarara todo lo impreso la diferencia sería 0, y si los módulos no imprimieran nada (b) sería 147. El hallazgo estructural es una propiedad del script y lo refutaría un script que leyese la salida del build. Lo que SÍ roza la vacuidad es el titular «223 titulares fuera de la tabla»: mientras el proyecto siga imprimiendo footprints de andamio, esa cifra será grande en cualquier estado del árbol y por tanto no mide un defecto. El defecto vive en los 15, no en los 223 — y eso él lo dice en §6, pero no en el titular.

MEDICIÓN vs ESTIMACIÓN: el esqueleto (356/147/223/14/133/40/183, el per-módulo, las citas de doc, los footprints) es MEDIDO y lo he reproducido. El reparto 41 titulares / 182 andamio NO lo es, y la línea de cabecera «TODAS MEDIDAS · Ninguna estimación» contradice a su propio hallazgo marcado `medido:false` y a su §6. Es un fallo de etiqueta, no de cifra, y por eso no tumba el hallazgo: el núcleo de 15 no depende del reparto.

**Lo correcto:**

PRECISIONES OBLIGATORIAS ANTES DE QUE ESTO ENTRE EN NINGÚN PLAN (sobrevive, pero no tal como está escrito):

(1) ⛔ LA ETIQUETA DE CABECERA ES FALSA. «CIFRAS QUE AFIRMA: TODAS MEDIDAS. Ninguna estimación» debe retirarse. Correcto: «MEDIDO: 356 impresos, 147 filas, 223/14/133, el per-módulo, los footprints y las citas de doc. JUICIO: el reparto 41 titulares / 182 andamio, porque `titular` no tiene definición operativa en el repo». El propio informe se contradice (un hallazgo lleva `medido:false`). Es exactamente [[feedback-estimacion-sin-etiqueta]].

(2) ⛔ EL TITULAR DEL HALLAZGO 1 DICE «223 titulares entregados fuera de la tabla». Contradice su propio §6 (41 titulares + 182 andamio) y es la parte cuasi‑vacua del informe. Debe decir: «223 NOMBRES IMPRESOS fuera de la tabla; de ellos 15 con cifra ya publicada o control M-11 afectado».

(3) ⭐ FALTA EL «ANTES DE CONSTRUIR, BUSCAR». El [G] propuesto ya existe como patrón en este repo: `check-warnings.bash` (ADR-060) hace exactamente eso — lee la salida real del build, la compara con una tabla declarada y rompe en los DOS sentidos. El control nuevo debe escribirse como HERMANO de ése (misma estructura de tabla, misma política de romper hacia abajo), no de cero. Y hay un dividendo que el informe no vio y que refuerza su tesis: `check-warnings.bash:13` afirma «⭐ Rompe en LOS DOS SENTIDOS, como `check-footprints`» — esa comparación es FALSA en el sentido que aquí importa, y es una cabecera que hay que corregir (cae además dentro del encargo A1).

(4) ⚠️ ÁMBITO DE LA MEDICIÓN, que no está escrito. Las cifras salen de `scratchpad/axioms_fol.txt` y `axioms_rpp.txt`, ambas de 2026‑09‑18 18:36 y con líneas «Replayed» (caché), producidas por un build que el propio auditor dice NO haber ejecutado. La PRESENCIA/AUSENCIA de nombres está contrastada contra el fuente de hoy y es sólida; los VALORES (net-0, `[propext, Quot.sound]`, el `raa`) no los ha re‑medido nadie en esta pasada. Toda cifra de footprint debe ir con «medido sobre la captura de 18:36, no re‑ejecutado» (M‑13).

(5) Tres deslices de cita, cosméticos pero que hay que arreglar porque el proyecto cita por fichero:línea:
   · `FOL/Eq.lean:417/396/29` no existe; es `FOL/Theorems/Eq.lean` (líneas correctas).
   · `evalTerm_updateFunc` NO tiene su footprint publicado «por nombre»: REFERENCE.md:582 publica la cifra describiéndolo («el lema de coincidencia, sin axiomas») y REFERENCE.md:766 lo nombra sin cifra. Sigue siendo del grupo G1, pero por una vía más débil.
   · `d3_prf_real`: doc/REFERENCE-Incompleteness.md:5353 dice «Footprint de `d3_prf_real` = la base sancionada», que es publicación INDIRECTA, no una cifra literal.

(6) 🔑 LO QUE HAY QUE LLEVARSE AL PLAN, en este orden: (a) el control [G] hermano de `check-warnings`; (b) `derives_completo` en la tabla HOY, porque es el único titular del ecosistema con un axioma del proyecto y nadie lo vigila; (c) cerrar las dos familias que la doc publica ENTERAS (Prenex0 4 que faltan, Eq0 2); (d) `LKh.rec` y la decisión sobre `TermG.rec`/`FormulaG.rec`, que es el punto más reciente y el único módulo sin control ninguno; (e) escribir en la cabecera del script cuál es su ÁMBITO — hoy declara 143 nombres de FOL y 4 de RPP y no lo dice en ninguna parte, que es la razón por la que el 175 de RPP parece un fallo y no lo es.

---

### A3 · El CHANGELOG de mayo y el control `[E]` DESARMADO
**Veredicto del informe:** `CONFIRMADO` · **¿sobrevive a la refutación?** **SÍ**

**Resumen:** El control [E] de FOL compara la fecha del titular de nueve documentos contra la fecha más reciente que aparezca en CHANGELOG.md, y ese CHANGELOG lleva 125 días congelado en 2026-05-16 con 111 commits por detrás: hoy [E] aprueba los nueve por márgenes de 57 a 120 días y no puede fallar salvo que un titular retroceda a mayo.

#### Cifras

MEDIDO, todo leyendo el árbol en solo lectura (ni un `lake`):
· Qué compara [E] (check-doc-sync.bash:240-263): NEWEST = máximo lexicográfico de TODAS las fechas ISO que aparezcan en CHANGELOG.md (grep -ohE sobre el fichero entero, sort -r, head -1). HEAD_DATE(d) = máximo ISO de las 12 PRIMERAS líneas de cada doc de AUTHORITATIVE. Avisa si HEAD_DATE < NEWEST (comparación de CADENAS, `test \<`). Son 9 documentos: REFERENCE.md, CURRENT-STATUS-PROJECT.md, DEPENDENCIES.md, DECISIONS.md, README.md, AXIOMS.md, NEXT-STEPS.md, AI-GUIDE.md, cuarentena/README.md. [E] es AVISO: E_HITS nunca pone FAIL=1.
· NEWEST hoy, reproducido con la línea exacta del script: 2026-05-16. Fechas presentes en el CHANGELOG: 2026-05-16, 2026-05-08, 2026-04-25, 2026-04-20.
· CHANGELOG.md: 126 líneas, 6 596 bytes, mtime may. 28; último commit que lo tocó, 2026-05-16. Última entrada `### Added (2026-05-16)` (línea 13), cabecera `**Last updated:** 2026-05-16` (línea 3).
· Commits de FOL desde entonces: 111 (`git log --oneline --since=2026-05-16 | wc -l`), sobre 177 del repo. Hueco temporal 2026-05-16 → 2026-09-18 = 125 días.
· HEAD_DATE de los nueve docs: 09-12, 09-12, 07-12, 07-12, 09-12, 09-13, 09-12, 07-12, 09-11. Margen mínimo frente a NEWEST: 57 días (2026-07-12 − 2026-05-16); máximo: 120 días (2026-09-13).
· Simulación con NEWEST=2026-09-18: E_HITS = 9 de 9.
· Ficheros .lean nuevos en FOL/ desde 2026-05-16: 25 módulos `*0.lean`/nuevos (Craig0, BlockExtraction0, SkolemHerbrand0, SkolemNF0, SkolemN0, PrenexNF0, Prenex0, Skolem0, HerbrandBlock0, Compacity0, Finitary0, Hauptsatz0, NDtoLK0, SequentSound0, Sequent0, Derives2, Derives1, Herbrand0, DecEq, Propositional0, Canonical0, Eq0, Lindenbaum0, Fresh0, HenkinLimit0, Henkin0, Lift0, Eigenvariable, Rename, Soundness0, Derives0, Enumeration, Core) más cuarentena/Inconsistencia.lean.
· Estado del árbol hoy, con las mismas fórmulas del script: CORE=40, THEO=6, TFW=6 ⇒ ACTIVE=52; QUAR=5; AXIOMS=4 (`imp_intro`, `raa`, `or_elim`, `ex_elim`, los cuatro en FOL/MetaRules.lean).
· NO MEDIDO por mí: la cifra de jobs de FOL (53, memoria) y el `sorry` (se delega en check-sorry.bash, que no he ejecutado). Van sin sello.

#### Hallazgos

* **[alta]** [E] toma su patrón de referencia de un fichero que NINGÚN control audita
  · *Evidencia:* E:/dropbox/github/lean4/FOL/check-doc-sync.bash:240 — `NEWEST=$(grep -ohE "20[0-9]{2}[-‑][0-9]{2}[-‑][0-9]{2}" CHANGELOG.md 2>/dev/null | sed "s/‑/-/g" | sort -r | head -1)`; y línea 130 del mismo fichero: «CHANGELOG.md se excluye: es un diario, sus cifras son históricas por diseño». CHANGELOG.md no está en AUTHORITATIVE (líneas 113-114), y [D] (líneas 383-388) sólo mira REFERENCE/CURRENT-STATUS/DEPENDENCIES y sólo comprueba que EXISTA la marca, no que sea fresca.

* **[alta]** El CHANGELOG está congelado en 2026-05-16 con 111 commits por detrás
  · *Evidencia:* E:/dropbox/github/lean4/FOL/CHANGELOG.md:3 — `**Last updated:** 2026-05-16`; línea 13 — `### Added (2026-05-16)` es la entrada más reciente. `git log --oneline --since=2026-05-16 | wc -l` en E:/dropbox/github/lean4/FOL → 111. Último commit del fichero: `git log -1 --format=%ad --date=short -- CHANGELOG.md` → 2026-05-16.

* **[alta]** Caso concreto: CURRENT-STATUS-PROJECT.md tiene el titular fechado el 09-12 y el cuerpo movido el 09-18, y [E] lo aprueba
  · *Evidencia:* E:/dropbox/github/lean4/FOL/CURRENT-STATUS-PROJECT.md:2 — `> # ⛔⛔ AVISO DE ESTADO — 2026‑09‑12. LEER ANTES QUE NADA`. Su HEAD_DATE calculado con la misma línea del script (head -12 + regex ISO) es 2026-09-12; `git log -- CURRENT-STATUS-PROJECT.md` muestra seis commits posteriores (2026-09-17 c4abeaa, fc12381; 2026-09-18 f598062, 3252adc, 27a7c87, 78bbdfe). La comparación de check-doc-sync.bash:247, `[ "$HEAD_DATE" \< "$NEWEST" ]`, es `2026-09-12 < 2026-05-16` → FALSO ⇒ no avisa.

* **[alta]** Ningún titular puede disparar [E] hoy: el margen mínimo es de 57 días
  · *Evidencia:* Reproducido el bucle de check-doc-sync.bash:243-251 en solo lectura sobre los nueve docs de AUTHORITATIVE: REFERENCE.md 2026-09-12, CURRENT-STATUS-PROJECT.md 2026-09-12, DEPENDENCIES.md 2026-07-12, DECISIONS.md 2026-07-12, README.md 2026-09-12, AXIOMS.md 2026-09-13, NEXT-STEPS.md 2026-09-12, AI-GUIDE.md 2026-07-12, cuarentena/README.md 2026-09-11. Todos > 2026-05-16 ⇒ E_HITS=0 y se imprime check-doc-sync.bash:254 «✓ ningún titular se ha quedado atrás del CHANGELOG ($NEWEST)».

* **[media]** Datar el CHANGELOG REARMA el control y los nueve documentos salen en rojo de aviso
  · *Evidencia:* Misma simulación con NEWEST=2026-09-18: los nueve avisan (E_HITS=9), incluidos DEPENDENCIES.md, DECISIONS.md y AI-GUIDE.md, con titular 2026-07-12 y 111 commits desde entonces. ⚠️ No rompe el check: E_HITS no toca FAIL en ningún punto (los únicos `FAIL=1` están en las líneas 126, 178, 378, 389 y 426 de check-doc-sync.bash, ninguna en el bloque [E], líneas 230-263).

* **[baja]** El registro de ADR que citan los commits de FOL no vive en FOL
  · *Evidencia:* E:/dropbox/github/lean4/FOL/DECISIONS.md: `grep -n "^## ADR-0"` llega a `## ADR-010: Cinco sub-librerías independientes, no una jerarquía de extensión` (línea 178, fichero de 226 líneas). Los ADR-030…ADR-068 que citan los commits de FOL están en E:/dropbox/github/lean4/ROBINSON_PlusPlus/DECISIONS.md (p. ej. línea 5414: `## ADR-068: 🏁 el TIPO DE LOS SÍMBOLOS es un PARÁMETRO`). Relevante para redactar el CHANGELOG sin inventar referencias.

* **[baja]** `maehara_eq` no existe en el árbol de FOL: la entrada del 09-18 no debe anunciarlo
  · *Evidencia:* `grep -n maehara E:/dropbox/github/lean4/FOL/FOL/Craig0.lean` sólo da `maehara` (líneas 22, 319, 805, 845). El anuncio está rectificado en E:/dropbox/github/lean4/ROBINSON_PlusPlus/sondeos/CraigEqVacuo.lean:12 — «Este fichero es la EVIDENCIA de que el `maehara_eq` anunciado en ADR-066 §2».

#### Acción propuesta

ACCIÓN. (a) No es un arreglo puntual de una línea: datar el CHANGELOG REARMA [E] y entonces los NUEVE documentos avisan (medido), así que la pasada es «datar + revisar nueve titulares». (b) Y hay un control [G] que escribir, porque el defecto es estructural: [E] toma su patrón de referencia de un fichero que ningún control audita — es el patrón «referencia inauditada», hermano de las nueve causas ya medidas. [G] propuesto, barato y objetivo: `fecha más reciente del CHANGELOG >= fecha del último commit que toca *.lean` (o `>= hoy − N días`); si no, ROJO — no aviso. Nada en check-doc-sync.bash lo hace hoy ([D], líneas 383-388, sólo comprueba que la marca EXISTA, y CHANGELOG.md está excluido en la línea 130). (c) Ojo al redactar: los ADR-030…068 no están en DECISIONS.md de FOL (llega a ADR-010) sino en el de ROBINSON_PlusPlus, y `maehara_eq` NO existe en FOL/Craig0.lean.

=== TEXTO LISTO PARA PEGAR (también en C:\msys64\tmp\claude\e--dropbox-github-lean4-ROBINSON-PlusPlus\85b0df6c-1e14-407d-a9ae-04b9e8841ed5\scratchpad\CHANGELOG-FOL-parche.md) ===

--- PARCHE 1 — CHANGELOG.md línea 3, sustituir ---
**Last updated:** 2026-09-18

--- PARCHE 2 — insertar íntegro entre la línea 11 («## [Unreleased]») y la 13 («### Added (2026-05-16)») ---

> ⚠️ **Las entradas desde 2026-05-28 se redactan a posteriori (2026-09-18)** a partir del
> `git log` de este repositorio: el CHANGELOG estuvo congelado en 2026-05-16 mientras
> entraban **111 commits**. Eso desarmó el control `[E]` de `check-doc-sync.bash`, que
> compara la fecha del titular de cada documento autoritativo contra la fecha más reciente
> del CHANGELOG.
> ⛔ El registro de decisiones que citan estos commits **no vive en este repo**:
> `DECISIONS.md` de FOL llega a ADR-010; ADR-030 … ADR-068 están en `DECISIONS.md` de
> ROBINSON_PlusPlus.

### Added (2026-09-18)

- **`FOL/Craig0.lean`** — MAEHARA y la INTERPOLACIÓN DE CRAIG para `LKp` (ADR-063):
  - `maehara`, `craig`, `craig_impl`, `lkp_to_lk0`, `predF_lift`, `predF_subst`, `lkp_example`.
  - ⚠️ El `maehara_eq` relativizado a `E` que ADR-066 §2 anunciaba **no existe en este árbol**:
    ADR-067 lo midió VACUO (evidencia compilada en `ROBINSON_PlusPlus/sondeos/CraigEqVacuo.lean`).
- **`FOL/BlockExtraction0.lean`** — la mitad ⟹ de HERBRAND DE BLOQUE (ADR-064):
  `instB_nil`, `instB_snoc`, `quantFree_of_blockInv`, `lk0_herbrand_block`,
  `herbrandExtractionBlock_of`, `herbrand_extraction_block`, `herbrand_block`.
- **`FOL/SkolemHerbrand0.lean`** — el ENCHUFE Skolem↔Herbrand (ADR-066): las dos piezas no
  componían. `impAll_neg_allBlock`, `impAll_ex_neg_not_forall`, `derives0_neg_allBlock_iff`,
  `herbrand_of_skolemNF`.
- **`FOL/SkolemNF0.lean`** — la dirección ⟹ de Skolem (ADR-065), y sale **sin
  `Classical.choice`**: `derives0_skolemize`, `derives0_skolemize_iff`, `derives0_allBlock_mp`,
  `allBlock_forall`.

### Changed (2026-09-18)

- **El tipo de los SÍMBOLOS pasa a ser un PARÁMETRO** (ADR-068) — `FOL/FOL.lean`, `FOL/DecEq.lean`:
  - `TermG (S : Type)` / `FormulaG (S : Type)` son el núcleo genérico, con
    `abbrev Term := TermG String` y `abbrev Formula := FormulaG String`; constructores e
    `injEq` se reexportan con `export`. **El resto del árbol no cambió ni una línea.**
  - Coste MEDIDO: **tres ficheros** (estos dos y `ROBINSON_PlusPlus/Meta/HilbertSeq.lean`),
    ~40 líneas, y los 147 footprints idénticos. La estimación escrita («163 módulos /
    3 902 declaraciones») era falsa por un factor ≈50: medía el ALCANCE del tipo, no el TRABAJO.
  - ⛔ Nada del árbol es genérico todavía: faltan las clases `FreshSym` y `EnumSym`.

### Added (2026-09-17)

- **EL HAUPTSATZ** — `FOL/NDtoLK0.lean` y `FOL/Hauptsatz0.lean` (ADR-049/050/051/052):
  - `ndToLK`, `mpLK`, `viaEqImpl`, `herbrandExtraction_of_cutElim`; entra la regla `eqAx`.
  - `LKh`, `lkh_mono`, `lkh_to_lk0`, `lk0_to_lkh`, `lkh_subst`, `lkh_lift`, `eqInstance_subst`,
    `eqInstance_lift`, `cutPrinAux`, `cutLeftAux`, **`hauptsatz`**, `cut_elimination`,
    `herbrand_extraction`, `herbrand`.
- **`FOL/Finitary0.lean`** (ADR-053, y su **RECTIFICACIÓN**: el Hauptsatz NO hacía falta) — la
  consistencia de `Derives₀` **sin `Classical.choice`**: `tval_eqInstance`, `lk0_tval`,
  `lk0_empty`, `lk0_no_bot`, `lkc_tval`, `lkc_empty`, `lkc_no_bot`, `lk0_empty_of_no_bot`,
  `lkc_empty_of_no_bot`, `lk0_not_empty_fin`, `lkc_not_empty_fin`, `derives0_consistent_fin`,
  `derives0_not_P_fin`.
- **`FOL/Compacity0.lean`** (ADR-054) — COMPACIDAD y LÖWENHEIM-SKOLEM DESCENDENTE:
  `consistency_of_satisfiable₀`, `compactness₀`, `model_existence_countable₀`,
  `loewenheim_skolem_down`.
- **`FOL/HerbrandBlock0.lean`** (ADR-055) — Herbrand para un BLOQUE de existenciales, mitad ⟸:
  `subst_exBlock`, `derives0_exBlock_of_inst`, `derives0_exBlock_of_disj`,
  `derives0_exBlock_of_cert`, `ex_bloque_igualdad`.
- **`FOL/Skolem0.lean`** (ADR-056, ampliado por ADR-059) — el axioma de Skolem/Henkin es
  CONSERVATIVO: `evalTerm_updateFunc`, `evalFormula_updateFunc`, `evalTerm_new`,
  `skolem_conservative`, `henkin_conservative`. ADR-059 lo pasa a término de argumentos fijos.
- **`FOL/Prenex0.lean`** (ADR-057) — la CAPA PRENEXA sobre `Derives₀`, las ocho equivalencias:
  `and_forall`, `and_ex`, `or_forall`, `or_ex`, `impl_forall_left`, `impl_ex_left`,
  `impl_forall_right`, `impl_ex_right`.
- **`FOL/PrenexNF0.lean`** (ADR-058, con su §4 SALDADO) — la FORMA NORMAL prenexa:
  `mergeAnd_iff`, `mergeImpl_iff`, `prenex_iff`, `derives0_prenex_iff`, `quantFree_lift`,
  `prenex_isPrenex` (la salida de `prenex` **está** en forma prenexa).
- **`FOL/SkolemN0.lean`** (ADR-060) — SKOLEM bajo un prefijo `∀ⁿ`: `not_occurs_vars`,
  `eval_allBlock_envPush`, `evalTerms_vars`, `eval_skolemAxN`, `skolem_conservative_n`.
- **`FOL/SkolemNF0.lean`** (ADR-062) — LA FORMA NORMAL DE SKOLEM: `qdepth_subst`,
  `skolemizeF_shape`, `skolemizeF_impAll`, `occursFormula_lift`, `occurs_prenex`,
  `skolem_conservative_nf`, `derives0_of_skolemNF`, `skolemNF_shape`.
- **`check-doc-sync.bash`** (ADR-061) — portado desde ROBINSON_PlusPlus; en su PRIMERA
  ejecución encontró nueve desfases vivos desde mayo.
- **`.github/workflows/build.yml`** — FOL vuelve a tener CI: no la tenía desde mayo, y las dos
  veces que corrió falló en 0 s.

### Fixed (2026-09-17)

- **CI**: el paso del toolchain se endurece contra el CRLF (`tr -d`).
- **CI + `check-sorry.bash`**: el gate de `sorry` pasa a ser BLOQUEANTE. El árbol estaba a
  cero — **el roto era el control**.

### Added (2026-09-16)

- 🏁 **COMPLETITUD DE FOL⁼, DEMOSTRADA** — el ensamblaje de Henkin, cerrado:
  - `FOL/Fresh0.lean` + `FOL/HenkinLimit0.lean` (ADR-039): `cst_bound_formula`,
    `derivesSet0_shift_inv`, `shiftTheory_consistent`, `exists_fresh`; `not_occurs_henkinAx`,
    `hen_consistent`, `henLimit_consistent`, `henLimit_witness`.
  - `FOL/Lindenbaum0.lean` (ADR-040): `derivesSet0_intro_impl`, `lindenbaum_lemma`,
    `max_cons_contains`, `henkin_completion`.
  - `FOL/Canonical0.lean` + `FOL/Eq0.lean` (ADR-041): `truth_lemma`, `eval_pullback_formula`,
    `model_existence_lemma₀`, **`completeness₀`**, `derives0_complete_iff`, `derives0_em`,
    `derives0_peirce`; `derives0_eq_symm`, `derives0_eq_trans`, `derives0_eq_func_congr`,
    `derives0_atom_congr`. **Cero axiomas propios.**
- **La VÍA H (finitaria)**:
  - `FOL/DecEq.lean` + `FOL/Propositional0.lean` (ADR-042): la completitud PROPOSICIONAL —
    `instDecidableEqTerm`, `instDecidableEqFormula`; `derives0_em_ctx`, `kalmar`, `elim_atoms`,
    `derives0_of_ptaut`, `derives0_of_ptaut_ctx`, `derives0_peirce_prop`.
  - `FOL/Herbrand0.lean` (ADR-043): el CERTIFICADO de Herbrand — `ptaut_of_check`,
    `derives0_discharge`, `derives0_of_eqInstance`, `derives0_ex_of_cert`, `herbrand_iff`,
    `ex_tercio`, `ex_igualdad`. H3 queda **enunciada, no postulada**.
  - `FOL/Derives1.lean` (ADR-044): `rewrite_at` es ADMISIBLE — `rewrite_equiv`,
    `rewrite_at_admissible`, `derives0_to_derives1`, `derives0_iff_derives1`.
  - `FOL/Derives2.lean` (ADR-045): `subst` es ADMISIBLE — `derives2_lift`, `eq_substTerm`,
    `eq_substFormula`, `derives1_to_derives2`, `derives0_iff_derives2`.
  - `FOL/Sequent0.lean` (ADR-046): el CÁLCULO DE SECUENTES — `LK₀`, `lk0_herbrand`,
    `lk0_to_lkc`, `herbrandExtraction_of`.
  - `FOL/SequentSound0.lean` (ADR-048): `LK₀` no prueba de más — `lkc_sound`, `lk0_sound`,
    `lk0_to_derives0`, `lk0_to_derives2`, `lk0_not_empty`.

### Fixed (2026-09-16)

- **`FOL/Semantics.lean`**: un `omega` sobre un caso imposible metía `Classical.choice`.
  Verificado y corregido.

### Added (2026-09-14)

- **`FOL/Derives0.lean`** (ADR-033, Paso 0) — `Derives₀`, el cálculo sobre el que la metateoría
  SÍ significa algo: sin ω-regla ni los cuatro axiomas ⇒ cero habitantes-axioma.
  `derives0_to_derives`, `derives0_raa`.
- **`FOL/Soundness0.lean`** (ADR-034, Paso 1) — el repo tiene por fin un cálculo de FOL⁼
  SÓLIDO: `derives0_soundness`, `derives0_consistent`, `derives0_not_complete`.
- **`FOL/Rename.lean`** (ADR-035) — `derives0_rename`, y es CONSTRUCTIVA; más la recíproca
  (conservatividad, sin inducción nueva): `derives0_rename_inv`, `derives0_rename_iff`,
  `derives0_rename_conservative`.
- **`FOL/Eigenvariable.lean`** (ADR-036) — el paso de EIGENVARIABLE: `absDerives`,
  `derives0_gen_fresh`, `derives0_inst_fresh`.
- **`FOL/Henkin0.lean`** + **`FOL/Lift0.lean`** (ADR-037) — `henkin_step_consistent`, el corazón
  de Henkin (el ensamblaje, no); `derives0_lift`, `derives0_ex_forall_neg_absurd`.

### Changed (2026-09-14)

- **`FOL/Theorems/Eq.lean`**: medida la causa de `Classical.choice` — FOL pasa **de 26 a 16**
  declaraciones que lo arrastran.
- **`FOL/Theorems/Eq.lean`**: corregida la regla sobre `omega` que quedó DEMASIADO GENERAL.

### Added (2026-09-13)

- **`FOL/Enumeration.lean`** (ADR-030) — la enumerabilidad de `Formula` deja de ser un postulado.
- **`FOL/Theorems/Eq.lean`** (ADR-031) — las dos congruencias de la igualdad, DEMOSTRADAS: la
  Completitud de `cuarentena/Completeness.lean` queda a UN postulado (de cinco axiomas a uno).

### Changed (2026-09-13)

- **ADR-032 CERRADO, opción (A)**: `henkin_extension_lemma` **SE QUEDA**. Se midió que sale —
  «es el caro» era FALSO— pero pagarlo metería `raa` y la Henkin saldría de la patología, no de
  la lógica. Queda protegido: `check-axioms.bash` rompe **también si la cuenta baja**.

### Removed (2026-09-12)

- **Tres `lean_lib` RETIRADAS** a `cuarentena/librerias-retiradas/` (D-1): `FOLPure`,
  `PropLogic` y `FOL_poli`. Medido: cero consumidores, cero artefactos de compilación, y
  `FOL_poli/FOL.lean` era **byte-idéntico** a `FOL/FOL.lean`. Estaban en el peor estado
  posible: declaradas (⇒ su salida en el `LEAN_PATH` de ROBINSON_PlusPlus), con 15 de los 28
  axiomas del repo, y **nunca compiladas** — la causa raíz de que un `axiom` FALSO sobreviviera
  ahí 80 días.
- **`FOL/Completeness.lean`** pasa a `cuarentena/Completeness.lean`.

### Changed (2026-09-12)

- **De 13 `axiom` a 4** (D-2…D-5). Los cuatro que quedan están en `FOL/MetaRules.lean`:
  `imp_intro`, `raa`, `or_elim`, `ex_elim`.
- **`TheoryFramework` entra de verdad en el build** (A-5): `@[default_target]` y
  ``globs := #[.submodules `TheoryFramework]``. Estaba declarada sin `default_target`, así que
  **nunca se compilaba**, y su `Instances/FOL.lean` llevaba meses roto y huérfano
  autodescribiéndose «fully complete and verified».
- **`FOL/Core.lean`** (nuevo, D-4): el núcleo sintáctico — exactamente lo que
  ROBINSON_PlusPlus consume.
- **`substFormula_liftFormula`** baja a FOL (R-4): estaba **tres veces** en ROBINSON_PlusPlus.
- **`cuarentena/` NO era efectiva**, y el censo de habitantes estaba MAL (5 → 12).
- **`git-lock`** deja de apuntar a la cadena `an` y protege lo que importa (D-5).
- **`FOLPure` y `FOL_poli`**: propagada por fin la corrección de junio del `axiom` FALSO.
- Nuevos: **`AXIOMS.md`** y **`check-axioms.bash`**.

### Fixed (2026-09-11)

- ⛔⛔ **`soundness` es FALSO** en presencia de `FOL/MetaRules.lean`: con `raa` demuestra
  `False` **sin hipótesis**. `FOL/Soundness.lean`, `FOL/Compacity.lean` y
  `FOL/Theorems/Soundness.lean` pasan a `cuarentena/`; se añaden
  `cuarentena/Inconsistencia.lean` (la evidencia, **compilada**) y `cuarentena/README.md`.
- **`gen` NO es la ω-regla**: corregido su docstring.

### Changed (2026-07-12)

- Se adopta la plantilla unificada de gobernanza: `AI-GUIDE.md`, `NAMING-CONVENTIONS.md`,
  `DECISIONS.md` y `DEPENDENCIES.md`. Las dos últimas eran aún la plantilla genérica de
  `lean4-project-template` sin adaptar (título «ProjectName» literal, ejemplos ficticios)
  pese a que el proyecto real tenía 5 `lean_lib` y ~70 ficheros `.lean`.

### Changed (2026-07-04)

- Toolchain a `leanprover/lean4:v4.31.0` (estable más reciente; iguala a ROBINSON_PlusPlus).

### Added (2026-06-24)

- **`FOL/Theorems/Eq.lean`**: lema de sustitución de Barendregt (`subst_subst_comm_succ`),
  niveles consecutivos.

### Added (2026-06-23)

- **`FOL/Theorems/Eq.lean`**: composición subst-subst-lift generalizada por niveles (De Bruijn),
  y conmutación subst/lift a nivel fórmula (`substFormula_lift_comm`).

### Fixed (2026-06-23)

- **`FOL/Theorems/Quantifiers.lean`**: `subst_lift_cancel_formula` era un `axiom` **FALSO** —
  pasa a teorema en su forma restringida verdadera.

### Added (2026-06-13)

- **`FOL/MetaRules.lean`**: `dne` — eliminación de doble negación (lógica clásica).

### Added (2026-06-12)

- **`FOL/MetaRules.lean`** (nuevo): meta-reglas ω de deducción, extraídas de ROBINSON_PlusPlus.
- **`FOL_poli.lean`** y **`ENGARCE-ROBINSON-FOL.md`**: meta-axiomas de ω-lógica.
  ⚠️ `FOL_poli` fue RETIRADA el 2026-09-12 (ver arriba).

### Added (2026-06-09)

- **`FOL_poli/`** (nueva `lean_lib`): clon polimórfico de la semántica de FOL para soportar
  universos superiores — `FOL.lean`, `Semantics.lean`, `Deduction.lean`, `Soundness.lean`,
  `Completeness.lean`, `Compacity.lean`, `Classical.lean`, `Tactics.lean`, `Tactics2.lean` y
  `Theorems/` (7 módulos). ⚠️ RETIRADA el 2026-09-12: su módulo raíz era **byte-idéntico** al
  de `FOL/` y **nunca se compilaba**.

### Changed (2026-06-06)

- **`FOL/Theorems/Eq.lean`**: eliminado el argumento `simp` `hne`, no usado, en
  `substTerm_liftLift`.

### Added (2026-05-28)

- **Modelo COCIENTE en `FOL/Completeness.lean`**: se reimplementa para dejar FOL con igualdad
  «100 % sorry-free», y se fusionan las ramas `agents/investigacion-situacion-proyecto` y la
  rama de trabajo del asistente.
  ⛔⛔ **RECTIFICADO el 2026-09-11/12**: esa completitud pasaba por `soundness`, que es FALSO
  en presencia de `FOL/MetaRules.lean`. El módulo está hoy en `cuarentena/Completeness.lean`.
  La completitud de verdad es `completeness₀` (2026-09-16, ADR-041).
- **`FOL/Theorems/Eq.lean`**: restaurados `substTerm_lift_comm` y `substTerm_liftLift`.

#### ⚖️ La refutación

SOBREVIVE el núcleo, y lo he intentado tumbar reproduciendo cada cifra en solo lectura (ni un `lake`).

QUÉ SOBREVIVE, exactamente:
1. La descripción de [E] es literal. `E:/dropbox/github/lean4/FOL/check-doc-sync.bash:240` es la línea `NEWEST=$(grep -ohE ... CHANGELOG.md ... | sort -r | head -1)`; `AUTHORITATIVE` en 113-114 (los nueve docs, `DOCS="$AUTHORITATIVE"`); la exclusión «CHANGELOG.md se excluye: es un diario» en la línea 130; [D] en 384-388 sólo comprueba que EXISTA `**Last updated:**` en tres ficheros. Confirmado.
2. NEWEST reproducido con la línea exacta del script → 2026-05-16, y las únicas fechas del fichero son 2026-05-16, 2026-05-08, 2026-04-25, 2026-04-20. CHANGELOG.md: 126 líneas, 6 596 bytes; `git log -1 --format=%ad --date=short -- CHANGELOG.md` → 2026-05-16. Confirmado.
3. Los nueve HEAD_DATE, reproducidos con `head -12 | grep -ohE ISO | sort -r | head -1`, salen IDÉNTICOS a los publicados: REFERENCE 09-12, CURRENT-STATUS 09-12, DEPENDENCIES 07-12, DECISIONS 07-12, README 09-12, AXIOMS 09-13, NEXT-STEPS 09-12, AI-GUIDE 07-12, cuarentena/README 09-11 ⇒ E_HITS=0. Márgenes 57 y 120 días: aritmética correcta.
4. `git log --oneline --since=2026-05-16 | wc -l` → 111, y 177 en total. Comprobé además que `--since=2026-05-16 --until=2026-05-17` da 0, así que el 111 no infla contando commits del propio día.
5. [E] NO puede romper el check: los `FAIL=1` están en 126, 178, 378, 389 y 426; ninguno en el bloque [E] (230-263). Incluso la rama de error («no pude leer la fecha … control VACÍO») sale sin FAIL. Confirmado, y es el punto más fuerte del hallazgo.
6. Los conteos del árbol con las fórmulas literales del script: CORE=40, THEO=6, TFW=6 ⇒ ACTIVE=52; QUAR=5; AXIOMS=4, los cuatro en `FOL/MetaRules.lean` (78 `imp_intro`, 110 `raa`, 145 `or_elim`, 159 `ex_elim`). Confirmado.
7. Los dos hallazgos «baja»: `grep -n maehara FOL/Craig0.lean` da sólo `maehara` (22, 319, 805, 845) — `maehara_eq` NO está; `DECISIONS.md` de FOL llega a `## ADR-010` (línea 178 de 226). Confirmado.

LENTE DE VACUIDAD (la aplico en serio): el hallazgo NO es vacuo. Lo VACUO es el control [E], no la afirmación sobre él: si el CHANGELOG estuviera datado hoy, [E] avisaría de los nueve (simulación trivialmente cierta: el máximo HEAD_DATE es 09-13 < 09-18). El hallazgo es contingente del estado del árbol y cambiaría si el CHANGELOG se mantuviera. Pasa la lente.

REFUERZO que el auditor no midió y yo sí (no cambia el veredicto, lo agranda): el MISMO [E] sin referencia auditada está en `ROBINSON_PlusPlus/check-doc-sync.bash:246`; su CHANGELOG está en 2026-09-11 (7 días). El defecto estructural es de los DOS repos, y ningún `check-*.bash` de ninguno de los dos comprueba la frescura del CHANGELOG (regla «antes de construir, buscar»: verificado, el [G] propuesto no existe ya).

DOS PEGAS, ninguna fatal:
(a) CIFRA MAL SELLADA. «25 módulos *0.lean/nuevos desde 2026-05-16» va como MEDIDO y se contradice con su PROPIA lista (33 nombres) y con el árbol: `git log --diff-filter=A --since=2026-05-16 --name-only -- '*.lean'` da 34 ficheros nuevos bajo `FOL/`, más `cuarentena/Inconsistencia.lean`, más 18 de `FOL_poli/` (añadidos en junio y retirados el 09-12). Es contexto, no sostiene el hallazgo, pero es exactamente el fallo que el proyecto persigue: un número sin reproducir viajando con sello.
(b) EL TEXTO PARA PEGAR no está medido en su mayor parte y no lo declara. El auditor sólo marcó «NO MEDIDO» la cifra de jobs y el sorry; sin embargo el parche afirma «los 147 footprints idénticos», «las dos veces que corrió falló en 0 s», «FOL pasa de 26 a 16 declaraciones con Classical.choice» y inventarios completos de símbolos por ADR, todo heredado de los ADR de RPP, no comprobado contra el árbol. Es un BORRADOR, no una medición.

**Lo correcto:**

Sobrevive. Al aplicarlo, tres correcciones:

1. Sustituir «25 módulos» por la cifra reproducible: 34 ficheros `.lean` nuevos bajo `FOL/` desde 2026-05-16 (más `cuarentena/Inconsistencia.lean`; y 18 de `FOL_poli/`, añadidos en junio y retirados el 09-12). Comando: `git log --diff-filter=A --since=2026-05-16 --name-only --pretty=format: -- '*.lean' | sort -u`.

2. El TEXTO PARA PEGAR entra al repo como BORRADOR con su procedencia dicha: sus inventarios de símbolos y sus cifras («147 footprints», «de 26 a 16», «falló en 0 s») vienen de los ADR de ROBINSON_PlusPlus, no de una medición de esta auditoría. Antes de commitear, o se verifican con grep contra el árbol o se marcan como histórico citado.

3. Ampliar el alcance: el [G] propuesto hay que escribirlo en LOS DOS repos, no sólo en FOL. `ROBINSON_PlusPlus/check-doc-sync.bash:246` tiene el mismo [E] con la misma referencia inauditada (su CHANGELOG, a 2026-09-11, lo tiene hoy sólo 7 días atrás — latente, no disparado). Y el [G] debe ser ROJO, no aviso: el defecto medido aquí es precisamente que E_HITS nunca toca FAIL.

---

### A4 · La CI de RPP en 8d91989, por fin VISTA
**Veredicto del informe:** `CONFIRMADO` · **¿sobrevive a la refutación?** **SÍ**

**Resumen:** Los cinco runs de la CI de RPP (8d91989 y los cuatro vecinos) están VISTOS con `gh`: los cinco son `success`, primer intento, sin ningún paso en rojo — salen de la tercera categoría y pasan a VERDE MEDIDO; pero ese verde certifica un PAR (RPP@sha + FOL@master-flotante) y deja el job `libro` sin ejecutar ninguno de sus cuatro controles.

#### Cifras

MEDIDO con `gh run list`, `gh api .../actions/runs/<id>` y `gh run view <id> --job <jid> --log` (logs guardados en C:/msys64/tmp/claude/e--dropbox-github-lean4-ROBINSON-PlusPlus/85b0df6c-1e14-407d-a9ae-04b9e8841ed5/scratchpad/). Workflow unico: «Build» (.github/workflows/build.yml, el unico fichero en .github/workflows/). Horas en UTC; el commit local va en +0200.

commit | run id | conclusion | creado → fin (UTC) | duracion | FOL usado | jobs RPP/FOL | footprints
b787d9d | 35248747949 | success (attempt 1) | 2026-09-17 16:47:25 → 16:51:12 | 3 min 47 s | 4130faa | 145 / 50 | 132
8d91989 | 35320579707 | success (attempt 1) | 2026-09-18 07:40:43 → 07:44:48 | 4 min 05 s | d3a51f1 | 145 / 51 | 138
37ec0e4 | 35324176741 | success (attempt 1) | 2026-09-18 08:24:03 → 08:29:45 | 5 min 42 s | 90f01e9 | 145 / 52 | 142
b22dd85 | 35329338284 | success (attempt 1) | 2026-09-18 09:24:06 → 09:28:14 | 4 min 08 s | 04e2632 | 145 / 52 | 145
5884ffa | 35337367895 | success (attempt 1) | 2026-09-18 10:59:07 → 11:04:45 | 5 min 38 s | 404e2cd | 145 / 53 | 147

De propina, los dos posteriores (no pedidos, medidos igual): d85df4a → run 35353344724, success, 13:58:12→14:02:47 UTC, 4 min 35 s, 147 footprints; 2a9e88c → run 35357631645, success, 14:39:51→14:45:44 UTC, 5 min 53 s, 147 footprints. Los dos con 145/53 jobs y «✅ LOS 11 WARNINGS CUADRAN.».

Controles que SI se ejecutaron en los cinco (salida literal del log): «✅ No sorry found.» · «✅ LOS 10 ESTRATOS CUADRAN.» · «✅ LOS <N> FOOTPRINTS CUADRAN.» · «✅ DOCUMENTACION SINCRONIZADA.» (+ «✅ LOS 11 WARNINGS CUADRAN.» desde b22dd85). Ningun `##[error]` en ningun log; el unico `##[warning]` es el de Node.js 20 deprecado en actions/cache@v4 y actions/checkout@v4, ajeno al proyecto.

LAS TRES CATEGORIAS (las de 255e007), commit a commit — NINGUNO por analogia con la CI de FOL, los cinco por lectura directa del run:
- 8d91989 → VERDE VISTO
- b22dd85 → VERDE VISTO
- 37ec0e4 → VERDE VISTO
- b787d9d → VERDE VISTO
- 5884ffa → VERDE VISTO
Ninguno cae en ROJO ni en «no he podido comprobarlo». No hubo ningun `run failed`, asi que el punto 3 del encargo (sacar `--log-failed`) queda sin objeto: NO SE MIDIO porque no habia nada que medir.

NO MEDIDO / limitacion: los logs de Actions caducan (retencion por defecto 90 dias). El par (RPP@sha, FOL@sha) que certifica cada verde solo consta AHI; pasada la retencion, esa cifra no es recuperable.

#### Hallazgos

* **[baja]** Los cinco commits: CONCLUSION success, attempt=1, ningun paso en rojo — categoria VERDE VISTO
  · *Evidencia:* gh api repos/julian1c2a/ROBINSON_PlusPlus/actions/runs/35320579707 → «35320579707 attempt=1 concl=success sha=8d91989 previous_attempt=» (idem 35248747949/b787d9d, 35324176741/37ec0e4, 35329338284/b22dd85, 35337367895/5884ffa). Log del job: C:/msys64/tmp/claude/e--dropbox-github-lean4-ROBINSON-PlusPlus/85b0df6c-1e14-407d-a9ae-04b9e8841ed5/scratchpad/run_35320579707.log:«Build completed successfully (145 jobs).» y «✅ LOS 138 FOOTPRINTS CUADRAN.»

* **[media]** El verde de RPP certifica un PAR, y el segundo miembro NO esta fijado: FOL entra por `ref: master`
  · *Evidencia:* E:/Dropbox/GitHub/lean4/ROBINSON_PlusPlus/.github/workflows/build.yml:41-42 «repository: julian1c2a/FOL» / «ref: master». Medido en el log: run_35320579707.log, salida de `git log -1 --format=%H` de los DOS checkouts → «8d91989b3fa4a079460b8960cb3e1749d2f799c7» y «d3a51f1a12e86c368e02af24b5bf0cb5d4e3657f» (= FOL d3a51f1 «lock: FOL.lean y FOL/Craig0.lean»). Un re-run hoy compilaria RPP@8d91989 contra FOL@HEAD-de-hoy: otra pregunta, otro verde.

* **[media]** El job `libro` esta en VERDE habiendo ejecutado CERO de sus cuatro controles, en los cinco runs
  · *Evidencia:* gh api .../jobs → job «libro · controles §2.1/§2.6/§2.7 [success]» con los pasos 6..12 (`Set up Python`, `Install TeX Live`, §2.6, §2.7, `Compilar el libro`, poppler, §2.1) todos «=> skipped». Causa medida y JUSTIFICADA: scratchpad/libro_35320579707.log:«· sin cambios en doc/book/ — se omite el PDF», y `git show --name-only` confirma 0 ficheros doc/book/ en los siete commits. La consecuencia es de LECTURA: «CI verde» en estos commits significa `lake build` + 5 controles del job `build`, no los 9 del workflow.

* **[baja]** `Check for sorry` lleva `continue-on-error: true`: su rojo no tenia por que romper el run
  · *Evidencia:* build.yml:83-85 «- name: Check for sorry» / «continue-on-error: true   # Warning only — change to false to make it blocking». No enmascaro nada aqui — el log dice literalmente «✅ No sorry found.» en los cinco —, pero el `conclusion: success` que devuelve el API para ese paso es el valor POSTERIOR al continue-on-error, no el resultado crudo.

* **[baja]** M-12 (empujar FOL ANTES que RPP) se cumplio en los CINCO — medido por los SHA que el runner saco
  · *Evidencia:* Los FOL usados son, en orden: 4130faa (2026-09-17 18:46:58, 22 s antes de b787d9d), d3a51f1 (09:37:47, 2 min 48 s antes de 8d91989), 90f01e9 (10:23:20, 35 s antes de 37ec0e4), 04e2632 (11:23:24, 34 s antes de b22dd85), 404e2cd (12:58:27, 33 s antes de 5884ffa). Todos son el commit `lock:` inmediatamente anterior en E:/Dropbox/GitHub/lean4/FOL.

* **[baja]** La cifra de check-footprints crecio 132 → 138 → 142 → 145 → 147 en esos cinco commits, y el «147» del banner es de 5884ffa en adelante
  · *Evidencia:* Logs: run_35248747949.log «✅ LOS 132 FOOTPRINTS CUADRAN.» · run_35320579707.log «138» · run_35324176741.log «142» · run_35329338284.log «145» · run_35337367895.log «147» · run_35353344724.log (d85df4a) y run_35357631645.log (2a9e88c) «✅ LOS 147 FOOTPRINTS CUADRAN.». Dato para A2: el titular «147» NO vale para 8d91989, donde la CI midio 138.

* **[baja]** `check-warnings` (ADR-065) no existia todavia en 8d91989 ni en 37ec0e4: entra en b22dd85
  · *Evidencia:* Pasos del job `lake build`: en 35320579707 y 35324176741 la lista termina en «12. Check doc sync => success»; en 35329338284 (b22dd85), 35337367895 y posteriores aparece «13. Check warnings => success» y el log dice «✅ LOS 11 WARNINGS CUADRAN.». El «0 warnings» de ADR-057/058/059 no lo reejecuto nadie en CI hasta b22dd85.

#### Acción propuesta

1) A4 se cierra: los cinco commits pasan a VERDE VISTO en el registro que lleve el estado de la CI. El aviso del propietario se respeta — no se movio ninguno por analogia con FOL, cada uno sale de su propio run.

2) Un control [G] nuevo, barato y que cierra un agujero REAL (hallazgo 2): hoy el verde de RPP certifica el par (RPP@sha, FOL@master-de-ese-instante), y el segundo miembro solo vive en un log que caduca a los 90 dias. Un paso de una linea en el job `lake build` — imprimir `git -C ../FOL rev-parse HEAD` al `$GITHUB_STEP_SUMMARY` — hace el par recuperable sin caducidad. Es el mismo patron que M-12 ya reconoce (RPP clona FOL como hermana) pero sin dejar rastro de CUAL.

3) Un arreglo puntual, de REDACCION, no de codigo (hallazgo 3): cuando se diga «CI verde» de un commit de estos, decir de que job. El workflow tiene DOS; el segundo (`libro`) esta verde habiendo omitido sus cuatro controles porque el push no toco doc/book/. La puerta esta bien escrita y lo AVISA en su log, asi que no hay nada que arreglar en el YAML; lo que se desliza es el titular.

4) Dato que le toca a A2, no a A4, y que sale gratis de esta medicion: el «147» del banner NO vale para 8d91989 — alli la CI midio 138. La cifra de check-footprints es una serie por commit (132/138/142/145/147), no una constante; quien la cite tiene que citar TAMBIEN el commit, que es exactamente lo que M-13 exige («una cifra de control se RE-EJECUTA o se marca con su AMBITO»).

5) NO hacer: nada mas. No he tocado ningun fichero de los dos repos, ni ejecutado `lake` en ninguna forma.

#### ⚖️ La refutación

Reproduje el hallazgo entero por mi cuenta y no he podido tumbarlo. (1) `gh api .../actions/runs/<id>` de los siete runs: los siete `success`, `run_attempt=1`, con los SHAs, las horas UTC y las duraciones exactas de la tabla; `gh run list --limit 40` muestra UN solo run por SHA, así que no hay un intento fallido oculto detrás de ninguno de los cinco. (2) Los pasos por job confirman lo que afirma: en 8d91989 y 37ec0e4 la lista termina en «12. Check doc sync» (16 pasos) y en b22dd85 y posteriores aparece «13. Check warnings» (17 pasos) — el hallazgo 7 es medida, no relato. (3) El job `libro` sale `success` con 7 pasos `skipped` en los CINCO runs (comprobado por API, no por el log), la puerta dice «sin cambios en doc/book/ — se omite el PDF» y `git show --name-only` da 0 ficheros `doc/book/` en los siete commits: hallazgo 3 confirmado por dos vías independientes. (4) build.yml:41-42 (`repository: julian1c2a/FOL` / `ref: master`) y build.yml:85 (`continue-on-error: true`) están en las líneas exactas que cita; además `lakefile.lean:13` es `require FOL from "../FOL"` y `lake-manifest.json` registra `"type": "path"` SIN rev, así que nada fija el segundo miembro del par: el hallazgo 2 no es retórico. (5) En run_35320579707.log línea 184, el `git log -1 --format=%H` que sigue al checkout con working directory `.../ROBINSON_PlusPlus/FOL` imprime `d3a51f1a…`: el par (RPP@sha, FOL@sha) está MEDIDO, no inferido; los cinco SHAs de FOL contrastan uno a uno con `git log` de FOL y son todos commits `lock:` con las horas declaradas. (6) La serie de footprints la obtuve por una SEGUNDA vía, no del log: contando las filas del heredoc TABLA de check-footprints.bash da 147 hoy y `git show 8d91989:check-footprints.bash` da 138 — exactamente lo que la CI imprimió. (7) `##[error]` = 0 en los doce logs guardados y el único `##[warning]` es el de Node.js 20; los cinco logs de `libro` son ficheros distintos (md5 distintos), no una copia repetida. LENTE DE VACUIDAD: ningún hallazgo es incondicional — si el YAML fijara un SHA de FOL el hallazgo 2 sería falso; si algún commit hubiera tocado doc/book/ el 3 sería falso; los runs podían haber salido rojos (la propia CI de FOL «falló en 0 s» dos veces el 09-17). MEDICION vs ESTIMACION: las siete cifras que publica son medidas y están así etiquetadas, y la única limitación (retención de 90 días de los logs) va marcada «NO MEDIDO».

**Lo correcto:**

Sobrevive ENTERO en su núcleo: los cinco commits (b787d9d, 8d91989, 37ec0e4, b22dd85, 5884ffa) pasan a VERDE VISTO por lectura directa de su propio run, y los hallazgos 1, 2, 3, 4, 6 y 7 quedan confirmados con evidencia independiente. Tres correcciones de redacción, ninguna que tumbe nada: (a) el hallazgo 3 dice que «CI verde» significa «lake build + 5 controles del job build», y para 8d91989 y 37ec0e4 son CUATRO (check-warnings no existía todavía) — se contradice con su propio hallazgo 7; debe decir «4 controles hasta 37ec0e4, 5 desde b22dd85», y por tanto «no los 9 del workflow» es «no los 8/9 del workflow». (b) El hallazgo 5 (M-12) está bien concluido pero mal argumentado: los «22 s / 2 min 48 s / 35 s / 34 s / 33 s antes» son restas de FECHAS DE COMMIT locales (+0200), que no son instantes de push; lo que de verdad prueba M-12 es el SHA que el runner sacó de `ref: master` al arrancar el run. Hay que decir eso y dejar las restas como dato accesorio, o etiquetarlas como lo que miden. (c) En la nota «NO MEDIDO», «pasada la retención esa cifra no es recuperable» es un pelín fuerte: el SHA de FOL sigue siendo INFERIBLE de la historia de master de FOL más las horas (salvo force-push); lo que se pierde es la CERTIFICACION del par, no el dato. Esto refuerza, no debilita, la acción propuesta 2 (imprimir `git -C ../FOL rev-parse HEAD` al $GITHUB_STEP_SUMMARY).

---

### A5 · ¿Hay un sesgo sistemático al cotizar el riesgo? (M-14)
**Veredicto del informe:** `PARCIAL` · **¿sobrevive a la refutación?** **⛔ NO**

**Resumen:** Leídos ADR-062…068 completos, el plan §5.13/§6.6/§6.8-§6.13/§7.5 y los bloques 09-16/17/18 de NEXT-STEPS, más los seis commits de FOL con `git show --numstat`: la hipótesis se cumple en **5 de 7** (062, 063, 065, 067, 068), falla con contraejemplo explícito en **1** (064) y es parcial en **1** (066) — merece M-14, pero la evidencia publicada que la sostiene tiene **cuatro defectos medidos** (una cita fabricada, una estimación atribuida a una sección que no la contiene, una cifra refutada que sigue viva en el plan, y una unidad de «línea» que cambia entre ADR).

#### Cifras

TABLA ADR POR ADR (cita literal | estimación y su etiqueta | riesgo real | líneas MEDIDAS por `git show --numstat` en E:/dropbox/github/lean4/FOL):

· ADR-062 (c4abeaa). Declarado, ADR-060 §5: «Iterar sobre una formula prenexa entera … **no esta hecho** … ⬜ **No medida.**»; ADR-062 §5 describe el riesgo como «hay que elegir entre tres rutas» (tres diseños de algoritmo). ESTIMACIÓN: NINGUNA. Real, ADR-062 §1 (título): «El unico riesgo que habia, y se mata con una **decision de definicion**» (el combustible); §3: «`occursFormula_lift` **no existia** … el teorema final pide una hipotesis que **nadie puede descargar**». MEDIDO: +536 l. en `FOL/SkolemNF0.lean`. ⇒ SÍ (construcción→definición), sin cifra previa que contrastar.

· ADR-063 (f598062). Declarado, ADR-056 §1 tabla: «pieza cara: `SubLang` + Maehara **desde cero**». ESTIMACIÓN: «~850-1400 l. cada una» — SIN etiqueta ESTIMADO, y es un rango para F **y** H juntas. Real, ADR-063 §4: «⛔ **falso**: `predF`+`PredSub`+`Cov` son **30 l.**» / «donde estaba de verdad: en **elegir que simbolos se cuentan**, que es una **decision de ENUNCIADO**». MEDIDO: +848 l. de fichero (`FOL/Craig0.lean`); la ADR publica «665 l. de codigo (784 con documentacion)» y 784 = 848 − 64 líneas en blanco. ⇒ SÍ, y autodeclarado.

· ADR-064 (3252adc). Declarado, ADR-055 §3 (literal): «hay que llevar ademas la **tupla parcial** acumulada y la salida pasa a `List (List Term)`». ESTIMACIÓN: «~350-450 l., riesgo alto» — SIN etiqueta. Real, ADR-064 §1: «el dato no habia que construirlo»; §5: «✅ Y la estimacion de ADR-055 **ACERTO** … ⚠️ cierto». MEDIDO: +519 l. (`BlockExtraction0.lean`) +14 (`HerbrandBlock0.lean`); la ADR publica «≈400 l. de codigo (518 con documentacion)». ⇒ **NO: CONTRAEJEMPLO**.

· ADR-065 §1 (d499f26). Declarado, ADR-062 §4: «**exige empujar el axioma de Skolem bajo el prefijo `∀ⁿ`** (la regla K iterada sobre `allBlock`), y **no esta medida**». ESTIMACIÓN: NINGUNA. Real, ADR-065 §1: «Medida: **un solo lema**, y por una identidad que estaba delante: `allBlock n (Formula.forall A) = allBlock (n + 1) A`». MEDIDO: +83/−2 l. en `SkolemNF0.lean` (la ADR dice «+70 l.»). ⇒ SÍ (construcción→identidad definicional).

· ADR-066 §1 (27a7c87). Declarado, ADR-065 §4: «Falta **iterarla sobre el bloque** (`¬ allBlock m ψ ⇒ exBlock m (¬ψ)`) con `ex_congr`». ESTIMACIÓN: «~90-130 l., riesgo bajo-medio ⚠️ ESTIMADO» — ✅ ETIQUETADA (la única bien etiquetada de las cinco). Real, ADR-066 §1: «**las dos piezas NO componian** … no es que faltara un lema: es que las dos piezas se encuentran **al otro lado de una negacion**». MEDIDO: +138 l. (`SkolemHerbrand0.lean`), la ADR dice «~55 l. de codigo». ⇒ PARCIAL: la negación **ya estaba declarada** en ADR-062 §4 («Herbrand habla de EXISTENCIALES y Skolem los quita … esa negacion **no esta escrita**») y la propia ADR-066 §1 lo reconoce: «ADR-062 §4 **midio bien** la juntura».

· ADR-067 (sin commit de código en FOL). Declarado, ADR-066 §2: «Coste: **reescribir `Craig0` entero** con el parametro `E` (los 26 casos, **~700 l. mecanicas**)» — SIN etiqueta. Real, ADR-067 §1: «⛔ **`E` es una salida existencial SIN COTA**» ⇒ «El teorema seria cierto y no diria nada». MEDIDO: **0 líneas aterrizadas**; §5: «la implementacion iba por **3 errores de compilacion restantes** de 51». ⇒ SÍ, el caso más puro de la serie.

· ADR-068 (78bbdfe + RPP 2a9e88c). Declarado, ADR-055 §4.1 y plan §7.5:1271: «📐 Tamano de parametrizar: **163 modulos / 3 902 declaraciones** (FOL 42/545, RPP 121/3 357), **MEDIDO**» — etiquetada MEDIDO, **no** ESTIMADO. Real, ADR-068 §2: «Esa cifra medía el **ALCANCE** del tipo, no el **TRABAJO**. Un `abbrev` más un `export` absorbe el alcance entero». MEDIDO: `FOL/FOL.lean` +58/−12, `FOL/DecEq.lean` +10/−6, `ROBINSON_PlusPlus/Meta/HilbertSeq.lean` 8 líneas ⇒ **3 ficheros**, la cifra de la ADR es correcta. ⇒ SÍ.

RECUENTO: SÍ 5 (062, 063, 065, 067, 068) · NO 1 (064) · PARCIAL 1 (066). Umbral ≥5/7 alcanzado.

«EL PLAN LO ESTIMÓ» vs «EL PLAN LO MIDIÓ» (auditado con grep sobre las tres fuentes):
· Cifras SIN etiqueta que se usaron como cotización: ADR-056 «~850-1400 l.»; ADR-056 §5 «~250-350 l., riesgo bajo»; ADR-055 §3 «~350-450 l., riesgo alto»; ADR-066 §2 «~700 l. mecanicas». CUATRO de las cinco cotizaciones de la serie van SIN etiqueta.
· Cifras CON etiqueta ESTIMADO: sólo ADR-065 §4 («~90-130 l. … ⚠️ ESTIMADO» y «⚠️ ESTIMADO alto» para el refactor de `Hauptsatz0`) y ADR-067 §3 («⚠️ ESTIMADO: ~120 l. … ~800-900 l.»). La etiqueta aparece **a partir de ADR-065**, no antes.
· Y el caso que no encaja en ninguna de las dos categorías: «163 módulos / 3 902 declaraciones» iba etiquetada **MEDIDO** y era una medición CORRECTA — del sujeto equivocado. Ese es el fallo que bloqueó el paso 4 durante dos meses, y **no** es el fallo que M-13 ni [[feedback-estimacion-sin-etiqueta]] vigilan.

HISTÓRICO estimado→medido (plan, líneas 573, 631, 1058, 1080, 1188, 1224), para ver si el sesgo es «siempre alto»: Barendregt ~90→99 (corto); inducción del grado ~400-600→605 (justo fuera, por arriba); `prenex_isPrenex` ~70→**95** (⚠️ CORTA, la estimación se quedó por debajo); Skolem bajo prefijo ~200→113 (larga); Craig ~850→665 (larga); Herbrand de bloque ~350-450→≈400 (dentro). ⇒ el sesgo NO es «las estimaciones siempre sobran»: es que **cotizan la construcción y la construcción no es donde se decide**.

CONTROL DE UNIDAD (medido con `wc -l` + `grep -c '^[[:space:]]*$'`): `Craig0.lean` 848 total / 784 no-blancas → la ADR llama «784 con documentacion» a las **no-blancas**; `SkolemNF0.lean` al cerrar ADR-062 tenía 536 totales → la ADR llama «536 con documentacion» al **total**. Dos reglas distintas en dos ADR consecutivas ⇒ los cotejos «~850 estimado vs 665 medido» no son conmensurables. Con la unidad «fichero», la estimación de ADR-056 (850) acierta el tamaño de `Craig0.lean` (848) **al 0,2 %**.

REDACCIÓN PROPUESTA DE M-14 (estilo de M-11/M-12/M-13, fila para la tabla de DECISIONS.md:55):

| **M-14** | ⚠️ **El riesgo de una pieza se COTIZA en la construcción y se PAGA en el enunciado: antes de estimar líneas, escribir la FIRMA literal del teorema y un CONSUMIDOR que la use, y preguntar «¿qué decisión de enunciado o de definición puede volverlo falso, vacuo o inaplicable?».** Una estimación sólo puede contar lo que ve —una inducción, un port, un algoritmo—, y en esta serie eso nunca fue lo que decidió: la «pieza cara» declarada resultó ser de **30 l.** y el riesgo estaba en «elegir qué símbolos se cuentan, que es una decisión de ENUNCIADO» (ADR-063 §4); «empujar el axioma bajo el prefijo ∀ⁿ» fue **un solo lema**, por una identidad definicional (ADR-065 §1); los 26 casos de `maehara_eq` iban por **3 errores de 51** cuando el enunciado resultó **VACUO** (ADR-067); y «163 módulos» fueron **3 ficheros**, porque un `abbrev` + un `export` absorben el alcance entero (ADR-068 §2). ⛔ **Y el contraejemplo que la acota, que es de la misma serie**: ADR-064, donde la obstrucción que ADR-055 declaró («hay que llevar la tupla parcial») era **cierta** y la estimación cayó **dentro de su rango**. ⇒ la regla no dice que la construcción nunca sea el riesgo: dice que **una cotización que sólo mira la construcción no ha cotizado nada**. | ADR-063 §4, ADR-065 §1, ADR-067, ADR-068 §2 | El control barato, y ya es método del proyecto («primero el consumidor, después el molde», ADR-055 §1): **ninguna cifra de líneas se publica sin, delante, el bloque con la firma literal y el consumidor**; si la firma no está escrita, la cotización se publica como `⬜ SIN ENUNCIADO` y **no cuenta**. Y sobre la firma, pasar la **lente de VACUIDAD** (ADR-067 §5): «¿y si es cierto y no dice nada?». ⬜ No mecanizado |

#### Hallazgos

* **[alta]** La hipótesis se cumple en 5 de 7, no en las cinco: ADR-064 es contraejemplo y está dentro de la ventana 062-066
  · *Evidencia:* E:/dropbox/github/lean4/ROBINSON_PlusPlus/DECISIONS.md:5084 (ADR-064 §5) — «✅ Y la estimacion de ADR-055 ACERTO» con la tabla «| lineas | ~350-450 | **≈400** ✅ dentro del rango |» y «| «hay que llevar la tupla parcial» | ⚠️ cierto | ✅ **cierto** — pero ya la llevaba `instB` |». Medido con git show --numstat 3252adc: +519 l. en FOL/BlockExtraction0.lean.

* **[alta]** La cita que hace encajar a ADR-064 en el patrón es FABRICADA: ADR-055 nunca escribió «redisenio del enunciado»
  · *Evidencia:* DECISIONS.md:5033 (ADR-064 §1): «ADR-055 midio asi la obstruccion: *«hay que llevar ademas la TUPLA PARCIAL acumulada ⇒ es un redisenio del enunciado, no una envoltura»*». El original, DECISIONS.md:4248 (ADR-055 §3): «La mala: hay que llevar ademas la **tupla parcial** acumulada y la salida pasa a `List (List Term)`. ⇒ **~350-450 l., riesgo alto**. No es la envoltura que la estimacion inicial (~250 l.) sugeria.» `grep -n redisen DECISIONS.md` devuelve UNA sola línea: la 5033.

* **[alta]** El plan sigue publicando como MEDICIÓN la cifra que ADR-068 refutó por un factor de ~50
  · *Evidencia:* doc/PLAN-COMPLETITUD-FINITISTA.md:1271 — «📐 **Tamaño de parametrizar**, medido hoy: **163 módulos / 3 902 declaraciones** (FOL 42/545 · RPP 121/3 357)», sin rectificar. NEXT-STEPS.md:160 sí la lleva tachada: «⛔ ~~📐 163 módulos / 3 902 declaraciones~~ — **FALSO, por un factor de ~50** (ADR-068)».

* **[alta]** ADR-063 §4 compara contra una estimación que la sección citada no contiene, y convierte un rango en punto
  · *Evidencia:* DECISIONS.md:4976 (ADR-063 §4): «| | ADR-056 (estimado) | medido |» con «| lineas | ~850 | **665** |» y «| riesgo | alto | **medio** |». El original, DECISIONS.md:4304 (ADR-056, Contexto): «quedaban dos, **F** (interpolacion de Craig por Maehara) y **H** (Skolem), **~850-1400 l. cada una**» — es un RANGO, para F y H, y la palabra «alto» no aparece en toda la ADR-056 referida a F (verificado con sed -n '4299,4380p' | grep riesgo). Y el plan lo empeora: doc/PLAN-COMPLETITUD-FINITISTA.md:1188 dice «§6.6 estimó ~850 l. y «riesgo alto»», pero «850» aparece UNA sola vez en todo el plan, en esa misma línea 1188.

* **[media]** La unidad «línea» cambia entre ADR consecutivas, así que ningún cotejo estimado-vs-medido de la serie es conmensurable
  · *Evidencia:* FOL/Craig0.lean: wc -l = 848, líneas en blanco = 64 ⇒ 784 no-blancas; ADR-063 (DECISIONS.md:4901) publica «665 l. de codigo (**784** con documentacion)» ⇒ usa NO-BLANCAS. FOL/SkolemNF0.lean al cerrar ADR-062: git show --numstat c4abeaa = +536 totales; ADR-062 (DECISIONS.md:4801) publica «350 l. de codigo (**536** con documentacion)» ⇒ usa TOTALES. Con la unidad «fichero», la estimación de ADR-056 (~850) acierta `Craig0.lean` (848 l.) al 0,2 %, y la conclusión «la estimación se pasó» se invierte.

* **[media]** ADR-067 es el caso más limpio de la hipótesis: la construcción estaba al 94 % y el enunciado la anuló entera
  · *Evidencia:* DECISIONS.md:5325 (ADR-067 §1): «⛔ **`E` es una salida existencial SIN COTA** … ⇒ para CUALQUIER interpolante se fabrica un `E` que satisface **las dos** condiciones a la vez **sin mirar el secuente**»; §5 (DECISIONS.md:5407): «el coste evitado: la implementacion iba por **3 errores de compilacion restantes** de 51. Estaba a punto de aterrizar un teorema vacuo **con todos los controles en verde**». El coste declarado era construcción pura: ADR-066 §2 (DECISIONS.md:5252) «reescribir `Craig0` entero con el parametro `E` (los 26 casos, ~700 l. mecanicas)».

* **[media]** El fallo de ADR-068 NO es el que M-13 ni [[feedback-estimacion-sin-etiqueta]] vigilan: la cifra iba etiquetada MEDIDO y era correcta
  · *Evidencia:* DECISIONS.md:4275 (ADR-055 §4.1): «📐 Tamano de parametrizar: **163 modulos / 3 902 declaraciones** (FOL 42/545, RPP 121/3 357), **MEDIDO**». Y DECISIONS.md:5442 (ADR-068 §2): «Esa cifra medía el **ALCANCE** del tipo, no el **TRABAJO**. Un `abbrev` más un `export` absorbe el alcance entero.» ⇒ una medición correcta del sujeto equivocado atraviesa los dos controles existentes. Medido: git show --numstat 78bbdfe = FOL/FOL.lean +58/−12, FOL/DecEq.lean +10/−6; RPP 2a9e88c = Meta/HilbertSeq.lean 8 líneas.

* **[media]** ADR-066 es sólo PARCIAL: el riesgo «real» (la dualidad) ya estaba declarado cuatro ADR antes
  · *Evidencia:* DECISIONS.md:5231 (ADR-066 §1): «ADR-062 §4 **midio bien** la juntura … pero **Herbrand habla de EXISTENCIALES y Skolem los quita**». El declarante original, DECISIONS.md:4874 (ADR-062 §4): «⬜ **El enchufe con Herbrand no esta escrito** … el puente va **en la direccion contraria** … El ensamblaje real es *refutar `∀ᵐ ψ`* = *derivar `∃ᵐ ¬ψ`*, y esa negacion **no esta escrita**.» ⇒ el proyecto sí había localizado el riesgo en el enunciado; lo que ADR-065 §4 hizo fue re-cotizarlo como construcción («Falta iterarla sobre el bloque … con `ex_congr`», ~90-130 l. ESTIMADO).

* **[media]** Cuatro de las cinco cotizaciones de la serie van SIN la etiqueta ESTIMADO; la etiqueta sólo aparece a partir de ADR-065
  · *Evidencia:* Sin etiqueta: DECISIONS.md:4304 «~850-1400 l. cada una»; :4363 «~250-350 l., riesgo bajo por ser port»; :4249 «⇒ **~350-450 l., riesgo alto**»; :5253 «~700 l. mecanicas». Con etiqueta: DECISIONS.md:5190 «(~90-130 l., riesgo bajo-medio ⚠️ ESTIMADO)», :5198 «⚠️ ESTIMADO alto», :5381 «⚠️ ESTIMADO: `LKe` + los dos puentes ~120 l.». (grep -n 'ESTIMADO' DECISIONS.md devuelve exactamente esas tres apariciones en el tramo 4796-5505.)

* **[baja]** ADR-064 §5 reclama una primicia que no le corresponde: la capa prenexa cayó dentro de su rango el día anterior
  · *Evidencia:* DECISIONS.md:5089 (ADR-064 §5): «⭐ Es la **primera** estimacion de esta serie que cae dentro de su propio rango». Contra: ADR-056 §5 (DECISIONS.md:4363) estimó la capa prenexa en «~250-350 l.» y ADR-057 / plan §6.7 (doc/PLAN-COMPLETITUD-FINITISTA.md:1019) miden «`../FOL/FOL/Prenex0.lean`, **260 l.**» — dentro del rango, y con fecha 2026-09-17, un día antes.

* **[baja]** El sesgo NO es «las estimaciones siempre sobran»: hay al menos una que se quedó corta, y eso es lo que distingue M-14 de una regla de calibración
  · *Evidencia:* doc/PLAN-COMPLETITUD-FINITISTA.md:1058 (§6.8, ADR-058): «⚠️ Estimado ~70 l., **medido 95** — la primera estimación del día que se queda **corta**, por contar «dos inducciones» donde había **seis**». Y :573 (§5.10): «~90 l. estimadas → **99 l.**». ⇒ el patrón no es de magnitud sino de SUJETO: se cotiza la construcción y decide el enunciado.

* **[baja]** El encargo atribuye a ADR-064 la frase que está en ADR-063 §4
  · *Evidencia:* El texto «es una decision de ENUNCIADO» aparece en DECISIONS.md:4981 (ADR-063 §4, tabla: «| donde estaba de verdad | -- | ⭐ en **elegir que simbolos se cuentan**, que es una decision de ENUNCIADO |») y en doc/PLAN-COMPLETITUD-FINITISTA.md:1190 («…una decisión de ENUNCIADO, no de construcción»). En ADR-064 no aparece; ADR-064 es precisamente la ADR donde el patrón falla.

#### Acción propuesta

TRES COSAS, y sólo una es regla nueva.

(1) ESCRIBIR M-14 — justificado (5/7, umbral alcanzado). Va como fila en la tabla de DECISIONS.md:55, con el texto propuesto en «cifras». ⚠️ Pero hay que escribirla CON su contraejemplo dentro (ADR-064): sin él, M-14 se convierte en «la construcción nunca es el riesgo», que es falso y ya refutado por la propia serie. Y no duplica nada: [[feedback-estimacion-sin-etiqueta]] y M-13 vigilan la ETIQUETA de la cifra; M-14 vigila el SUJETO que se cotiza. El caso de «163 módulos» lo prueba: iba etiquetada MEDIDO, era correcta, y era la cifra equivocada.

(2) CUATRO ARREGLOS PUNTUALES, porque la evidencia de M-14 está contaminada y hay que repararla ANTES de que M-14 la cite:
  a) `doc/PLAN-COMPLETITUD-FINITISTA.md:1271` — sigue publicando «163 módulos / 3 902 declaraciones, **medido hoy**» sin la rectificación de ADR-068. NEXT-STEPS.md:160 ya la lleva tachada; el plan no. Es la cifra que bloqueó el paso 4 dos meses y **sigue viva**.
  b) `doc/PLAN-COMPLETITUD-FINITISTA.md:1188` — «§6.6 estimó ~850 l. y «riesgo alto»»: §6.6 del plan no contiene ni la cifra ni la palabra. Corregir la atribución a ADR-056 §1, y decir que allí es «~850-1400 l. cada una» para F **y** H, sin la palabra «alto».
  c) `DECISIONS.md:5033` (ADR-064 §1) — la cita de ADR-055 incluye «⇒ es un redisenio del enunciado, no una envoltura», que ADR-055 **no escribe** (grep: «redisenio» aparece SÓLO ahí). Sustituir por la cita literal.
  d) `DECISIONS.md:5089` / plan:1224 — «la **primera** estimacion de esta serie que cae dentro de su propio rango» es falso: la capa prenexa (ADR-056 §5, «~250-350 l.» → ADR-057, «260 l. de código») ya cayó dentro **el día anterior**. Corregir a «la segunda».

(3) UN CONTROL [G] NUEVO, y es pequeño: `check-citas.bash`. Extrae de DECISIONS.md y del plan toda cadena entre «…» que vaya acompañada de una referencia («ADR-0NN §K», «§N.M») y comprueba por `grep -F` que aparece **literalmente** en el destino; rompe si no. Habría cazado (2b) y (2c), que son los dos hallazgos que fabrican el patrón. ⚠️ ESTIMADO ~60-90 l., riesgo bajo — y la cifra va etiquetada porque no la he medido.
   ⛔ Lo que NO propongo: un control para M-14 misma. «¿La firma está escrita antes de la cifra?» no se mecaniza sin falsos positivos; su verificación es a mano, como la de M-8 y la de M-11.

⚠️ Y una corrección al encargo: el hallazgo «está dicho de pasada en ADR-064» está mal atribuido. La frase vive en **ADR-063 §4** (`DECISIONS.md:4981`) y en el plan §6.12 (`:1190`). ADR-064 es justo la ADR donde el patrón **no** se cumple.

#### ⚖️ La refutación — **MANDA ÉSTA**

Reproduje una a una las mediciones y casi todas son CORRECTAS (detalle en «correccion»), pero el informe no sobrevive tal como esta entregado, por cuatro defectos que cambian la ACCION, no solo la redaccion:

[1] ⛔ El «5 de 7» mezcla DOS POBLACIONES y el umbral se alcanza contando casos donde no habia nada que cotizar. El propio informe escribe «ESTIMACION: NINGUNA» para ADR-062 y para ADR-065. Verificado en el arbol: ADR-060 §5 / ADR-062 §4 (DECISIONS.md:4865-4874) declaran la deuda con «no esta medida» / «no esta escrita» — sin una sola cifra. Si M-14 regula CIFRAS («antes de estimar lineas, escribir la firma...»), su poblacion son las ADR con cifra publicada: 063 SI · 064 NO · 066 PARCIAL · 067 SI · 068 SI(etiquetada MEDIDO) ⇒ **3 SI / 1 NO / 1 PARCIAL de 5**, no 5/7. La regla sigue siendo defendible, pero el umbral publicado es de un recuento no homogeneo — que es exactamente el vicio que la regla denuncia.

[2] ⛔ «Cita FABRICADA» (gravedad alta) esta sobre-etiquetada, y el titulo del hallazgo se contradice con el hallazgo #1 del mismo informe. Medido: `grep -n redisen DECISIONS.md` ⇒ UNA linea, la 5033 ✓. Pero la SUSTANCIA si esta en el original: DECISIONS.md:4249 dice «**No es la envoltura** que la estimacion inicial (~250 l.) sugeria». Es una PARAFRASIS entrecomillada, no una cita inventada. Y el titulo («la cita que hace encajar a ADR-064 en el patron») choca con el hallazgo #1: ADR-064 es justo la ADR donde el patron NO se cumple, y lo declara ella misma en §5 (DECISIONS.md:5078-5086, verificado).

[3] ⛔ El «CONTROL DE UNIDAD» mide bien y concluye mal — y ahi el informe confunde MEDICION con COINCIDENCIA. Medido por mi: `Craig0.lean` 848 total / 64 blancas / **784** no-blancas ⇒ ADR-063 usa NO-BLANCAS ✓; `git show --numstat c4abeaa` = **+536** total en `SkolemNF0.lean` ⇒ ADR-062 usa TOTALES ✓. La unidad si cambia. Pero la inferencia «con la unidad fichero la estimacion de ADR-056 (850) acierta `Craig0.lean` (848) al 0,2 % y la conclusion se invierte» es SELECCION DE UNIDAD a posteriori: hay tres unidades (848/784/665) contra un RANGO (850-1400); siempre se encuentra una coincidencia. Y la refuta la propia ADR-056: ese rango era «~850-1400 l. **cada una**» para F **y H**, y H aterrizo en esa misma ADR con **110 l. de codigo** (`FOL/Skolem0.lean`, DECISIONS.md:4304) — ninguna unidad salva eso. Un 0,2 % contra un extremo de rango no es calibracion.

[4] ⛔ La enmienda (2d) se apoya en usar «serie» en dos sentidos. El informe define «la serie» como ADR-062…068 en todo lo demas («las cinco cotizaciones de la serie»), y luego corrige el «primera de esta serie» de ADR-064 apelando a ADR-057, que queda FUERA de esa serie. Ademas, medido: ADR-057 (DECISIONS.md:4381) dice «`FOL/Prenex0.lean`, **260 l. de codigo**» y NO formula ningun cotejo con el rango ~250-350 (que esta en ADR-056 §5, :4363); el cotejo lo construye el auditor. Es una enmienda al texto historico de un ADR apoyada en una definicion que el informe no mantiene.

[5] ⚠️ Estimacion/medicion, segunda confusion: «ADR-067 · MEDIDO: **0 lineas aterrizadas**» solo vale acotado a FOL (asi va en la tabla, pero no en el RESUMEN). Medido: `git show --numstat d85df4a` (RPP) = **+89 l. en `sondeos/CraigEqVacuo.lean`**, y el fichero existe (4 684 bytes). El contraejemplo es codigo compilado, no cero.

[6] ⚠️ Anclas aproximadas, en un informe que propone `check-citas.bash`: 5089→**5086**, 5231→**5224**, 5325→**5328**, 5407→**5401**, 5252→**5261**. Todas caen en la ADR y seccion correctas, pero ninguna es exacta.

LENTE DE VACUIDAD (aplicada en serio): el HALLAZGO no es vacuo — depende del arbol, habria salido distinto con otro, y trae contraejemplo falsable (064). Pero la REDACCION de M-14 si roza la vacuidad en su clausula operativa: «¿que decision de enunciado o de definicion puede volverlo falso, vacuo o inaplicable?» admite siempre alguna respuesta, y el propio informe reconoce que no se mecaniza. Lo que la salva a medias es el contraejemplo dentro; sin el, M-14 seria «la construccion nunca es el riesgo», que la propia serie refuta.

**Lo correcto:**

LO QUE SI SOBREVIVE (lo he reproducido yo, leyendo el arbol; todo lo de abajo es MEDIDO):

· Los seis numstat de FOL, EXACTOS: c4abeaa +536 `FOL/SkolemNF0.lean` · f598062 +848 `FOL/Craig0.lean` · 3252adc +519 `FOL/BlockExtraction0.lean` y +14/−1 `FOL/HerbrandBlock0.lean` · d499f26 +83/−2 `FOL/SkolemNF0.lean` · 27a7c87 +138 `FOL/SkolemHerbrand0.lean` · 78bbdfe `FOL/FOL.lean` +58/−12 y `FOL/DecEq.lean` +10/−6. Y RPP 2a9e88c `Meta/HilbertSeq.lean` 4/4 = 8 lineas. Ninguna cifra del informe falla aqui.
· `wc -l` + blancas: Craig0 848/64/784 · SkolemHerbrand0 138/28/110 · BlockExtraction0 519/42/477 · Prenex0 355/32/323.

· ⭐ ARREGLO (2a), INTACTO Y ES EL IMPORTANTE: `doc/PLAN-COMPLETITUD-FINITISTA.md:1271` sigue publicando «📐 **Tamaño de parametrizar**, medido hoy: **163 módulos / 3 902 declaraciones**» sin rectificar, mientras `NEXT-STEPS.md:160` ya la lleva tachada («FALSO, por un factor de ~50»). Es la cifra que bloqueo el paso 4 y sigue viva en el plan. Hay que arreglarlo.

· ⭐ ARREGLO (2b), INTACTO: `plan:1188` dice «§6.6 estimó ~850 l. y «riesgo alto»». Medido: en §6.6 del plan (lineas 991-1016) NO aparece «850» ni «alto» — la unica linea con «riesgo» es la 1012, «riesgo **bajo**»; y en TODA la ADR-056 (4299-4376) «riesgo» aparece UNA vez, :4363, «riesgo bajo por ser port». El original, DECISIONS.md:4304, es «~850-1400 l. **cada una**» para F y H. La atribucion es incorrecta y hay que corregirla a ADR-056 §Contexto, con el rango y sin la palabra «alto». Lo mismo vale para el encabezado de ADR-063 (DECISIONS.md:4901, «estimado en ~850 l., riesgo alto») y su tabla §4 (:4978).

· ADR-064 COMO CONTRAEJEMPLO: verificado literal en :5078 («✅ Y la estimacion de ADR-055 ACERTO»), tabla «~350-450 | **≈400** ✅ dentro del rango» y ««hay que llevar la tupla parcial» | ⚠️ cierto | ✅ **cierto**». Es el elemento que impide que M-14 degenere; tiene que ir DENTRO de la regla, como el informe pide.
· EL CASO «163 MODULOS» ATRAVIESA LOS DOS CONTROLES EXISTENTES: :4275 la publica «**MEDIDO**» y :5442 explica que medía el ALCANCE y no el TRABAJO. Este es el argumento fuerte de no-duplicacion frente a M-13 y [[feedback-estimacion-sin-etiqueta]], y aguanta entero.
· LA ETIQUETA `ESTIMADO` aparece exactamente 3 veces en el tramo 4796-5505 (:5190, :5198, :5381), todas en ADR-065/067 ⇒ «la etiqueta nace en ADR-065» ✓.
· EL SESGO NO ES DE MAGNITUD: `plan:1058` «Estimado ~70 l., **medido 95** — la primera del dia que se queda **corta**» ✓; `plan:573` «~90 → **99**» ✓.
· «ANTES DE CONSTRUIR, BUSCAR» PASADO: no existe ningun `check-cita*` en los dos repos, y `check-doc-sync.bash` (431 l.) comprueba SIMBOLOS MUERTOS citados como vigentes, no citas literales entre documentos. `check-citas.bash` seria nuevo de verdad.

LO CORRECTO, en tres puntos:

(A) M-14 SE ESCRIBE, pero con el recuento honesto: **3 de 5 cotizaciones** refutadas en el SUJETO (063, 067, 068), **1 contraejemplo** (064) y **1 parcial** (066); y aparte, **2 deudas sin cotizar** (062, 065) en las que el riesgo DECLARADO —no cotizado— tambien se resolvio por una definicion o una identidad. No publicar «5 de 7 · umbral alcanzado»: son dos poblaciones y la regla las trata distinto (a las de cifra las gobierna el control «firma + consumidor delante de la cifra»; a las otras no las toca).

(B) DE LAS CUATRO ENMIENDAS, SOLO DOS SE HACEN: (2a) y (2b), las dos verificadas arriba. (2c) se reescribe como lo que es —una parafrasis entrecomillada, no una cita fabricada— y, si se toca, se toca con `⚠️ parafrasis` y la cita literal al lado, sin gravedad alta. (2d) NO se hace: descansa en dos usos incompatibles de «serie» y en un cotejo (260 l. contra ~250-350) que ADR-057 nunca formula.

(C) SE RETIRA EL «0,2 %». Del control de unidad sobrevive el HECHO (ADR-062 cuenta totales, ADR-063 no-blancas, y las dos dicen «con documentacion») y la consecuencia sana: **fijar la unidad antes de cotejar**. No sobrevive la inversion de la conclusion, refutada por la H de la misma ADR-056 (110 l. de codigo contra el mismo rango ~850-1400). Y `check-citas.bash` sigue justificado: habria cazado (2b) —que es el defecto que de verdad fabrica el patron— pero NO (2c), porque una parafrasis entrecomillada no la caza un `grep -F`; eso hay que decirlo al proponerlo, o el control nace prometiendo mas de lo que comprueba (que es [[feedback-controles-que-no-comprueban]]).


---

## Parte II · LOS CUATRO PLANES DE CAPA — **los cuatro refutados**

> 🔑 La convergencia de los cuatro refutadores es el producto: la capa 0 real es la
> capa de OPERACIONES de `FOL/FOL.lean`, el parámetro tiene que llamarse `Sym`, y
> `Fresh0` no puede retirar sus seis declaraciones de `String`. Eso es ADR-069.

---

### G0 · Plan de capa: el núcleo (`FOL/FOL.lean`)
**¿sobrevive?** **⛔ NO**

**Orden que proponía:** **0-A → 0-B → 0-C**, y el orden lo fijan DOS DAGs, no uno.

(1) **El DAG definicional DENTRO del fichero** — es el que puede romper el build a medio camino, y es asimétrico: generificar un CALLEE con el CALLER todavía monomórfico siempre compila (`S` unifica a String); generificar un CALLER con el callee monomórfico es ERROR DE TIPO. Por tanto callee-antes-que-caller, siempre. Aristas medidas: `top` → `neg` (FOL.lean:75); `liftFormula` → `liftTerms`,`liftTerm` (117,118); `substFormula` → `substTerms`,`substTerm`,`liftTerm` (145,146,148,151); `Derives` → todo lo anterior. `iff`, `getAt?`, `replaceAt`, `LocalRule` y los tres shims no tienen aristas de salida dentro del fichero. Dentro de 0-C: los dos bloques `mutual` (103-112, 127-140) ANTES que `liftFormula` (114) y `substFormula` (142).

(2) **El DAG de imports**, que decide el ORDEN ENTRE PASADAS por radio de explosión medido sobre los 10 módulos que importan `FOL.FOL` directamente (Classical, Core, DecEq, Deduction, Derives0, Enumeration, MetaRules, Semantics, Tactics, Tactics2). Conteo por grupo:
 - neg/top/iff: Classical 2, Derives0 4, MetaRules 1 → **7** — pasada 0-A, la más barata.
 - getAt?/replaceAt/LocalRule: Derives0 3, Semantics 26, Tactics 1 → **30**, y CERO en RPP → pasada 0-B.
 - lift/subst: Derives0 6, MetaRules 3, Semantics 56 → **65** en los importadores directos, y **13 431** ocurrencias en RPP → pasada 0-C, la última.

Se sube por radio creciente para que cada verde y cada tabla de footprints aísle un riesgo distinto (ADR-068 §5, nada de big-bang). ⚠️ 0-B y 0-C son mutuamente independientes (ninguna llama a la otra), así que el orden entre ellas es una elección: la pongo así porque 0-B lleva el riesgo *cualitativo* (recursión bien fundada, lemas de ecuación) y 0-C el *cuantitativo*, y si se hacen al revés un fallo de 0-B llegaría enmascarado por el ruido de 0-C.

⚠️ Y una corrección medida al orden que el propietario propuso («Fresh0 → Enumeration → Lindenbaum/Henkin»): eso es capa 1, pero conviene saber ya que **`Enumeration` no comparte NINGUNA de las 15 declaraciones de esta capa** — medido: 0 usos de lift/subst, 0 de getAt?/replaceAt/LocalRule, 0 de neg/top/iff, 0 de Derives. Sí menciona Term/Formula 19 veces y su bloqueante propio es la estructura de String en `natToString` (Enumeration.lean:184-189: `String.ofList`, `s.toList`, `Char.ofNat`), que es exactamente lo que `EnumSym` sustituye. ⇒ **capa 0 y `Enumeration` pueden ir EN PARALELO**; lo que no puede ir en paralelo es Fresh0/Lift0/Rename/Eigenvariable, que consumen `liftFormula`/`getAt?` y por tanto van DESPUÉS de 0-B y 0-C.

**Dónde decía que estaba el riesgo:** **El riesgo NO está en FOL.lean. Está en 12 líneas de tres módulos BLOQUEADOS de la capa 1, y ninguna de ellas la escribe esta capa.**

Dentro de FOL.lean no hay un solo `rfl` que pueda romperse: el fichero no tiene ninguna prueba salvo los tres shims (`rw [FormulaG.ex.injEq] at h; exact h`, FOL.lean:69) y dos `heq_of_eq`. Lo que la capa 0 cambia son los **lemas de ecuación**, y sus consumidores están fuera:

1. ⛔ **Los 12 sitios `rfl` sobre `getAt?`/`replaceAt`** (pasada 0-B), CONTADOS: nueve de la forma `simp only [getAt?, ..., ih, posDepth] <;> rfl` — Eigenvariable.lean:244,245,249; Lift0.lean:163,164,168; Rename.lean:218,219,220 — y tres de la forma `rw [abs_getAt?, hget]; rfl` — Eigenvariable.lean:337; Lift0.lean:247; Rename.lean:298. Ojo con el matiz que el proyecto tiene medido: el `rfl` que `rw` dispara SOLO va a transparencia `reducible`; el `rfl` que aquí está ESCRITO es la táctica, a transparencia por defecto. Es decir, estos 12 ya están protegidos precisamente porque alguien escribió el `rfl` a mano. Donde sí puede aparecer el fallo with_reducible es en cualquier `rw` de esos ficheros que HOY cierre solo y mañana no, porque `Term` es `abbrev` (reducible) pero `@liftTerm S` no despliega a `reducible`. Eso no se mide leyendo: lo mide el compilador.

2. ⚠️ **Los `theorem ... := rfl` que dependen de que lift/subst DESPLIEGUEN** (pasada 0-C). Medidos: Theorems/Quantifiers.lean:74 y :77 (`substFormula v t (.and A B) = ... := rfl`, `liftFormula c (.and A B) = ... := rfl`), SkolemNF0.lean:181, y en RPP ChainOkBoundedPrf.lean:352,355 y :175,:314,:767, ChainPrf.lean:716,741. Si `liftTerm`/`substTerm` dejaran de compilarse por recursión estructural al añadir `{S}`, estos `:= rfl` caen en cadena y con ellos los certificados de Herbrand. ESTIMADO: no caen, y el precedente es MEDIDO — `decEqTerm` (DecEq.lean:64-91) es exactamente una recursión mutua estructural sobre `TermG S` / `List (TermG S)`, se generificó en ADR-068 y siguió reduciendo: Herbrand0.lean:302 cierra con `(by rfl)` y FOL dio 53 jobs verde. Es la única evidencia disponible sin compilar, y es evidencia sobre OTRA función.

3. ⛔ **Lo que de verdad va a doler, y no es técnico: los candados.** De los 10 importadores directos, 5 están en `locked_files.txt` (Core, DecEq, Derives0, Enumeration, MetaRules) y de los 3 ficheros del riesgo (1) los 3 están bloqueados (Eigenvariable, Lift0, Rename). El protocolo de `git-lock.bash` es «desbloquea SOLO el fichero objetivo» — una pasada que rompe 12 líneas repartidas en 3 módulos bloqueados choca de frente con el protocolo. Eso hay que decidirlo ANTES de empezar, no al toparse con el hook de pre-commit.

4. 🔑 **Y el riesgo de DOCUMENTACIÓN, que es el que este proyecto tiene tipificado.** El docstring de FOL.lean:22-25 afirma hoy: «⛔ Lo que esto todavía no hace: **nada del árbol es genérico aún**». En cuanto entre la pasada 0-A esa frase es FALSA, y es exactamente la clase de cabecera que el encargo lateral [A1] persigue (el precedente SkolemNF0/HerbrandBlock0). Cada pasada tiene que reescribir ese bloque, no sólo compilar.

Y una advertencia sobre dónde NO está el riesgo, porque yo mismo lo puse ahí antes de medirlo: creí que el peligro sería `⊤`/`¬`/`⇔` volviéndose polimórficos y dejando `?S` sin resolver. Medido, `⊤` no se usa como fórmula ni una sola vez en los dos repos. El riesgo declarado estaba en una construcción y el real está en una decisión de operativa (los candados) y en 12 líneas de terceros — que es, literalmente, el sesgo que el encargo [A5] propone elevar a M-14.

**Estimación:** **Lo CONTADO (no estimado), leyendo el árbol:**
- 39 declaraciones en FOL.lean; 2 ya hechas (TermG, FormulaG); **15 a tocar**; 24 que se quedan.
- **17 líneas de FIRMA cambian**, y son éstas, una por una: 52, 54 (Term.noConfusion) · 63, 65 (Formula.noConfusion) · 68 (Formula.ex.inj) · 73 (neg) · 75 (top) · 77 (iff) · 103 (liftTerm) · 108 (liftTerms) · 114 (liftFormula) · 128 (substTerm) · 136 (substTerms) · 142 (substFormula) · 164 (getAt?) · 180 (replaceAt) · 204 (LocalRule). Ningún CUERPO necesita tocarse: están todos escritos con constructores anónimos (`.var`, `.func`, `.impl`…), que ya unifican `S`.
- Las 8 apariciones del token `String` están en 6 líneas: 14 (docstring), 43, 44, 54 (×2), 65 (×2), 92. Destino de cada una: 14 se reescribe (queda mintiendo), 43 y 44 SE QUEDAN (son el ancla), 54 y 65 pasan a `(S := S) (S' := S)`, 92 es la decisión abierta (Coe, 0 usos medidos).
- 0 usos de la estructura de String en FOL.lean. 2 literales de cadena, ambos en el ejemplo (276, 284).

**Lo ESTIMADO (marcado como tal, y no lo he compilado):**
- **ESTIMADO 30-45 líneas de diff** en FOL.lean para la capa entera: las 17 de firma, más **ESTIMADO 10-20** de reescritura del docstring de cabecera (líneas 10-26, que quedan falsas), más **ESTIMADO 3-8** de ascripciones defensivas si el elaborador no infiere solo los tipos de `A B C` en `LocalRule.commuteImpl` (FOL.lean:205) ni los de `liftTerms`/`substTerms` en las llamadas mutuas.
- **ESTIMADO 0-15 líneas de reparación en la capa 1** por la pasada 0-B (los 12 sitios `rfl` de Eigenvariable/Lift0/Rename). Puede ser 0 y puede ser 12; no hay forma de saberlo sin `lake build`, y los tres ficheros están bloqueados.
- **ESTIMADO 0 líneas en RPP.** Base: ADR-068 midió que RPP sólo necesitó Meta/HilbertSeq.lean, y esta capa no toca `Derives` (197 citas medidas), ni getAt?/replaceAt (0 citas en RPP), y las 13 431 ocurrencias de lift/subst se instancian solas en String. ⚠️ Es una ESTIMACIÓN por analogía con el paso anterior, no una medición.
- **ESTIMADO: los 147 footprints, IDÉNTICOS.** Razón: ninguna de las 15 declaraciones cambia de valor definicional en `S := String`. Pero esto es exactamente lo que ADR-068 §5 obliga a RE-MEDIR con su tabla por pasada, y una estimación de footprint no vale como control.

⚠️ Y el aviso que el encargo lateral pide que repita de mi propia cifra: todo el bloque «ESTIMADO» de arriba lo produce un agente que **no compila**. Que lo mida el compilador antes de que entre en ningún plan.

#### Módulos

| fichero | l. | decls. a tocar | clases | bloqueantes |
|---|---|---|---|---|
| `FOL/FOL.lean · PASADA 0-A — shims de noConfusion + conectivos derivados (líneas 49-77)` | 29 | 6 | ninguna | Ninguno estructural. Las seis son `Term.noConfusion` (FOL.lean:52-54), `Formula.noConfusion` (63-65), `Formula.ex.inj` (68-69), `neg` (73), `top` (75), `iff` (77). El único texto que menciona String es el `(S := String) (S' := String)` de FOL.lean:54 y FOL.lean:65 -> pasa a `(S := S) (S' := S)`. MEDIDO sobre los consumidores: `Formula.noConfusion` tiene 13 sitios de llamada explícitos (BlockExtraction0.lean:178,240,300,359 y Sequent0.lean:227,238,248,292,318,354,365,371,413); `Formula.ex.inj` tiene 2 (BlockExtraction0.lean:379, Sequent0.lean:425); y `Term.noConfusion` tiene **CERO** sitios de llamada en los dos repos -> es un shim sin consumidor, y la decisión honesta es generificarlo o borrarlo, no darlo por usado. ⭐ Y una alarma que la medición DESACTIVA: temía que `top` al hacerse polimórfico dejara `⊤` sin `S` resoluble; medido, `⊤` aparece 4 veces en los dos repos y las CUATRO son la propia declaración de notación (FOL.lean:81) y tres comentarios/docstrings (EvalLiftcPrf.lean:826, Axioms.lean:7 y :1262). `⊤` no se usa como fórmula en ningún sitio ⇒ riesgo cero, medido. |
| `FOL/FOL.lean · PASADA 0-B — navegación y reglas locales (líneas 153-206)` | 54 | 3 | ninguna | `getAt?` (FOL.lean:164), `replaceAt` (FOL.lean:180), `LocalRule` (FOL.lean:204). ⭐ `Pos` (FOL.lean:156) NO se toca: CONTADO, sus 4 constructores no mencionan Term/Formula ni String — es libre de símbolos. ⛔ Sobre la pregunta explícita «getAt?/replaceAt NO REDUCEN, ¿cambia al generificar?»: NO cambia, y la razón medida está en Derives1.lean:63-67 — no reducen porque las dos llamadas recursivas cambian *los dos* argumentos a la vez (`getAt? f1 p'` desde `getAt? f p`), así que `f` no es prefijo fijo y Lean cae en recursión BIEN FUNDADA. Añadir `{S : Type}` añade un prefijo que SÍ es fijo en todas las llamadas recursivas, luego no altera la medida de terminación ni el esquema: siguen siendo WF. Lo que sí cambia son sus lemas de ecuación, y AHÍ está el consumidor real, todo en capa 1: 9 sitios `simp only [getAt?/replaceAt, ...] <;> rfl` (Eigenvariable.lean:244,245,249; Lift0.lean:163,164,168; Rename.lean:218,219,220) y 3 sitios `rw [..._getAt?, hget]; rfl` (Eigenvariable.lean:337; Lift0.lean:247; Rename.lean:298). Los tres ficheros están LOCKED. En RPP: CERO usos de getAt?/replaceAt/LocalRule/rewrite_at (medido, grep vacío) ⇒ esta pasada no puede tocar RPP. |
| `FOL/FOL.lean · PASADA 0-C — lift y sustitución (líneas 98-151)` | 54 | 6 | ninguna | `liftTerm`/`liftTerms` (mutual, FOL.lean:103,108), `liftFormula` (114), `substTerm`/`substTerms` (mutual, 128,136), `substFormula` (142). NINGUNA usa la estructura de String: medido, en FOL.lean no hay ni un `++`, ni `toString`, ni `toList`, ni `Char`, ni `.length`, ni comparación — las únicas apariciones de esos tokens son en el docstring de la línea 18. El símbolo viaja INERTE: `.func f ts` copia `f` sin mirarlo. ⚠️ Es la pasada de mayor superficie con diferencia: ocurrencias CONTADAS en RPP — liftTerm 5424, substTerm 5030, substFormula 2141, liftFormula 836 (total 13 431) — y ninguna cambia, porque la técnica de ADR-068 conserva el nombre y `S` se instancia sola en String. ⚠️ Dependencia INTERNA que fija el orden: `liftFormula` llama a `liftTerms`/`liftTerm`, y `substFormula` llama a `substTerms`/`substTerm` Y a `liftTerm 0 s` (FOL.lean:148,151) ⇒ los mutuos ANTES que los de fórmula, o el paso intermedio no typechequea. |
| `FOL/FOL.lean · LO QUE NO SE TOCA (24 declaraciones contadas)` | 102 | 0 | ninguna | ⛔⛔ `Derives` (FOL.lean:211-268, 22 constructores CONTADOS) se queda en String, y NO por las citas sino por M-11. (1) Las citas: la cifra «320» del encargo es falsa — medido, `Derives` sin subíndice aparece **197 veces en RPP** (33 ficheros; el mayor es Meta/Hilbert.lean con 43) y **393 veces en FOL**; a eso se suma la notación `⊢` con 2101 ocurrencias no-comentario en RPP. (2) La razón de fondo: `Derives` es el ÚNICO tipo de la lista negra de M-11, y está habitado por 4 `axiom` medidos en MetaRules.lean:78,110,145,159 (`imp_intro`, `raa`, `or_elim`, `ex_elim`) más los que el censo de MetaRules declara en Theorems/Neg.lean:57 y Theorems/Quantifiers.lean:115, más `ax_induction_prim` (Full/Induction.lean:251) y `ax_axiomsCodeT_eq` (Minimal/Axioms.lean:1624) en RPP. Generificarlo convertiría **un** tipo prohibido en una **familia** de tipos prohibidos y obligaría a reenunciar los axiomas-habitante. (3) Y NO rompe nada dejarlo: sus constructores mencionan `liftFormula 0`, `substFormula 0 t A`, `neg`, `⊥`, `getAt?`, `replaceAt`, `LocalRule` con `Γ : List Formula` ya fijado, así que `S := String` sale por unificación. El único punto de contacto con la vía genérica es `derives0_to_derives` (Derives0.lean:157), que es UNIDIRECCIONAL y se queda anclado en String — y el propio docstring de Derives0.lean:155-156 ya lo dice: «Toda la metateoría vive de este lado; `Derives` se queda como herramienta». Tampoco se tocan: `abbrev Term`/`abbrev Formula` (43,44 — son el ancla), los 2 `export` (47,58 — exportan de TermG/FormulaG, ya genéricos), las 11 notaciones (80-89,96 — apuntan a constantes), `infix ⊢` (270), `Pos` (156), y los 3 defs del ejemplo `formula_ejemplo`/`posicion_Q`/`formula_simplificada` (275,280,283). ⚠️ BLOQUEANTE REAL, el único del fichero: `formula_ejemplo` usa literales `"P"`/`"Q"` (FOL.lean:276) y `formula_simplificada` depende de él (FOL.lean:284) ⇒ se quedan en String necesariamente. ⚠️ DECISIÓN PENDIENTE: `instance : Coe String Formula` (FOL.lean:92). Es la única declaración que menciona String por una razón que no es el `abbrev`. Medido: **CERO usos** en los dos repos (ni `⊢ "..."` ni `("..." : Formula)`). Generificarla a `Coe S (FormulaG S)` metería una instancia con cabeza variable que el elaborador probaría en toda coerción fallida; recomiendo dejarla en String o borrarla, y en ningún caso generificarla «por simetría». |

#### ⚖️ La refutación — **MANDA ÉSTA**

NO SOBREVIVE. Lo que mato no es que no vaya a compilar (probablemente compile): es que el plan publica como MEDIDO lo que no midio, y su unica justificacion numerica —el orden de las pasadas por "radio de explosion"— esta calculada sobre un conjunto de ficheros que no es el real.

=== [R1] "10 importadores directos de FOL.FOL" es FALSO: son 16 (MEDIDO) ===
`grep -rln "^import FOL.FOL$" FOL/` da: Classical, Core, DecEq, Deduction, Derives0, Enumeration, MetaRules, Semantics, Tactics, Tactics2 **+ Theorems/Deduction, Theorems/Derived, Theorems/Eq, Theorems/Impl, Theorems/Neg, Theorems/Quantifiers**. Los seis de `Theorems/` no aparecen en el plan, y `FOL/Theorems/Eq.lean` SI esta en locked_files.txt. Los tres radios (7 / 30 / 65) estan medidos sobre 10 de 16 ficheros ⇒ el ORDEN 0-A→0-B→0-C, que es lo unico que el plan argumenta con numeros, no esta justificado. Ironia medida: el plan cita `Theorems/Quantifiers.lean:74,77` en `riesgo_real` como "capa 1" cuando es importador DIRECTO — y ahi mismo (lineas 69-75) hay `simp only [liftFormula, substFormula, liftTerm, ...]`, que es capa 0 pura.

=== [R2] ⛔⛔ La "alarma que la medicion DESACTIVA" es una medicion FALSA ===
El plan: «medido, `⊤` aparece 4 veces en los dos repos y las CUATRO son la propia declaracion de notacion y tres comentarios. `⊤` no se usa como formula en ningun sitio ⇒ riesgo cero, medido.»
MEDIDO por mi: `grep -rnw "top"` ⇒ **FOL/Craig0.lean:344** `refine ⟨top, ?_, LKp.ax _ _ A (List.Mem.tail _ h1) h2, ?_, ?_⟩` y **FOL/Craig0.lean:353** `refine ⟨top, LKp.implR _ _ Formula.bottom Formula.bottom ...⟩`. `top` SI se usa como formula, dos veces, en un fichero LOCKED donde vive `craig` (teorema publicado con fila propia). El plan grepeo la NOTACION y nunca el IDENTIFICADOR: es exactamente «casar por subcadena que ABSUELVE» (feedback_controles_que_no_comprueban). Ademas son dos `refine ⟨top, ...⟩`, es decir, `top` en posicion de testigo dentro de un constructor anonimo — el peor sitio para un `{S}` implicito sin argumentos de los que inferirlo.

=== [R3] La pasada 0-A NO es "la mas barata" ===
Plan: «neg/top/iff: Classical 2, Derives0 4, MetaRules 1 → 7 — la mas barata».
MEDIDO: `neg` como identificador = 133 lineas en 21 ficheros de FOL y 173 lineas en RPP; `iff` = 13 lineas en FOL, 8 de ellas en `Prenex0.lean`. De los ficheros que usan neg/iff/top hay **17 LOCKED**: Canonical0, Craig0, Derives0, Derives1, Derives2, Eigenvariable, Henkin0, Herbrand0, Lift0, MetaRules, NDtoLK0, Prenex0, PrenexNF0, Propositional0, Rename, SkolemHerbrand0, Soundness0. El plan subestima 0-A por dos ordenes y la coloca primera POR ESO.

=== [R4] 0-C: el plan mide 3 ficheros; son 32, y 29 LOCKED ===
MEDIDO: tocan liftFormula/substFormula/liftTerm/substTerm/liftTerms/substTerms 32 ficheros de FOL/. Libres: solo FOL.lean, Semantics.lean, Theorems/Quantifiers.lean. LOCKED: BlockExtraction0, Canonical0, Craig0, Derives0, Derives1, Derives2, Eigenvariable, Eq0, Finitary0, Hauptsatz0, Henkin0, HenkinLimit0, Herbrand0, HerbrandBlock0, Lift0, Lindenbaum0, MetaRules, NDtoLK0, Prenex0, PrenexNF0, Rename, Sequent0, SequentSound0, Skolem0, SkolemHerbrand0, SkolemN0, SkolemNF0, Soundness0, Theorems/Eq (29).

=== [R5] 0-B: faltan dos consumidores, los dos LOCKED ===
MEDIDO, ficheros con getAt?/replaceAt: Derives0, **Derives1**, Eigenvariable, FOL.lean, Lift0, Rename, Semantics, **Soundness0**. El plan no nombra Derives1 ni Soundness0. `Soundness0` aloja `derives0_soundness`, `derives0_consistent`, `derives0_not_complete` = TRES filas de la tabla de footprints. Y `LocalRule` (que el plan mete en 0-B) tiene consumidores con PRUEBA en cuatro ficheros que no lista: Eigenvariable.lean:266-270, Lift0.lean:183-187, Rename.lean:232-237 (LOCKED los tres) y Semantics.lean:275, mas Derives1.lean:41,215,283 (LOCKED). El "Tactics 1" que si cuenta es un COMENTARIO (Tactics.lean:33): el control cuenta su propio andamio. `RPP = 0` si lo acerto (medido: 0).

=== [R6] Contradiccion interna de cifras (M-13) ===
En `capa`: «**6** de sus 10 importadores directos SI estan bloqueados (Core, DecEq, Derives0, Enumeration, MetaRules)» — enumera CINCO. En `riesgo_real`: «**5** estan en locked_files.txt». MEDIDO: de los 16 importadores reales hay 6 bloqueados (esos cinco + Theorems/Eq.lean). El plan acierta el 6 por un error de conteo, no por medicion.

=== [R7] No se consulto frozen_files.txt ===
`git-lock.bash` tiene DOS listas y FREEZE no se desbloquea (hay que crear `*Ext.lean`). El plan afirma la operativa («la capa 0 se edita sin desbloquear nada») mirando solo una. MEDIDO: `FOL/frozen_files.txt` = 1 entrada (`cuarentena/Inconsistencia.lean`) ⇒ la conclusion resulta correcta, pero por suerte.
✅ Lo que SI verifique a favor del plan: `FOL/FOL.lean` no esta en `locked_files.txt` (la entrada `FOL.lean` es el barrel raiz) y `is_locked()` usa `grep -Fxq` (linea EXACTA), asi que no hay absolucion por subcadena. Ese punto del plan es correcto y esta bien medido.

=== [R8] Footprints: el plan estima bien pero no nombra las filas en riesgo ===
La tabla esta en `ROBINSON_PlusPlus/check-footprints.bash`. Las filas FRAGILES son las tres con footprint `-` (CERO axiomas): `FOL.HenkinLimit0.not_occurs_henkinAx|-`, `FOL.Canonical0.eval_pullback_formula|-`, `FOL.DecEq.instDecidableEqTerm|-`. Cualquier `Classical` que entre por un cambio de esquema de recursion las rompe, y `eval_pullback_formula` es induccion sobre Formula con las ecuaciones de lift/subst. El plan dice «ESTIMADO: los 147 footprints, IDENTICOS» (etiquetado, correcto) pero no dice CUALES vigilar, que es lo unico accionable.
Y su apoyo central es debil: para sostener que los `:= rfl` no caen cita el precedente de `decEqTerm` — OTRA funcion. Los dos datos MEDIDOS del proyecto sobre este fichero apuntan en direcciones opuestas: `DecEq.lean:29-31` («`deriving DecidableEq for Term` NO funciona: es un inductivo ANIDADO») y `Derives1.lean:63-67` («`getAt?`/`replaceAt` se compilan por recursion BIEN FUNDADA y `rfl` NO las abre»). Es decir: en FOL.lean conviven funciones que reducen y funciones que no, y el plan no tiene medido en cual de los dos grupos cae `liftTerm`/`liftTerms` ni si anadir `{S}` (que mete un `SizeOf S` por `instSizeOfDefault`) mueve la frontera. Eso solo lo dice el compilador — y el plan lo reconoce, pero DESPUES de haber llamado "medida" a la conclusion.

=== [R9] LENTE DE VACUIDAD: al final de la capa 0, `S := List Char` NO es posible ===
No por culpa del plan (es modulo-a-modulo por ADR-068 §5), pero el plan no lo dice y deberia. Falta, medido: (a) `Term`/`Formula` siguen siendo `abbrev ... String` y los usa todo el arbol; (b) `Derives` se queda en String de forma PERMANENTE por decision del propio plan; (c) `Derives0` —donde vive TODA la metateoria publicada: completeness₀, hauptsatz, herbrand, craig, compactness0...— no se toca, y sus constructores mencionan liftFormula/substFormula/getAt?/LocalRule, asi que hasta que Derives0 no sea generico ningun teorema publicado se puede enunciar sobre otro S; (d) `FreshSym` y `EnumSym` no se mencionan NI UNA VEZ en el plan, y sin ellas Fresh0/Enumeration/Lindenbaum/Henkin no cruzan. La capa 0 es NECESARIA y NO SUFICIENTE, y el plan no enuncia el resto.
Y hay una vacuidad real y concreta: `Term.noConfusion` tiene **CERO** sitios de llamada en los dos repos (lo confirmo midiendo). El plan propone «generificarlo o borrarlo» sin decidir. Generificar un shim sin consumidor es trabajo cuyo unico efecto observable es mover un `#print axioms`.

=== [R10] `Coe String Formula`: conclusion correcta, argumento invalido ===
Confirmo que la unica declaracion viva es FOL/FOL.lean:92. Pero una `Coe` se inserta IMPLICITAMENTE y es invisible a grep: «CERO usos medidos» no es una medicion posible por lectura. Dejarla en String (lo que el plan recomienda) es lo correcto; BORRARLA —la otra opcion que ofrece— no esta respaldado por nada.

=== [R11] Cifras de `Derives` no reproducibles ===
Plan: 197 en RPP, 393 en FOL. MEDIDO por lineas (`grep -rnw Derives`): **163 en RPP**, **1001 en FOL**. Si el plan contaba ocurrencias, falta el ambito (M-13). No cambia la decision (Derives se queda), pero es otra cifra publicada sin decir que se conto.

=== LO QUE SI SOBREVIVE, verificado linea a linea ===
- 39 declaraciones en FOL.lean, 2 hechas, **15 a generificar**, 24 intactas: lo reconte y sale exacto.
- Las **17 lineas de firma** (52,54,63,65,68,73,75,77,103,108,114,128,136,142,164,180,204): correctas.
- Las **8 apariciones de `String` en 6 lineas** (14,43,44,54,65,92): exacto, verificado con grep.
- `Formula.noConfusion` = **13** sitios: exacto. `Formula.ex.inj` = **2** (BlockExtraction0:379, Sequent0:425): exacto. `Term.noConfusion` = **0**: exacto.
- getAt?/replaceAt/rewrite_at en RPP = **0**: exacto.
- `Pos` (156-161) no menciona Term/Formula/String: correcto, no se toca.
- El DAG definicional interno (callee antes que caller; los dos `mutual` antes que liftFormula/substFormula) y la asimetria «generificar el callee siempre compila, el caller no»: razonamiento correcto.
- El argumento M-11 para dejar `Derives` en String (4 axiomas-habitante en MetaRules.lean:78,110,145,159): solido, y es la parte mejor del plan.
- El bloque `estimacion` SI lleva su etiqueta ESTIMADO y su aviso final: ahi la regla 5 se cumple. La violacion esta FUERA de ese bloque, en `bloqueantes` y `orden`, donde «medido» aparece sobre [R2], [R3] y [R4].

**Lo correcto:**

LO CORRECTO, y en este orden:

(1) REHACER EL CENSO DE CONSUMIDORES SOBRE EL CIERRE TRANSITIVO, NO SOBRE LOS IMPORTADORES DIRECTOS. Los tres conjuntos, medidos por mi y listos para usar:
   - neg/top/iff → 21 ficheros en FOL (133 lineas de `neg`) + 173 lineas en RPP; 17 de esos ficheros LOCKED.
   - getAt?/replaceAt/LocalRule → Derives0, Derives1, Eigenvariable, Lift0, Rename, Semantics, Soundness0 (+FOL.lean); 6 LOCKED; 0 en RPP.
   - lift/subst → 32 ficheros en FOL, 29 LOCKED; libres solo Semantics y Theorems/Quantifiers.
  Con esos numeros el orden por "radio creciente" es 0-B (7 ficheros) → 0-A (21) → 0-C (32), NO el que el plan propone. Si se prefiere mantener 0-A primero, hay que argumentarlo por otra cosa que el radio.

(2) CORREGIR LAS DOS AFIRMACIONES FALSAS ETIQUETADAS COMO MEDIDAS:
   - `top` SI se usa como formula: FOL/Craig0.lean:344 y :353. Retirar la frase «⊤ no se usa como formula en ningun sitio ⇒ riesgo cero, medido» y sustituirla por el caso concreto: dos `refine ⟨top, ...⟩` en un fichero LOCKED que aloja `craig`. Si `top` se hace `{S}`-polimorfico, esos dos sitios son el primer candidato a `(top : Formula)`.
   - «10 importadores directos» → 16, con los seis de FOL/Theorems/ y Theorems/Eq.lean LOCKED.
   - Unificar el 6-vs-5 de bloqueados: son 6 de 16.

(3) ANADIR AL PLAN LA SECCION QUE FALTA: «que NO desbloquea esta capa». Enunciar explicitamente que al terminar la capa 0 `S := List Char` sigue sin poder instanciarse en ningun teorema publicado, y que el camino restante es Derives0 (22 constructores) + FreshSym/EnumSym + Enumeration/Fresh0/HenkinLimit0/Lindenbaum0/Canonical0. Sin esa seccion el plan invita a leer la capa 0 como si comprara algo, y no compra nada instanciable.

(4) NOMBRAR LAS TRES FILAS DE FOOTPRINT EN RIESGO, que son las unicas con `-` (cero axiomas) en ROBINSON_PlusPlus/check-footprints.bash: `FOL.HenkinLimit0.not_occurs_henkinAx`, `FOL.Canonical0.eval_pullback_formula`, `FOL.DecEq.instDecidableEqTerm`. Y anadir, por cada pasada, las filas de `Soundness0` (derives0_soundness, derives0_consistent, derives0_not_complete), que la pasada 0-B toca y el plan no mencionaba.

(5) DECIDIR LOS DOS HUERFANOS EN VEZ DE DEJARLOS ABIERTOS. `Term.noConfusion`: 0 consumidores medidos ⇒ BORRARLO, no generificarlo (generificar un shim sin consumidor es trabajo puro). `instance : Coe String Formula`: dejarla EXACTAMENTE como esta y escribir en el docstring que un grep no puede demostrar que una `Coe` no se usa — no es candidata a borrado sin compilador.

(6) LA PRIMERA MEDICION QUE HAY QUE PEDIRLE AL COMPILADOR, antes de escribir ninguna pasada, es UNA y es barata: si `liftTerm`/`liftTerms` se compilan hoy por recursion estructural o bien fundada, y si eso cambia al anadir `{S : Type}` (que introduce un `SizeOf S` por `instSizeOfDefault`). De esa unica respuesta dependen los ~8 `theorem ... := rfl` sobre lift/subst (Theorems/Quantifiers.lean:74,77; SkolemNF0.lean:181; RPP ChainOkBoundedPrf.lean:175,314,352,355,767; ChainPrf.lean:716,741) y el `by rfl` del certificado de Herbrand (Herbrand0.lean:302). El precedente de `decEqTerm` que el plan invoca es OTRA funcion y no responde a esto.

(7) Y la decision de operativa que el plan si identifica bien y hay que tomar ANTES de tocar nada: 29 de los 32 ficheros afectados por 0-C estan LOCKED, y el protocolo de git-lock.bash es «desbloquea SOLO el fichero objetivo». O se acuerda una excepcion escrita para esta migracion, o la capa 0 choca con el hook de pre-commit en la primera pasada.

---

### G1 · Plan de capa: `Enumeration`
**¿sobrevive?** **⛔ NO**

**Orden que proponía:** DENTRO DE LA CAPA el DAG interno de Enumeration.lean impone esto, y el orden correcto NO es el de la cabecera del fichero (capa 0→1→2→3→4) sino uno partido en DOS VERDES, y la razón es la tabla de footprints, no la compilación:

PASO 0 (no toca nada): promover la clase. `class EnumSym (S : Type)` + `instance : EnumSym String := ⟨natToString, natToString_surj⟩`, insertados entre la línea 189 (fin de capa 2) y la 191 (cabecera de capa 3). Es el único sitio posible: la instancia necesita natToString_surj (:186) y la clase la necesitan natToTerm (:196) y natToFormula (:291). Cero declaraciones existentes modificadas; VERDE trivial.

VERDE A — capas 0/1/2 intactas + tamaños + capa 3 (7 declaraciones): termSize:223, termsSize:227 ({S} sólo, sin instancia — recursión mutua estructural, forma ya medida verde en sondeos/SymbolParam.lean:26-33), luego natToTerm:196, natToTerms:211 ({S}[EnumSym S], mutual WF), term_surj_aux:235, natToTerm_surj:268, natToTerms_surj:271.
⭐⭐ POR QUÉ ESTE CORTE: check-footprints.bash NO tiene fila para natToTerm_surj ni para natToTerms_surj (medido: la única fila de Enumeration en las 147 es la 29, `FOL.Metamath.Enumeration.natToFormula_surj|Classical.choice,Quot.sound,propext`). Y en el VERDE A natToFormula sigue en String y sigue llamando a natToString_surj:327 ⇒ la fila 29 NO SE MUEVE. ⇒ el VERDE A no mueve NINGÚN titular publicado. Es gratis en términos de documentación, y aun así es donde está todo el riesgo técnico (el mutual WF con instancia en el prefijo fijo). Se mide el riesgo caro con la factura documental a cero.

VERDE B — capa 4 (4 declaraciones): formulaSize:278 ({S}), natToFormula:291, formula_surj_aux:317, natToFormula_surj:374.
⛔ AQUÍ y sólo aquí se mueve la fila 29. Y hay que actualizar CINCO sitios, no uno (medido): check-footprints.bash:29, FOL/AXIOMS.md:118, FOL/cuarentena/README.md:198, ROBINSON_PlusPlus/DECISIONS.md:2112 y FOL/REFERENCE.md:722 (que lista las 24 declaraciones y pasaría a 26).

EN LA MIGRACIÓN GLOBAL, Enumeration va LA PRIMERA de todo: es el único módulo cuyo único import es FOL.FOL y es INDEPENDIENTE de la cadena Fresh0 entera (Fresh0 ← Henkin0 ← Lift0 ← Eigenvariable ← Derives0 ← FOL, cuatro módulos por delante). El orden propuesto por el propietario («Fresh0 → Enumeration → …») está invertido respecto del DAG y además pone lo caro delante: HenkinLimit0 importa a LOS DOS (Fresh0:15 y Enumeration:16), así que el punto de encuentro es HenkinLimit0 y el orden entre Fresh0 y Enumeration es libre — ⇒ va primero el que no depende de nada, que es éste.

**Dónde decía que estaba el riesgo:** DÓNDE PARECE QUE ESTÁ Y NO ESTÁ:
· NO está en la recursión bien fundada, aunque la cabecera del fichero la marque con ⚠️ dos veces (:52-55). La medida es `termination_by n => n`, puro Nat, y los tres decreasing_by (:204-209, :215-219, :310-315) se cierran con unpair_fst_le/unpair_snd_le/unpair_sum_le + omega, que son capa 0 y no mencionan S. El parámetro es INERTE a la terminación (criterio de [[feedback-medir-la-forma]]).
· NO está en termSize/termsSize sobre el inductivo ANIDADO, que es lo que MÁS asusta al leerlo. Ya está medido verde: sondeos/SymbolParam.lean:26-33 compila `mutual def liftTerm {S} / liftTerms {S}` sobre `Term S` anidado. Otra medición que estaba hecha y a punto de repetirse ([[feedback-medicion-que-se-evapora]]).
· NO está en los consumidores: los 19 usos en código (10 HenkinLimit0 + 6 Lindenbaum0 + 3 Compacity0) fijan S por tipo esperado y no cambian ni una línea.

DÓNDE ESTÁ DE VERDAD, tres sitios y ninguno es una construcción:

(1) ⛔ EN UN ENUNCIADO YA ESCRITO Y MAL MEDIDO. DECISIONS.md:5291-5294 dice que con S arbitrario natToTerm_surj «DEJA DE SER DEMOSTRABLE» y marca ⬜ «no medido cuánto cuesta». Es falso: con [EnumSym S] la prueba sobrevive letra por letra y cuesta 11 declaraciones. Si eso entra en un plan tal cual, se planifica una obstrucción que no existe. Y hay un segundo enunciado contaminado por el mismo sitio: DECISIONS.md:4260 da por ✅ MEDIDO que «natToTerm_surj REFUTA que haya κ términos distintos para κ no numerable»; tras el VERDE A ese teorema pasa a ser condicional en [EnumSym S] y la refutación sólo vale instanciada en String. El teorema en String no cambia, pero la frase sí. Esto es exactamente el eje [A1] del encargo lateral: cabeceras que afirman deudas que otro ya pagó.

(2) ⛔ EN EL FOOTPRINT, Y ES UN DIVIDENDO QUE HAY QUE DECLARAR ANTES, NO DESPUÉS. sondeos/ClassicalChoiceCenso.lean:86-87 mide: «las SEIS de FOL/Enumeration.lean, que hoy vienen de String.ofList_toList». Las seis declaraciones aguas abajo de natToString_surj son, contadas: natToString_surj:186, term_surj_aux:235, natToTerm_surj:268, natToTerms_surj:271, formula_surj_aux:317, natToFormula_surj:374 — encaja EXACTO (ESTIMADO que sean esas seis; el reparto por declaración no está medido, sólo el total 6 y la causa). Al generificar, CINCO de las seis pierden Classical.choice (la choice se retira al cuerpo de `instance : EnumSym String`, que es la única que sigue descomponiendo un String) y natToString_surj se queda sola con ella. ⇒ la fila 29 de check-footprints pasa de `Classical.choice,Quot.sound,propext` a algo más limpio. ⚠️⚠️ PELIGRO DE MÉTODO: eso NO se escribe de antemano. Lo que Quot.sound y propext hagan en la prueba genérica (vienen de simp/omega, y el footprint de una táctica depende del ENTORNO DE IMPORTS) no lo sé; la fila hay que RE-MEDIRLA con `#print axioms`, no deducirla. Y la corrección va en los CINCO sitios listados, o check-footprints da verde en uno y las tres .md publican una cifra muerta.

(3) ⚠️ EN UN CONTROL QUE NO COMPRUEBA. El VERDE B añade DOS NOMBRES NUEVOS (EnumSym, instEnumSymString) a FOL/REFERENCE.md:722, que lista las 24 declaraciones del módulo. MEDIDO en check-doc-sync.bash:336-356: el bloque [C] sólo comprueba que el NOMBRE DEL MÓDULO («Enumeration.lean») aparezca en §6 — la lista de declaraciones NO está bajo ningún control. ⇒ se puede dejar obsoleta y todo da verde. Es el noveno caso de [[feedback-controles-que-no-comprueban]] y, como allí, la herramienta se arregla, la cifra nunca.

(4) ⚠️ Y el sitio que el verde no cubre: cuarentena/Completeness.lean:126-129 consume natToFormula y natToFormula_surj y NO COMPILA. Es el mismo fichero donde un `axiom` falso sobrevivió ochenta días. Hay que abrirlo a mano después del VERDE B o queda una tercera categoría —«no he podido comprobarlo»— disfrazada de verde.

**Estimación:** ⚠️ TODO LO DE ABAJO ES **ESTIMADO** salvo lo marcado MEDIDO. Ningún número de líneas escritas sale del compilador: no he construido nada (prohibición de lake en este encargo).

MEDIDO (leyendo el árbol, no estimado):
· 377 líneas en FOL/Enumeration.lean; 24 declaraciones contadas mecánicamente; 9 líneas con «String» (2 docstring, 3 en natToString/natToString_surj que no se tocan, 4 a cambiar: :202, :253, :296, :327).
· 11 declaraciones a tocar (:196, :211, :223, :227, :235, :268, :271, :278, :291, :317, :374); 13 intactas.
· 12 sitios que consumen las ecuaciones WF por simp (:249, :256, :259, :266, :325, :331, :337, :345, :350, :358, :366, :371).
· 19 usos en código en los 3 consumidores del build (HenkinLimit0 10, Lindenbaum0 6, Compacity0 3) + 2 en cuarentena (no compila) + 0 en ROBINSON_PlusPlus fuera de sondeos/.
· 1 sola fila de las 147 de check-footprints toca a este módulo (línea 29). 5 sitios publican su footprint.

ESTIMADO — líneas a tocar:
· FOL/Enumeration.lean: ~15 líneas de FIRMA (las 11 declaraciones; term_surj_aux ocupa 3 líneas :235-237 y formula_surj_aux 2 :317-318, el resto 1 cada una) + 4 líneas de CUERPO (natToString→EnumSym.enum ×2, natToString_surj→EnumSym.enum_surj ×2) + ~10 líneas NUEVAS (class EnumSym + instance, copiadas de sondeos/SymbolParamCoste.lean:73-80, no reescritas) + ~15 líneas de docstring (la fila «capa 2» de la tabla :39, la sección «Footprint» :62-65 que hoy dice «cero axiomas del proyecto» sin mencionar dónde queda la choice, y la nueva mención de la clase). **≈ 45 líneas ESTIMADO**, repartidas ≈30 en el VERDE A y ≈15 en el VERDE B.
· Consumidores (HenkinLimit0, Lindenbaum0, Compacity0): **0 líneas ESTIMADO**. Éste es el número que hay que refutar primero si falla algo; el candidato a refutarlo es Lindenbaum0:144/151 (`rw [if_pos h]` tras `by_cases`).
· Documentación y controles: 5 líneas (check-footprints.bash:29, FOL/AXIOMS.md:118, FOL/cuarentena/README.md:198, RPP/DECISIONS.md:2112, FOL/REFERENCE.md:722) + la rectificación de RPP/DECISIONS.md:5291-5294 y :4260 + un ADR nuevo. **≈ 20 líneas ESTIMADO** más el ADR.

⛔ LO QUE NO ESTÁ ESTIMADO PORQUE NO SE PUEDE ESTIMAR: si las ecuaciones de despliegue de una definición WF mutua con una INSTANCIA en el prefijo fijo siguen disparando bajo `simp [natToTerm, …]` en los 12 sitios. Eso no es una cifra, es un sí/no, y lo dice el compilador. Si sale que no, los 12 sitios pasan a `rw [natToTerm.eq_def]` o `unfold` y la estimación de 45 líneas se queda corta por un factor que no voy a inventar — que es exactamente el error de ADR-068 (~×50) que este proyecto ya pagó una vez.

#### Módulos

| fichero | l. | decls. a tocar | clases | bloqueantes |
|---|---|---|---|---|
| `E:/dropbox/github/lean4/FOL/FOL/Enumeration.lean` | 377 | 11 | EnumSym S — y BASTA TAL COMO ESTÁ en sondeos/SymbolParamCoste.lean:73-75 (enum : Nat → S ; enum_surj : ∀ s, ∃ n, enum n = s). MEDIDO contrastando los DOS únicos usos de natToString_surj: línea 253 `obtain ⟨nf,hnf⟩ := natToString_surj f` (f = símbolo de función de .func f ts) y línea 327 `obtain ⟨np,hnp⟩ := natToString_surj p` (p = símbolo de relación de .atom p ts). Los dos piden LITERALMENTE `∃ n, enum n = s` y nada más: el testigo se consume con `simp [natToTerm, hm, hr, hnf, hnts]` (256) / `simp [natToFormula, hm, hr, hnp, hnts]` (331), que cierra por TermG.func.injEq / FormulaG.atom.injEq — generados para el inductivo CON parámetro. ⇒ NO hace falta DecidableEq S: los 9 `if` de natToFormula:294-307 y el de natToTerm:199 son todos sobre `(unpair n).1 = k : Nat`, ni uno sobre S. NO hace falta inyectividad: la sobreyección se usa sólo en la dirección ∃n. NO hace falta Inhabited S: el caso base es `.var 0`, que habita TermG S incluso con S vacío. NO hace falta orden ni Repr. ⭐ La clase YA EXISTE COMPILADA en el sondeo — «antes de construir, buscar»: se PROMUEVE, no se reescribe, y el sondeo debe pasar entonces a importarla o deja de ser control (hoy vive en namespace ProbeCoste y se convertiría en un duplicado silencioso). Sitio: dentro de Enumeration.lean, entre la capa 2 y la capa 3, junto con `instance : EnumSym String := ⟨natToString, natToString_surj⟩`. NO en FOL/FOL.lean: la instancia necesita natToString_surj, que está aquí, y meter la clase en el núcleo mueve los 147 footprints de FOL.lean sin comprar nada — el DAG lo permite porque HenkinLimit0 importa Enumeration (:16) y Lindenbaum0 importa HenkinLimit0 (:15). | ⚠️ EL ÚNICO NO MEDIDO POR NADIE: recursión BIEN FUNDADA con instancia en el PREFIJO FIJO. natToTerm/natToTerms (FOL/Enumeration.lean:196-220, mutual, termination_by n => n) y natToFormula (:291-315). ⭐ Pero la cota que las salva es INERTE al parámetro, y esto SÍ es medible leyendo: los decreasing_by de :204-209, :215-219 y :310-315 se descargan con unpair_snd_le / unpair_fst_le / unpair_sum_le + omega, que son capa 0 y PURO Nat; S no aparece ni en la medida (`n`) ni en ningún objetivo decreciente. Lo que el compilador tiene que decir es otra cosa: las ECUACIONES DE DESPLIEGUE. MEDIDO: 12 sitios las consumen (FOL/Enumeration.lean:249, 256, 259, 266, 325, 331, 337, 345, 350, 358, 366, 371) con `simp [natToTerm|natToTerms|natToFormula, …]`, y al meter {S}[EnumSym S] esas ecuaciones cambian de forma (pasan a ∀ {S} [inst], …). ESTIMADO: siguen disparando. || ✅ LO QUE **NO** ES BLOQUEANTE, y estaba medido y olvidado: termSize/termsSize (:222-230) es recursión MUTUA ESTRUCTURAL sobre un inductivo ANIDADO (Term contiene List Term). Parece el riesgo gordo y NO lo es: sondeos/SymbolParam.lean:26-33 ya compila `mutual def liftTerm {S} : Term S → Term S / liftTerms {S} : List (Term S) → List (Term S)` — exactamente la misma forma, con parámetro, verde. Lo mismo formulaSize (:278). || ⚠️ Tercer bloqueante, de ENUNCIADO y no de construcción: DECISIONS.md:5291-5294 afirma que «con S arbitrario, natToTerm_surj DEJA DE SER DEMOSTRABLE ⇒ el parámetro obliga a añadir una hipótesis de numerabilidad a esa rama. ⬜ No medido cuánto cuesta». Eso es FALSO tal como está escrito: con [EnumSym S] la prueba de :235-266 sobrevive LETRA POR LETRA (sólo cambia natToString_surj → EnumSym.enum_surj), y el coste está medido aquí: 11 declaraciones. La frase es una cabecera que afirma una deuda que la clase del sondeo ya pagó. |
| `E:/dropbox/github/lean4/FOL/FOL/HenkinLimit0.lean` | 313 | 0 | ninguna en esta capa — instancia `EnumSym String` por tipo esperado | Consumidor nº1 (import FOL.Enumeration:16, `open FOL.Metamath.Enumeration`:83). MEDIDO: 10 apariciones de natToFormula en CÓDIGO (:194, :195, :197, :211, :223, :237, :257, :264, :265) más natToFormula_surj:305; las otras 4 son docstring. NO CAMBIA NI UNA LÍNEA: en los 10 sitios el tipo esperado es Formula = FormulaG String (bnd : Formula → Nat :183, henkinAx : … → Formula), así que S := String se infiere y la instancia resuelve. ⚠️ El riesgo no es el tipo, es la RESOLUCIÓN DE INSTANCIAS: `natToFormula n` pasa a elaborar como `@natToFormula String instEnumSymString n`, y todo sitio que case sintácticamente ese término tiene que seguir casando. Aquí no hay `rfl` sobre él, pero SÍ en Lindenbaum0. ⇒ una sola instancia `EnumSym String` en todo el árbol, o hay diamante. ✅ Su footprint NO se mueve: `noncomputable def bnd (f) := (cst_bound_formula f).choose` (:183) mete Classical.choice por su cuenta, independientemente de Enumeration. |
| `E:/dropbox/github/lean4/FOL/FOL/Lindenbaum0.lean` | 247 | 0 | ninguna en esta capa | Consumidor nº2 (vía import FOL.HenkinLimit0:15, `open`:67). MEDIDO: 6 apariciones en código (:133, :134, :144, :151, :183 y natToFormula_surj:182). ⛔ AQUÍ ESTÁ EL RIESGO DE VERDAD DE LOS CONSUMIDORES: `noncomputable def LindenbaumStep` (:130-135) mete `x = natToFormula n` DENTRO de la condición de un `if` decidido por Classical.propDecidable, y lindenbaum_step_consistent:144-146 y lindenbaum_step_subset:151-153 hacen `simp only [LindenbaumStep]` + `by_cases h : IsConsistent₀ (fun x => Or (LindenbaumStep S n x) (x = natToFormula n))` + `rw [if_pos h]`. Ese `rw` exige que el término que escribe el by_cases sea SINTÁCTICAMENTE el mismo que el de la definición, incluida la instancia Decidable. Con implícitos nuevos siguen siendo el mismo término (una sola instancia), ESTIMADO verde; es el sitio que hay que mirar primero si algo rompe aguas abajo. ✅ Footprint no se mueve: el `if IsConsistent₀` (la línea Π⁰₁, el WKL) ya trae Classical.choice. |
| `E:/dropbox/github/lean4/FOL/FOL/Compacity0.lean` | 132 | 0 | ninguna en esta capa | Consumidor nº3 (vía FOL.Canonical0). MEDIDO: 3 usos en código, :112 `natToTerm n` y :116/:118 `natToTerm_surj t`, todos con tipo esperado Term fijado por `termSetoid T hMax` ⇒ S := String se infiere. Cero cambios. ✅ Footprints (compactness₀ y loewenheim_skolem_down, filas 119-120 de check-footprints) no se mueven: pasan por henkin_completion, que ya trae choice. ⚠️ ⛔ EL ÚNICO CONSUMIDOR QUE HAY QUE MIRAR A MANO ES cuarentena/Completeness.lean:126 (`def formula_enum : Nat → Formula := FOL.Metamath.Enumeration.natToFormula`, sin eta): NO COMPILA en el build, así que el verde NO lo cubre — es exactamente el sitio donde un axiom falso sobrevivió ochenta días. ⭐⭐ Y el dato que más ahorra: grep MEDIDO en ROBINSON_PlusPlus — CERO consumidores de Enumeration fuera de sondeos/. Los 145 jobs de RPP no se mueven, y M-12 (push FOL antes que RPP) no entra en juego más que por la tabla de footprints. |

#### ⚖️ La refutación — **MANDA ÉSTA**

NO SOBREVIVE. Seis fallos, cuatro de ellos medidos leyendo el arbol.

═══ [1] ⛔⛔ LA JUSTIFICACION CENTRAL ES UN ERROR DE CATEGORIA (y el plan se refuta a si mismo)

El plan construye toda su prioridad sobre esto: «Fresh0 tiene cuatro modulos por delante (Fresh0 ← Henkin0 ← Lift0 ← Eigenvariable ← Derives0); Enumeration ← FOL y nada mas ⇒ es el UNICO modulo que se puede generificar sin tocar nada aguas arriba». Eso equipara el DAG de IMPORTS con la dependencia de GENERIFICACION, y son cosas distintas.

MEDIDO por mi en E:/dropbox/github/lean4/FOL/FOL/FOL.lean (287 lineas): lo UNICO generico son los dos inductivos (:27, :32) y los tres shims (:52, :63, :68). Siguen siendo String-puras `neg`:73, `top`:75, `iff`:77, `liftTerm`:103, `liftTerms`:108, `liftFormula`:114, `substTerm`:128, `substTerms`:136, `substFormula`:142, `getAt?`:164, `replaceAt`:180, `LocalRule`:204, `Derives`:211.

⇒ Enumeration importa un FOL.lean NO generico y aun asi se generifica. La razon no es «su unico import es FOL»: es que sus declaraciones no tocan liftFormula/substFormula/neg/Derives₀. Ese es el criterio, y el plan no lo aplica a Fresh0 — lo descarta por posicion en el DAG, sin medir que declaraciones de Fresh0 mencionan `Derives₀`. La frase «el orden del propietario es incompatible con el DAG» es una INFERENCIA SIN ETIQUETA presentada como medicion, y ademas la contradice el propio caso que el plan defiende.

═══ [2] ⛔⛔⛔ LENTE DE VACUIDAD: al final de esta capa `S := List Char` NO ES POSIBLE, y el plan no lo dice

(a) El plan promueve `class EnumSym` + `instance : EnumSym String` y NADA MAS. La `instance : EnumSym (List Char)` vive en sondeos/SymbolParamCoste.lean:87-94, y MEDIDO en lakefile.lean el `@[default_target]` es `lean_lib ROBINSON_PlusPlus`: `sondeos/` NO ENTRA EN EL BUILD. Al terminar el VERDE B, en el arbol compilado no existe ni una instancia de EnumSym distinta de String ⇒ el parametro no se puede instanciar ni una vez.

(b) Y aunque se promoviera: un `FormulaG (List Char)` producido por `natToFormula` no lo acepta NINGUNA operacion del nucleo — ni `liftFormula`, ni `substFormula`, ni `neg`, ni `top`, ni `iff`, ni `getAt?`, ni `replaceAt` (lista medida arriba, todas en FOL/FOL.lean). Se entrega un teorema generico cuyo tipo nadie puede manipular.

⇒ La capa 0 REAL de la migracion NO es Enumeration: es la CAPA DE FUNCIONES de FOL/FOL.lean (los ~9 defs de lift/subst + neg/top/iff), que es lo que necesitan Derives0, Rename, Eigenvariable, Lift0, Henkin0 y Fresh0 — o sea todo. Enumeration es la HOJA del grafo de valor, no su raiz: es lo mas barato, y el plan lo vende como «la capa 0 REAL». Ordenar por baratura y llamarlo dependencia es exactamente el problema que ADR-068 (~x50) ya pago.

═══ [3] ⛔⛔ «EL VERDE A NO MUEVE NINGUN TITULAR PUBLICADO» — REFUTADO POR MEDICION

El plan lista 5 sitios de publicacion y los declara MEDIDOS. Medidos por mi hay al menos 8, y tres de los que faltan los mueve el VERDE A, no el B:

FALTAN (medidos con grep sobre *.md de los dos repos):
· ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md:105 — publica el mismo triple `[propext, Classical.choice, Quot.sound]` para Enumeration. Sexto sitio, no listado.
· ROBINSON_PlusPlus/doc/PLAN-COMPLETITUD-FINITISTA.md:1261-1262 — «MEDIDO, y esto no es una limitacion pendiente de comprobar: `natToTerm_surj` es un TEOREMA COMPILADO que refuta que existan κ terminos cerrados distintos para κ no numerable, porque los simbolos son String». El VERDE A convierte ese teorema en condicional en `[EnumSym S]`. Es §7.5, la seccion que JUSTIFICA el paso 4 entero.
· ROBINSON_PlusPlus/DECISIONS.md:4173 y :5174 — dos frases mas sobre `natToTerm_surj`, movidas por el VERDE A.
· FOL/AXIOMS.md:111 publica la FIRMA `natToFormula_surj : ∀ f : Formula, ∃ n, natToFormula n = f`, y :119 el footprint de `formula_enum_surj`. El plan solo listo :118.

⇒ El argumento de venta del corte en dos («el VERDE A es gratis en terminos de documentacion, y ahi esta todo el riesgo tecnico») cae: el VERDE A mueve afirmaciones publicadas en tres documentos, uno de ellos la seccion que motiva el paso 4.

═══ [4] ⛔ LA «RECTIFICACION» DE DECISIONS.md:5291-5294 ES FALSA — el plan corrige una frase correcta

Texto verbatim leido: «con `S` arbitrario, natToTerm_surj deja de ser demostrable (enumera los terminos, y eso exige que los simbolos sean numerables). ⇒ el parametro generico obliga a AÑADIR UNA HIPOTESIS DE NUMERABILIDAD a esa rama. ⬜ No medido cuanto cuesta.»

Eso es literalmente cierto: con S arbitrario y SIN hipotesis no es demostrable, y la frase identifica correctamente el remedio — una hipotesis de numerabilidad, que es exactamente `[EnumSym S]`. Lo unico abierto es el ⬜ del coste, que es una deuda honesta, no una mentira. El plan lo declara «FALSO tal como esta escrito» y propone rectificarlo en un ADR. Es la lente [A1] aplicada a una cabecera que NO miente, y meteria en DECISIONS.md una rectificacion incorrecta. Lo que el plan aporta aqui es medir el ⬜ (11 declaraciones), no refutar nada.

═══ [5] ⚠️ EL PRECEDENTE CITADO PARA EL RIESGO TECNICO NO ES UN PRECEDENTE

El plan declara ✅ NO BLOQUEANTE la recursion mutua sobre inductivo anidado citando sondeos/SymbolParam.lean:26-33 (`mutual def liftTerm {S} / liftTerms {S}`). Correcto para termSize/termsSize — pero ese sondeo es recursion ESTRUCTURAL y con `{S}` SOLO, SIN argumento de instancia.

MEDIDO: `grep -rn "termination_by"` sobre FOL/FOL/*.lean y ROBINSON_PlusPlus/sondeos/*.lean devuelve UNICAMENTE las cuatro de Enumeration.lean (:161, :203, :214, :309). No existe en ninguno de los dos repos un solo precedente de recursion BIEN FUNDADA con una INSTANCIA en el prefijo fijo. El plan marca ese punto como «⚠️ EL UNICO NO MEDIDO POR NADIE» y eso es honesto, pero luego lo compensa con un precedente que cubre otra cosa. Los 12 sitios de `simp [natToTerm|natToTerms|natToFormula, …]` y los tres `decreasing_by` quedan sin testigo: es un si/no del compilador, y es el unico riesgo real de la capa.

═══ [6] ⚠️ COLISION DE NOMBRE, no en esta capa pero si en la tecnica que el plan generaliza

MEDIDO: en FOL/HenkinLimit0.lean y FOL/Lindenbaum0.lean el identificador `S` YA ESTA TOMADO — es la teoria (`LindenbaumStep S n x`:133, `hen S n`:223, `henkin_step_consistent`:264). Aqui no molesta (0 cambios), pero el plan presenta «añadir {S : Type} a la firma» como tecnica reutilizable y no avisa de que en los dos consumidores principales el nombre esta ocupado.

═══ SOBRE LAS REGLAS DEL PROYECTO

Regla 1 (medicion vs estimacion): el plan etiqueta bien casi todo (~45 lineas ESTIMADO, 0 lineas en consumidores ESTIMADO, el reparto de las seis choice ESTIMADO). ⛔ Pero publica «5 sitios publican su footprint» y «MEDIDO: 1 sola fila de las 147» bajo el epigrafe MEDIDO, y la primera es FALSA por medicion (son ≥7, y tres los mueve el VERDE A). Una medicion equivocada publicada como medicion es peor que una estimacion sin etiqueta.

Regla 4 (un verde puede no comprobar nada): ✅ el hallazgo sobre check-doc-sync.bash [C] es correcto y lo verifique lineas 332-356 — solo casa el NOMBRE del modulo contra §6 con frontera de palabra; la lista de 24 declaraciones de REFERENCE.md:722 no esta bajo ningun control. Ese punto SI sobrevive entero.

Pregunta 3 del encargo (¿mueve footprints publicados?): los titulares aguas abajo (check-footprints filas 48, 49, 50, 51, 57, 119, 120 — henLimit_consistent, henLimit_witness, lindenbaum_lemma, henkin_completion, completeness₀, compactness₀, loewenheim_skolem_down) NO se mueven, porque los siete ya llevan el triple completo y la choice se la meten ellos (`bnd` via Exists.choose en HenkinLimit0:183, el `if IsConsistent₀` en Lindenbaum0:133). ✅ Ahi el plan acierta, aunque solo cito tres de las siete filas.

**Lo correcto:**

QUE SOBREVIVE, LITERALMENTE (se puede reutilizar tal cual):

1. El inventario del fichero. Verificado linea a linea: 377 lineas, y las 14 posiciones que cita son exactas (unpair:90, natToList:158, natToString:184, natToString_surj:186, natToTerm:196, natToTerms:211, termSize:223, termsSize:227, term_surj_aux:235, natToTerm_surj:268, natToTerms_surj:271, formulaSize:278, natToFormula:291, formula_surj_aux:317, natToFormula_surj:374). Las 4 lineas de cuerpo a cambiar (:202, :253, :296, :327) son exactas.

2. La FORMA de la clase. `EnumSym S` con solo `enum`/`enum_surj` basta: verificado que los 9 `if` de natToFormula:294-307 y el de natToTerm:199 son todos sobre `(unpair n).1 = k : Nat` ⇒ no hace falta DecidableEq S; el caso base es `.var 0` ⇒ no hace falta Inhabited S; la sobreyeccion se consume solo en direccion ∃n ⇒ no hace falta inyectividad. Y «antes de construir, buscar»: la clase ya existe en sondeos/SymbolParamCoste.lean:73-75.

3. El aislamiento. Enumeration.lean no menciona liftFormula, substFormula, neg, ni Derives₀ ⇒ M-11 no entra y el modulo es generificable sin tocar nada aguas arriba. Eso es cierto — lo que es falso es la razon que el plan da (el import) y el valor que le atribuye.

4. El hallazgo de control: check-doc-sync.bash [C] no comprueba la lista de declaraciones. Es el hallazgo mas util del plan y es correcto.

5. Que los 7 titulares aguas abajo no mueven footprint. Correcto.

═══ QUE HAY QUE CAMBIAR PARA QUE EL PLAN VALGA

A) REESCRIBIR LA JUSTIFICACION DEL ORDEN. Enumeration NO es «la capa 0 REAL». Es la hoja mas barata. El criterio correcto no es el import sino QUE DECLARACIONES toca cada modulo; medirlo para Fresh0 antes de afirmar que el orden del propietario es incompatible. La capa 0 de verdad, si el objetivo es instanciar, es la CAPA DE FUNCIONES de FOL/FOL.lean (liftTerm/liftTerms/liftFormula/substTerm/substTerms/substFormula + neg/top/iff, ~9 defs, todas medidas String-puras hoy): sin ellas ningun `FormulaG (List Char)` sirve para nada.

B) CERRAR LA VACUIDAD O DECLARARLA. O bien se promueve TAMBIEN `instance : EnumSym (List Char)` (9 lineas, ya compiladas en sondeos/SymbolParamCoste.lean:87-94) al build — y entonces la capa entrega al menos UNA instanciacion real y el dividendo de footprint medible que NEXT-STEPS.md:50-52 ya cifro (`EnumSym (List Char)` sale `[propext, Quot.sound]`) — o bien el plan escribe explicitamente: «al final de esta capa S := List Char SIGUE SIENDO IMPOSIBLE en el arbol compilado, y lo seguira siendo hasta que la capa de funciones de FOL/FOL.lean sea generica». Sin una de las dos, la capa es cierta y no dice nada.

C) CORREGIR LA CIFRA DE SITIOS: no son 5, son al menos 8. Añadir doc/PLAN-COMPLETITUD-FINITISTA.md:105, :1261-1262, DECISIONS.md:4173, :5174, AXIOMS.md:111 y :119. Y retirar la afirmacion «el VERDE A no mueve NINGUN titular publicado»: lo mueve en tres documentos, todos por `natToTerm_surj`.

D) RETIRAR LA RECTIFICACION DE DECISIONS.md:5291-5294. La frase es correcta. Lo que procede es pagar su ⬜ («no medido cuanto cuesta») con el numero medido — 11 declaraciones — y dejar el enunciado en pie. Escribir un ADR que declare falsa una frase verdadera es exactamente el fallo de ADR-067 con el signo cambiado.

E) DECLARAR EL UNICO RIESGO TECNICO SIN PRECEDENTE. `termination_by` + instancia en el prefijo fijo no tiene ni un testigo en los dos repos (medido: las 4 unicas apariciones de termination_by estan en este mismo fichero). El precedente citado (SymbolParam.lean:26-33) es recursion ESTRUCTURAL con `{S}` y sin instancia: cubre termSize/termsSize, NO cubre natToTerm/natToTerms/natToFormula. Ese si/no, y si las ecuaciones de despliegue siguen disparando en los 12 sitios de simp, es lo unico que el compilador tiene que decir — y es lo primero que hay que sondear, en un fichero de sondeo, ANTES de tocar FOL/Enumeration.lean.

F) SI SE MANTIENE EL CORTE EN DOS, cambiarle la etiqueta: el VERDE A es «todo el riesgo tecnico CON factura documental en tres documentos», no «con la factura a cero».

---

### G2 · Plan de capa: la cadena `Derives0` → `Fresh0`
**¿sobrevive?** **⛔ NO**

**Orden que proponía:** ⛔ PASO 0, FUERA DE LA CAPA Y ANTES DE TODO: el bloque de funciones de FOL/FOL.lean (las 12: neg/top/iff, liftTerm/liftTerms/liftFormula, substTerm/substTerms/substFormula, getAt?/replaceAt/LocalRule). Sin el no hay paso 1: Derives₀ menciona liftFormula(:118,:122), substFormula(:119,:120,:145,:146), getAt?(:133), replaceAt(:135), LocalRule(:134) y neg(:139,:141). Este paso 0 NO es mi capa y su coste NO esta medido — el que ADR-068 midio fue el de los TIPOS. || Despues, el orden dentro de la capa que el DAG permite y que minimiza el riesgo por pasada: (1) Derives0 — es el unico que puede matar el plan, asi que su verde es la PUERTA; ademas es 1 linea (la 98) mas derives0_raa, y no arrastra instancias. La decision a tomar aqui es una sola: parametro IMPLICITO '{S : Type}', porque con explicito rompen los 268 usos de ⊢₀. (2) Rename — el DAG solo le pide Derives0, y es el mas barato de los cinco que quedan: 24 firmas, CERO instancias, y sus 4 filas de footprint estan las 4 en la tabla, asi que da un verde limpio de la tecnica antes de pagar nada. (3) Eigenvariable — aqui entra [DecidableEq S], que es hilo nuevo, y hay que decidir si se importa FOL.DecEq (que hoy NO importa) o se replica la instancia. (4) Lift0 — trivial detras de Eigenvariable: 15 firmas, cero String, cero instancias. (5) Henkin0 — hereda [DecidableEq S] y es donde aparece por primera vez la colision de nombre S. (6) La clase FreshSym, PROMOVIDA (no construida) desde sondeos/SymbolParamCoste.lean:29-62 a un modulo nuevo FOL/SymClasses.lean sobre FOL.FOL; conviene que lleve tambien EnumSym, porque Enumeration la necesita y es INDEPENDIENTE de Fresh0 en el DAG. (7) Fresh0. || ⛔ Por que el orden que propuso el propietario ('Fresh0 -> Enumeration -> Lindenbaum/Henkin') no es compatible con el DAG: Fresh0 esta al FINAL de esta cadena (depende de Henkin0 y Rename, que dependen de Lift0/Eigenvariable/Derives0), no al principio; y Enumeration cuelga directamente de FOL, no de Fresh0.

**Dónde decía que estaba el riesgo:** El riesgo NO esta donde el encargo lo situaba. Donde parecia: Rename y Eigenvariable, por las 24-26 apariciones de String cada uno, y cst_bound_sym. MEDIDO: las 24 de Eigenvariable son TODAS '(c : String)' y las 26 de Rename TODAS '(ρ : String → String)' — el simbolo como parametro opaco, cero estructura de cadena; y cst_bound_sym solo usa cst_inj + Classical.em, asi que FreshSym basta sin anadirle nada. Los dos ficheros mas 'sospechosos' son los mas baratos. || DONDE ESTA DE VERDAD, en tres sitios: || (R1) ⛔⛔ EL PRERREQUISITO INVISIBLE. La capa no arranca. Derives₀ esta construido sobre seis definiciones de FOL/FOL.lean que siguen en String. Generificarlas expone 107 de los 132 ficheros de la biblioteca de RPP (medido), con 3 536 citas de liftTerm, 1 926 de substFormula y 1 706 de substTerm. La tecnica de ADR-068 predice cero ediciones ahi, pero ADR-068 midio la parametrizacion de los TIPOS (TermG/FormulaG, 3 ficheros tocados, uno de ellos en RPP: Meta/HilbertSeq.lean). Parametrizar FUNCIONES es otra cosa: cambia las ecuaciones de simp y el desplegado definicional que RPP usa en aritmetizacion. Esa medicion NO EXISTE. Antes de planificar mi capa hay que hacerla — y el unico que la puede hacer es el compilador. || (R2) ⚠️ LA COLISION DE NOMBRE. 'S' ya significa LA TEORIA (Formula → Prop) en Henkin0 (8 sitios de codigo) y Fresh0 (13), y es el binder de la 'local notation S \" ⊢₀* \" f' en CINCO modulos (Henkin0:85, Fresh0:71, Canonical0:77, HenkinLimit0:85, Lindenbaum0:74). El parametro de simbolos no puede llamarse S ahi, y 'σ' tampoco sirve porque Rename lo usa para el renombrado inverso. Es una decision de NOMBRE que hay que tomar ANTES del paso 0, porque una vez elegida viaja por los seis ficheros y por los cinco de arriba. Barato si se decide al principio, caro si se descubre en el quinto modulo. || (R3) ⚠️ DOS TITULARES DE MI CAPA VIAJAN SIN CONTROL. 'derives0_raa' y 'FOL.Fresh0.cst_bound_formula' hacen #print axioms en el fuente pero NO estan en las 147 filas de check-footprints.bash (comprobado por comm). Generificar esos dos mueve un footprint que ningun control compara ⇒ el verde de check-footprints no diria nada. Y no son dos casos aislados: contrastando los 171 nombres que el arbol de FOL imprime contra las 147 filas de la tabla salen 40 impresos-y-no-tabulados (entre ellos FOL.HenkinLimit0.hen_consistent, FOL.Lindenbaum0.max_cons_contains, FOL.SkolemNF0.derives0_skolemize). Eso es el hallazgo [A2] del encargo de auditoria, medido: el verde de check-footprints no dice cuantos faltan. || ⭐ Y el riesgo que NO existe, para que no se presupueste: los 21 constructores de Derives₀ no cambian ni un caracter (el tipo de Γ se infiere de 'Derives₀ Γ f'); el parametro no renombra ningun caso de induccion (probado en el arbol: Rename.lean:195 induce sobre FormulaG, que ya tiene parametro, y compila en master); y RPP no cita Derives₀ ni una vez en su biblioteca.

**Estimación:** MEDIDO (leyendo el arbol, no estimado): 1 896 lineas en los 6 ficheros; 95 declaraciones contadas (Derives0 3, Eigenvariable 25, Rename 24, Lift0 15, Henkin0 7, Fresh0 21); de ellas 85 mencionan Term/Formula en la firma; 21 constructores en Derives₀; 6 inducciones sobre Derives₀ en todo el arbol; 268 usos de ⊢₀ y 558 apariciones de Derives₀ en FOL/FOL, 0 en la biblioteca de RPP; 6 declaraciones que usan la estructura de String, todas en Fresh0:79-110; 1 sitio que pide DecidableEq, Eigenvariable:73; 12 declaraciones en el prerrequisito de FOL/FOL.lean; 40 #print axioms sin fila en la tabla de 147. || ⚠️ ESTIMADO (no compilado — y esto es una ESTIMACION, con etiqueta, no una medicion): lineas de FIRMA a editar ~160-180 en mi capa, repartidas ESTIMADO asi — Derives0 ~3, Rename ~30, Eigenvariable ~35, Lift0 ~20, Henkin0 ~25 (incluye el renombrado de la variable S de teoria), Fresh0 ~45 (6 declaraciones retiradas + 15 firmas + el mismo renombrado); mas ~20 lineas de promocion de FreshSym/EnumSym desde el sondeo (promocion, no construccion: ya compilan). ⚠️ ESTIMADO aparte, y es el numero que de verdad falta: el prerrequisito de FOL/FOL.lean, ~25-30 lineas de firma sobre 12 declaraciones, PERO con una exposicion de 107 ficheros de RPP cuyo coste real NO esta medido por nadie. ⛔ No presupuestar esta capa hasta que el compilador haya pasado por el paso 0: cualquier cifra sobre los seis ficheros que asuma que el paso 0 cuesta cero es una estimacion disfrazada de plan. || ⚠️ Y una advertencia de metodo sobre lo que YO acabo de escribir: todo lo que digo sobre como se COMPORTARA Lean (que el parametro implicito salva el infix ⊢₀, que [DecidableEq S] no mueve el footprint, que los 21 constructores no cambian, que simp sigue casando con 'if s = c' generico) es RAZONADO A PARTIR DE LO LEIDO, no compilado — esta sesion es de solo lectura por prohibicion explicita. Las unicas dos de esas cuatro que tienen respaldo compilado en el arbol son la del parametro en la induccion (Rename.lean:195 sobre FormulaG) y la del footprint net-0 (check-footprints.bash:38). Las otras dos son ESTIMADAS.

#### Módulos

| fichero | l. | decls. a tocar | clases | bloqueantes |
|---|---|---|---|---|
| `E:/dropbox/github/lean4/FOL/FOL/FOL.lean  ⛔ PRERREQUISITO, NO es mi capa` | 287 | 12 | ninguna — MEDIDO: ninguna de las 12 toca el simbolo, solo lo transporta (liftTerm/substTerm deciden sobre Nat: 'if n < c', 'if n = v'). Basta {S : Type}. | Las 12 son: neg(:73) top(:75) iff(:77) liftTerm(:103) liftTerms(:108) liftFormula(:114) substTerm(:128) substTerms(:136) substFormula(:142) getAt?(:164) replaceAt(:180) LocalRule(:204). TODAS declaradas sobre Term/Formula = String. Derives₀ usa 6 de ellas (Derives0.lean:118,119,120,122,125,133,135,139,141,145) ⇒ sin este bloque no hay capa. ⚠️ EXPOSICION MEDIDA: 107 de 132 ficheros de ROBINSON_PlusPlus/ROBINSON_PlusPlus citan lift*/subst* (3 536 liftTerm, 1 926 substFormula, 1 706 substTerm, 674 liftFormula, 362 liftTerms, 1 363 substTerms, apariciones con \b). ADR-068 midio el coste de parametrizar los TIPOS (3 ficheros); el de parametrizar las FUNCIONES NO ESTA MEDIDO. ⚠️ 'instance : Coe String Formula' (:92) es el unico sitio String-especifico del bloque: se deja en String (una instancia 'Coe S (FormulaG S)' seria una coercion desde cualquier tipo). ⚠️ 'notation "⊤" => top' con {S} implicito deja ?S sin resolver si se usa aislado — pero ⊥ ya funciona asi hoy (FormulaG.bottom lleva S implicito), asi que hay precedente COMPILADO. |
| `E:/dropbox/github/lean4/FOL/FOL/Derives0.lean` | 194 | 2 | ninguna | ⛔ EL PUNTO QUE PODIA MATAR EL PLAN, y NO lo mata. (a) 21 constructores (contados con grep, coincide con el docstring; Derives tiene 22). (b) 558 apariciones de 'Derives₀' en 21 ficheros de FOL/FOL (Prenex0 123 lineas, Propositional0 40, Canonical0 31…) y ⭐ CERO en ROBINSON_PlusPlus/ROBINSON_PlusPlus — la unica cita en todo RPP es sondeos/DerivesSinMetaReglas.lean. RPP importa FOL.FOL(43), FOL.Deduction(28), FOL.Theorems.*(107), FOL.Tactics(22), FOL.MetaRules(1): ninguno alcanza Derives0. (c) La notacion es 'infix:50 " ⊢₀ " => Derives₀' (Derives0.lean:148), 268 usos de ⊢₀ en FOL/FOL. SOBREVIVE SOLO SI el parametro es IMPLICITO: con 'inductive Derives₀ (S : Type)' explicito el infix no puede suministrar S y rompen los 268. Con '{S : Type}' S se infiere de Γ/f. (d) 6 inducciones sobre Derives₀, MEDIDAS: Derives0:159, Eigenvariable:294, Rename:262, Lift0:204 (mi capa) + Soundness0:81 y Derives1:319 (aguas abajo). NDtoLK0:143 es sobre Derives₂ y Derives1:293 sobre Derives₁ — no cuentan. ⭐ Y el parametro NO cambia los nombres de caso: un PARAMETRO no se liga en las premisas menores del recursor, y hay prueba COMPILADA en el arbol — Rename.lean:195 hace 'induction f with | atom p ts =>' sobre FormulaG, que YA tiene parametro, y compila en master. ⭐ Ademas los 21 constructores NO cambian ni un caracter: el tipo de Γ se infiere de 'Derives₀ Γ f'. Solo cambia la linea 98. ⚠️ derives0_to_derives (:157) se queda EN String (puentea con Derives, que no se generifica): su firma ya dice {Γ : List Formula}, asi que no se toca. ⚠️ derives0_raa imprime footprint y NO esta en las 147 filas de check-footprints. |
| `E:/dropbox/github/lean4/FOL/FOL/Eigenvariable.lean` | 466 | 24 | DecidableEq S — y es el UNICO sitio de las 1 896 lineas que la pide | 25 declaraciones contadas; 24 mencionan Term/Formula en la firma (la excepcion es posDepth:233, que es Pos → Nat y no se toca). ⚠️ Las 24 apariciones de 'String' son TODAS '(c : String)': el simbolo como PARAMETRO OPACO. CERO manipulacion de cadenas. El fichero que mas 'sospechoso' parecia es de los mas baratos. EL UNICO uso no trivial es Eigenvariable.lean:73 — '| .func s [] => if s = c then .var k else .func s []' — que necesita Decidable (s = c) ⇒ [DecidableEq S] en absTerm/absTerms/absFormula y en las 21 declaraciones que los mencionan. Las 4 restantes (posDepth, occursTerm:357, occursTerms:361, occursFormula:366) solo piden {S}: occurs* usa 'Or (s = c)', que es una Prop, no un decide. ⭐ Y [DecidableEq S] NO mueve el footprint: FOL.Eigenvariable.absDerives esta hoy en la tabla como 'Quot.sound,propext' (check-footprints.bash:38), o sea instDecidableEqString ya es net-0. ⛔ La alternativa (open Classical) SI lo moveria: metería Classical.choice en absDerives, derives0_gen_fresh, henkin_step_consistent y todo lo de arriba ⇒ prohibida por ADR-068 §5. El fichero NO importa FOL.DecEq, asi que hay que anadir el import o replicar la instancia. |
| `E:/dropbox/github/lean4/FOL/FOL/Rename.lean` | 425 | 24 | ninguna | 24 declaraciones contadas; 22 mencionan Term/Formula (invOf:392 e invOf_spec:395 son String → String puro). ⚠️ Las 26 lineas con 'String' (54 apariciones) son TODAS '(ρ : String → String)' o '{ρ σ : String → String}' + 2 en el docstring: el simbolo como parametro opaco otra vez. CERO estructura de cadena. Pasa a (ρ : S → S). ⭐ Es el modulo MAS BARATO de la capa pese a tener el maximo de apariciones de String: 24 firmas, cero instancias, cero prosa que reescribir salvo la linea 39 del docstring ('En esta firma los dos son String'), que pasa a mentir. ⚠️ invOf lleva 'open Classical' y el if-dependiente (:393): generico en S sin cambios. Sus 4 filas de footprint estan TODAS en la tabla (34-37). |
| `E:/dropbox/github/lean4/FOL/FOL/Lift0.lean` | 338 | 15 | ninguna | 15 declaraciones contadas, las 15 mencionan Term/Formula. CERO apariciones de 'String' en todo el fichero (medido: grep -c String = 0). Solo abre FOL.Eigenvariable (posDepth), que no pide instancia. Es puro anadir {S : Type} y cambiar Term/Formula. Ningun bloqueante. |
| `E:/dropbox/github/lean4/FOL/FOL/Henkin0.lean` | 178 | 7 | DecidableEq S (por heredar absFormula/absTerm de Eigenvariable) | 7 declaraciones contadas, las 7 mencionan Formula. 3 de las 5 apariciones de String son codigo ('(c : String)' en henkinAx:90, abs_neg_witness:123, henkin_step_consistent:140); las otras 2 son docstring. Cero estructura de cadena. Solo abs_neg_witness y henkin_step_consistent tocan absFormula/absTerm ⇒ [DecidableEq S]; DerivesSet₀, IsConsistent₀, henkinAx, neg_impl_left, neg_impl_right solo piden {S}. ⚠️⚠️ COLISION DE NOMBRE MEDIDA: 'S' YA ESTA OCUPADO en este fichero por la TEORIA (S : Formula → Prop) en :82, :83, :85, :87, :139, :141, :142, :146, y por el binder de la 'local notation:50 S " ⊢₀* " f' (:85). El parametro del tipo de simbolos NO puede llamarse S aqui. La misma notacion con binder S esta en Fresh0:71, Canonical0:77, HenkinLimit0:85, Lindenbaum0:74. ⚠️ El 'open Classical' del filter (:77, :146-170) sigue valiendo: Classical.propDecidable aplica a cualquier Prop, no pide nada de S. |
| `E:/dropbox/github/lean4/FOL/FOL/Fresh0.lean` | 295 | 21 | FreshSym S — y la clase TAL COMO ESTA BASTA. No hay que anadirle nada. | 21 declaraciones contadas; 13 mencionan Term/Formula. ⭐⭐ RESPUESTA A LA PREGUNTA 4 (leida la prueba, Fresh0.lean:155-161): cst_bound_sym NO USA LA ESTRUCTURA DE String. Usa exactamente dos cosas — 'by_cases h : ∃ k, cst k = s' (Classical.em sobre una Prop, no sobre String) y 'cst_inj' (:106), que es un campo de FreshSym — mas Nat.not_succ_le_self. Ni longitud, ni prefijo, ni append, ni decide. ⇒ FreshSym BASTA, sin propiedad extra, y es satisfacible por List Char: la instancia YA ESTA COMPILADA en ROBINSON_PlusPlus/sondeos/SymbolParamCoste.lean:38-52. ⭐ RESPUESTA A LA 5: lo mismo para las otras cuatro. cst_bound_term/cst_bound_terms (:164,:174) solo llaman a cst_bound_sym + Nat.le_max_*; cst_bound_formula (:193) es induccion estructural sobre Formula con bound_pair (:186, que no pide nada); cst_bound_list (:212) usa List.not_mem_nil y List.Mem. Ninguna de las cinco toca String. ⛔ LA ESTRUCTURA DE String, EN TODA LA CAPA DE 1 896 LINEAS, ESTA EN SEIS DECLARACIONES Y SOLO AQUI: shift(:79, "f" ++ s), shift_inj(:83-84, String.append_right_inj "f"), cst(:91-93, "g" / "a" ++ cst n), cst_zero_ne(:98, not_eq_of_beq_eq_false rfl), cst_ne_shift(:102-104, idem), cst_inj(:110, String.append_right_inj "a"). Esas seis NO se generifican: se RETIRAN y se vuelven la 'instance FreshSym String', que ya esta escrita y compilada en el sondeo (:57-62) usando literalmente esos seis nombres. cst_zero_ne desaparece del todo (solo servia para probar cst_inj). ⇒ 6 retiradas + 15 generificadas con [FreshSym S]. NINGUNA de Fresh0 pide [DecidableEq S]. ⚠️ Misma colision de nombre S (teoria) en :71, :230, :231, :235, :236, :242, :243, :255, :256, :269, :270, :281, :282. ⚠️ El docstring del sondeo (SymbolParamCoste.lean:24) dice 'cst n := "c" ++ toString n' — ES FALSO, el cst real es "g"/"a"++cst n. Mentira de docstring en el propio sondeo que fija el plan. ⚠️ FOL.Fresh0.cst_bound_formula imprime footprint (:292) y NO esta en las 147 filas. |

#### ⚖️ La refutación — **MANDA ÉSTA**

NO SOBREVIVE. El plan mide bien (re-verifiqué sus cifras) pero (a) se refuta a sí mismo como plan, (b) contiene una contradicción interna que destruye su única evidencia compilada, (c) rompe tres módulos que declara fuera de su capa, y (d) apunta el riesgo de footprint al blanco equivocado.

LO QUE SOBREVIVE (re-MEDIDO por mí, leyendo el árbol):
· 1 896 líneas = 194+466+425+338+178+295 ✓ exacto; FOL.lean 287 ✓. 21 constructores en Derives₀ ✓ (contados uno a uno; Derives tiene 22, el extra es gen_rule).
· 147 filas en la tabla de check-footprints.bash ✓ (contadas dentro del heredoc TABLA) y 171 `#print axioms` en FOL/ + TheoryFramework/ ✓ ⇒ el hallazgo [A2] "40 impresos sin fila" es CORRECTO y medido; `derives0_raa` y `cst_bound_formula` no están en la tabla ✓ (grep = 0).
· El prerrequisito es REAL: Derives₀ usa liftFormula (Derives0:118,122), substFormula (:119,120,145,146), getAt? (:133), replaceAt (:135), LocalRule (:134), neg (:139,141), y las seis están en String en FOL.lean:73,114,142,164,180,204 ✓. La capa efectivamente no arranca.
· Eigenvariable:73 (`| .func s [] => if s = c then .var k else .func s []`) es el ÚNICO sitio que pide decidibilidad ✓: grep de `decide|DecidableEq|deriving|instance|open Classical` en Eigenvariable.lean da CERO líneas.
· Rename y Lift0: símbolo opaco, cero estructura de cadena ✓. Lift0 sin una sola aparición de String ✓.
· La estructura de String vive sólo en Fresh0:79-110 ✓ (leídas las seis). `cst_bound_sym` (Fresh0:152-161) usa exactamente `by_cases` sobre `∃ k, cst k = s` + `cst_inj` + `Nat.not_succ_le_self` ✓ ⇒ FreshSym basta, sin propiedad extra.
· La colisión de nombre S es real ✓ (Henkin0:78-85 `DerivesSet₀ (S : Formula → Prop)` + `local notation:50 S " ⊢₀* " f`; Fresh0:71).
· La mentira de docstring del sondeo (SymbolParamCoste:24 dice `cst n := "c" ++ toString n`; el real es `"g"` / `"a" ++ cst n`, Fresh0:91-93) ✓.
· ⭐ Y el plan etiqueta sus ESTIMADO y distingue explícitamente sus cuatro afirmaciones sobre Lean entre compiladas y razonadas. Eso cumple la regla 1 y hay que decirlo.

POR QUÉ NO SOBREVIVE:

(1) ⛔⛔ CONTRADICCIÓN INTERNA QUE ROMPE TRES MÓDULOS DE FUERA DE LA CAPA — y es el hallazgo que mata el paso (7). El plan dice: las seis declaraciones de Fresh0:79-110 "se RETIRAN" y se vuelven `instance FreshSym String`, "que ya está escrita y compilada en el sondeo (:57-62)". MEDIDO: `sondeos/SymbolParamCoste.lean:58-62` construye esa instancia citando literalmente `FOL.Fresh0.shift / cst / shift_inj / cst_inj / cst_ne_shift`. Retirar las seis ⇒ ese `instance` deja de elaborar. La evidencia compilada que sostiene TODA la capa se destruye con el paso que la invoca; la instancia String hay que REESCRIBIRLA con las pruebas inlineadas (≈10 líneas NUEVAS, no compiladas), no "promoverla".
   Y peor, MEDIDO con grep: `HenkinLimit0.lean:82` hace `open FOL.Fresh0` y usa `cst` DESNUDO en :183, :185, :186, :223, :237, :238, :254, :264, :306, y `shiftTheory` en :222, :234, :274; `Lindenbaum0.lean:65` y `Canonical0.lean:71` también abren Fresh0 y usan `shiftTheory` (:235, :237, :545). Retirar `cst`/`shift` rompe esos ~12 sitios. Son TRES módulos que el plan declara fuera de su capa y que el DAG pone inmediatamente aguas abajo.

(2) ⛔⛔ Y eso MUEVE CONTENIDO BAJO TEOREMAS PUBLICADOS, que el plan afirma que no toca. `HenkinLimit0:183` es `noncomputable def bnd (f : Formula) : Nat := (cst_bound_formula f).choose` y `:222-223` es `def hen` con `henkinAx (cst (hidx n)) ...`. Son DEFINICIONES, no teoremas: tras la generificación su desplegado pasa de `Fresh0.cst` a `@FreshSym.cst String instFreshSymString`, y sobre `hen`/`henLimit` se levantan `hen_consistent`, `max_cons_contains`, `henkin_completion` y `completeness₀` (ADR-041). Que la LISTA de axiomas no se mueva es plausible pero es ESTIMACIÓN, no medición, y el plan ni siquiera plantea la pregunta: su sección de riesgo de footprint nombra sólo dos impresores sin fila.

(3) ⛔ EL RIESGO DE FOOTPRINT ESTÁ APUNTADO AL BLANCO EQUIVOCADO. MEDIDO en check-footprints.bash (que además vive en ROBINSON_PlusPlus, no en FOL — el plan no lo dice): las filas 24 y 25 son `Derives₀.rec|propext` y `derives0_to_derives|propext`, o sea el recursor cuya signatura cambia en el paso (1), y el plan dice "sólo cambia la línea 98" sin mencionar ninguna de las dos. Las filas 34-46 son TRECE filas de la capa (Rename 34-37, Eigenvariable 38-40, Lift0 41-42, Henkin0 43, Fresh0 44-46); el plan cita una sola, la 38. Y de fondo: todo teorema publicado de FOL se enuncia con `⊢₀` (fila 58 derives0_complete_iff, 69-71 Herbrand, 118 derives0_consistent_fin, 148-151 Skolem…), así que generificar Derives₀ cambia el contenido definicional bajo todos ellos. El plan lo cataloga bajo "⭐ el riesgo que NO existe".

(4) ⛔ ERROR FACTUAL QUE MANDA A TRABAJO PROHIBIDO. El plan dice de Eigenvariable: "El fichero NO importa FOL.DecEq, así que hay que añadir el import o replicar la instancia". Falso: lo que `absTerm` pide es `Decidable (s = c)` con `s c : S`, o sea `DecidableEq` del NÚCLEO, cero imports. `FOL/DecEq.lean` da `DecidableEq (TermG S)/(FormulaG S)`, que Eigenvariable no necesita. Y añadir ese import sería exactamente lo único que el árbol tiene PROHIBIDO por escrito: `FOL/DecEq.lean`, sección "⛔ Y por qué NO se retrofita a los módulos ya escritos", dice que Henkin0 y Lindenbaum0 no lo importan a propósito porque "cambiarlo movería el footprint de teoremas ya publicados y medidos". El plan ofrece como opción la cosa que el repo documenta como prohibida.

(5) ⛔ TRAMPA NO VISTA: `open Classical` + obligación de instancia nueva = fallo SILENCIOSO con control en verde. Henkin0:77 tiene `open Classical` a nivel de módulo. Cuando `absFormula` pase a pedir `[DecidableEq Sym]`, cualquier declaración de Henkin0 / HenkinLimit0 / Lindenbaum0 que OLVIDE declarar la instancia la recibirá en silencio de `Classical.propDecidable`. Entonces el `absFormula` del enunciado no es el mismo término que el de los lemas de Eigenvariable y el `rwa [abs_neg_witness c A hcA] at h` (Henkin0:173) falla — o elabora y mete `Classical.choice` por una vía que no es matemática. La fila 43 ya lleva `Classical.choice`, así que check-footprints seguiría VERDE. Es la forma exacta de [[feedback-controles-que-no-comprueban]]. El plan lee ese `open Classical` como "sigue valiendo"; combinado con la instancia nueva es justo lo contrario.

(6) ⭐ LENTE DE VACUIDAD: cierto pero, tal como se describe, no compra NADA MEDIBLE. Al final de G2 no se instancia nada: los mismos teoremas, las mismas 147 filas, ninguna instancia ejercitada. La capa compilaría IDÉNTICA si el parámetro fuera INERTE y nadie lo notaría; no hay criterio de aceptación. Además el rendimiento en footprint es CERO: el `Classical.choice` de Fresh0 es `Classical.em` sobre `∃ k, cst k = s` (Fresh0:153), matemático, no de descomponer String — G2 no quita ni un `Classical.choice`. Y `Sym := List Char` al final de G2 sólo valdría para los teoremas de la propia capa: Enumeration, HenkinLimit0, Lindenbaum0, Canonical0, Semantics, Eq0 y Soundness0 siguen en String ⇒ `completeness₀` sigue String-only. Encima `FreshSym (List Char)` vive hoy en `ROBINSON_PlusPlus/sondeos/`, y FOL NO PUEDE importar RPP (medido: el `require FOL from "../FOL"` está en el lakefile de RPP, no al revés) ⇒ dentro de FOL, "se puede instanciar" es hoy literalmente falso.

(7) ⚠️ EL PRECEDENTE COMPILADO NO CUBRE LA DECISIÓN QUE EL PLAN LLAMA "LA PUERTA". Cita Rename.lean:195 (`induction f with | atom p ts =>` sobre FormulaG) como prueba de que el parámetro no renombra casos. Pero FOL.lean:37 declara `inductive FormulaG (S : Type)` — parámetro EXPLÍCITO y tipo Type. La decisión del paso (1) es un parámetro IMPLÍCITO `{S : Type}` sobre un inductivo Prop-valuado. El precedente es de otra cosa; esa afirmación es ESTIMADA y el plan la coloca entre las dos "con respaldo compilado".

(8) ⚠️ Mentira de docstring que el plan crea y no contabiliza: al retirar shift/cst, la cabecera de Fresh0 ("La construcción, en dos movimientos", líneas 27-33, con `shift s := "f" ++ s` y `cst 0 = "g"`) pasa a mentir, igual que Rename:39. El plan sólo contempla Rename:39. Es precisamente el eje [A1] del encargo de auditoría.

**Lo correcto:**

LO CORRECTO, en este orden:

A) LO ENTREGADO NO ES UNA CAPA, ES UNA PETICIÓN DE MEDICIÓN. El propio plan demuestra que G2 no puede empezar. Entonces el entregable honesto es: "capa G2 NO PLANIFICABLE; se entrega en su lugar la especificación del Paso 0". Todo lo demás (orden, coste, riesgo) sobra hasta que el compilador pase por el Paso 0, y el plan no debe publicar un orden de seis pasos detrás de una puerta que él mismo declara cerrada y sin medir.

B) RECORTAR EL PASO 0 A UNA PUERTA BARATA Y MEDIBLE, que NO es Rename. El plan propone Rename como "verde limpio de la técnica antes de pagar nada", pero Rename está DETRÁS del Paso 0. La puerta barata de verdad es un Paso 0-a con sólo `neg`, `top`, `iff` (FOL.lean:73-77): tres definiciones que ningún fichero de RPP arrastra por la vía `lift*`/`subst*`, y que ya ejercitan las dos dudas reales (¿`notation "⊤" => top` con `{S}` implícito resuelve?, ¿un `def` sin argumentos explícitos se instancia solo?). Si Paso 0-a sale verde y con las 147 filas intactas, entonces y sólo entonces se mide Paso 0-b (`liftTerm/liftTerms/liftFormula/substTerm/substTerms/substFormula/getAt?/replaceAt/LocalRule`), que es el que expone los 107 ficheros de RPP. Cada uno con su verde y su tabla, ADR-068 §5.

C) LA DECISIÓN DE NOMBRE, ANTES DE TOCAR NADA. `S` está ocupado por la TEORÍA (`Formula → Prop`) en Henkin0:78-85, Fresh0:71, HenkinLimit0:85, Lindenbaum0:74, Canonical0:77, y es el binder de la `local notation ... ⊢₀* ...` en los cinco. `σ` está ocupado por el renombrado inverso en Rename. El parámetro de símbolos se llama `Sym` (o `Σ`) y se fija en el Paso 0-a, no en el quinto módulo.

D) FRESH0: NO RETIRAR LAS SEIS. Es lo que rompe HenkinLimit0/Lindenbaum0/Canonical0 y lo que destruye el sondeo. Se hace al revés, en dos tiempos:
   1. Se AÑADE `FOL/SymClasses.lean` sobre `FOL.FOL` con `FreshSym` + `EnumSym` y con la instancia `FreshSym (List Char)` (promoción real del sondeo:29-52, esa sí compila tal cual).
   2. Fresh0 CONSERVA `shift`, `cst`, `shift_inj`, `cst_inj`, `cst_ne_shift`, `cst_zero_ne` como están, en String, y añade al lado `instance : FreshSym String` construida con esos seis nombres (que es exactamente lo que ya está compilado en el sondeo:57-62). Las 15 declaraciones restantes se generifican con `[FreshSym Sym]`. Los ~12 usos desnudos de `cst`/`shift` en HenkinLimit0 y los de `shiftTheory` en Lindenbaum0/Canonical0 siguen resolviendo, y NADA de lo publicado se mueve. La retirada de las seis, si alguna vez procede, es una capa posterior con su propio verde y su propia tabla — nunca dentro de G2.

E) EIGENVARIABLE: `[DecidableEq Sym]` y NADA de imports. No se importa `FOL.DecEq` (lo prohíbe su propio docstring: movería el footprint de Henkin0/Lindenbaum0) y no se replica ninguna instancia: `DecidableEq` es del núcleo. Y en Henkin0/HenkinLimit0/Lindenbaum0, donde hay `open Classical`, hay que declarar `[DecidableEq Sym]` EXPLÍCITAMENTE en toda declaración que mencione `absTerm`/`absTerms`/`absFormula`, porque si falta, `Classical.propDecidable` la rellena EN SILENCIO y el control sigue verde. Control que hay que escribir: un `grep` de las declaraciones que mencionan `absFormula` contra las que declaran la instancia.

F) CRITERIO DE ACEPTACIÓN DE G2 (hoy no existe, y sin él la capa es invacuable en el sentido de [[feedback-obligacion-vacua]]): el verde de G2 debe incluir, COMPILADOS y en el árbol de FOL, (i) las 147 filas idénticas, y (ii) al menos dos `example` con `Sym := List Char` que consuman de verdad `FOL.Rename.derives0_rename` y `FOL.Fresh0.exists_fresh`. Sin ese consumidor la capa compilaría igual con el parámetro INERTE y nadie lo sabría; es la lente de [[feedback-medir-la-forma]] (medir si el parámetro es inerte) aplicada al propio entregable.

G) CONTROL [G] QUE HAY QUE ESCRIBIR, NO ARREGLAR A MANO (eje [A2] del encargo, y esta vez con la cifra medida por mí): hay 171 `#print axioms` en FOL/ + TheoryFramework/ contra 147 filas en `ROBINSON_PlusPlus/check-footprints.bash` ⇒ 24 impresos sin fila como cota inferior del desajuste (el plan dice 40 tras casar nombres; no he re-medido ese casamiento, así que 40 queda ESTIMADO y 171 vs 147 MEDIDO). El control que falta no es una fila más: es un `check-footprints-cobertura` que ROMPA cuando un `#print axioms` del fuente no tenga fila, exactamente como `check-axioms.bash` rompe también hacia abajo (ADR-032 §4). Y antes de generificar nada, `derives0_raa`, `FOL.Fresh0.cst_bound_formula`, `FOL.HenkinLimit0.hen_consistent` y `FOL.Lindenbaum0.max_cons_contains` deben tener fila, o el verde de check-footprints no dirá nada sobre esta migración.

H) DOC: la cabecera de Fresh0:27-33 y Rename:39 describen la firma en String. Si se generifica, se corrigen EN LA MISMA PASADA, no después — es el eje [A1] del encargo y ya hay precedente de que SkolemNF0 y HerbrandBlock0 anunciaban deudas ya pagadas.

---

### G3 · Plan de capa: `HenkinLimit0` → `Lindenbaum0` → `Canonical0`
**¿sobrevive?** **⛔ NO**

**Orden que proponía:** DENTRO de la capa el orden está FORZADO y es lineal, por los imports medidos: HenkinLimit0 (import Fresh0 + Enumeration, :15-16) → Lindenbaum0 (import HenkinLimit0, :15) → Canonical0 (import Lindenbaum0 + Eq0 + Semantics + Soundness0, :15-18) → [Compacity0, ya fuera]. No hay grados de libertad.

⛔ PERO EL ORDEN NO ES LA PREGUNTA: mi capa NO PUEDE SER LA SIGUIENTE. El DAG dice que antes van, medido:
(1) FOL/FOL.lean:103-142 — liftTerm/liftTerms/liftFormula/substTerm/substTerms/substFormula. **15 de las 25 declaraciones de FOL/FOL.lean siguen sobre Term/Formula instanciados.** ADR-068 parametrizó el INDUCTIVO, no las FUNCIONES. HenkinLimit0 §1 (6 declaraciones) es literalmente sobre esas funciones: sin ellas no se escribe ni la primera línea.
(2) Eigenvariable (occursTerm/Terms/Formula, :357-373) y Rename (renameFormula, :111) — y Rename ya tiene 'ρ : String → String' en la firma.
(3) Henkin0 (DerivesSet₀ :82, IsConsistent₀ :87, henkinAx :90, henkin_step_consistent :139).
(4) Fresh0 y Enumeration, en cualquier orden entre sí: **son ramas INDEPENDIENTES** (Enumeration ← FOL; Fresh0 ← Henkin0, Rename). El orden que el propietario propuso, «Fresh0 → Enumeration → Lindenbaum/Henkin», no está mal: es que no es un orden, son dos ramas paralelas que se juntan en HenkinLimit0.

⭐ Y EL DATO DE ORDEN QUE NO ESTÁ EN NINGÚN SITIO: **Canonical0 es el punto de unión de DOS ramas del DAG que no se tocan hasta él.** La rama sintáctica (FOL → Derives0 → Eigenvariable → Lift0 → Henkin0 → Fresh0 → HenkinLimit0 → Lindenbaum0) y la rama SEMÁNTICA (FOL → Semantics → Soundness0), que nadie ha planificado y que es donde vive el bloqueante duro: 'Model.func : String → List D → D' (Semantics.lean:24). ⇒ Canonical0 no es «el tercero de mi capa»: es el primero que exige que la rama semántica haya aterrizado, y esa rama toca 9 ficheros (Canonical0, Compacity0, Finitary0, Rename, Semantics, SequentSound0, Skolem0, SkolemN0, Soundness0), MEDIDO.
⇒ Propuesta de orden real: HenkinLimit0 y Lindenbaum0 se pueden cerrar en cuanto estén FOL.lean, Eigenvariable, Rename, Henkin0, Fresh0 y Enumeration; Canonical0 espera además a Semantics/Eq0/Soundness0. Son DOS entregas con verde propio, no una.

⚠️ Y una condición previa que no es de imports sino de NOMENCLATURA, y que hay que decidir ANTES de tocar la primera línea de la capa: **'S' ya está ocupado**. FOL/FOL.lean:27 declara 'inductive TermG (S : Type)', pero en mi capa 'S' es LA TEORÍA ('S : Formula → Prop') en 53 de las 79 declaraciones y en 280 ocurrencias del identificador (40 + 72 + 168, CONTADAS). La técnica de ADR-068 («no hace falta renombrar nada, basta añadir {S} a la firma») es cierta abajo, donde 'S' está libre, y **es FALSA aquí**. Hay que elegir: o el parámetro de símbolos se llama distinto en esta capa (rompe la convención de FOL.lean), o se renombra la teoría en 280 sitios. Esa decisión es de la capa entera, no de un fichero.

**Dónde decía que estaba el riesgo:** ⛔ EL RIESGO NO ESTÁ EN MI CAPA. Está UNA CAPA MÁS ABAJO, en una sola fila de check-footprints, y es un movimiento HACIA ABAJO.

Lo primero, lo que el propietario teme y que MEDIDO no ocurre: las 11 filas de mi capa en check-footprints.bash son 2 filas a '-' (HenkinLimit0.not_occurs_henkinAx, línea 47 del script; Canonical0.eval_pullback_formula, línea 55) y 9 filas a 'Classical.choice,Quot.sound,propext'. Las 9 conservan 'Classical.choice' por vías que NO son String y que sobreviven a la generificación: el 'if IsConsistent₀' Π⁰₁ (Lindenbaum0.lean:133), 'Exists.choose' en 'bnd' (HenkinLimit0.lean:183), 'Classical.choose' en 'quotientOut' (Canonical0.lean:240) y ocho 'Classical.byContradiction'. Conservan 'Quot.sound' por el cociente ('termSetoid', Canonical0.lean:176; 'Quotient.sound' en :281 y :392). ⇒ ESTIMADO: el footprint de 'completeness₀' NO se mueve.

⭐⭐ Y HAY UN PRECEDENTE MEDIDO QUE LO CONFIRMA, y es la receta: **DecEq ya se generificó en ADR-068 y su fila NO se movió** — 'FOL.DecEq.instDecidableEqTerm|-' sigue en la tabla, y sigue midiendo, porque DecEq.lean:95 dejó 'abbrev instDecidableEqTerm : DecidableEq Term := instDecidableEqTermG'. Es decir: **se conservó el NOMBRE VIEJO como especialización en String, y el '#print axioms' sigue apuntando a él.**
⚠️ Y aquí está la trampa que nadie ha escrito: si a 'completeness₀' simplemente se le añade '{S} [FreshSym S] [EnumSym S]', el '#print axioms FOL.Canonical0.completeness₀' pasa a medir el teorema GENÉRICO — y el genérico ya no arrastra las instancias, luego su footprint PUEDE bajar. Si en cambio se hace 'completeness₀G' genérico + 'theorem completeness₀ := completeness₀G' en String, el '#print axioms' sigue arrastrando 'FreshSym String' y 'EnumSym String', y con ellas el 'Classical.choice' que 'String' mete hoy ⇒ la fila no se mueve y no hace falta ADR para el footprint. **Es una decisión de ENUNCIADO, y decide la diferencia entre «no pasa nada» y «hay que reabrir ADR-041».**

⛔ LA FILA QUE SÍ SE MUEVE, y no es mía: **línea 29 de check-footprints.bash, 'FOL.Metamath.Enumeration.natToFormula_surj|Classical.choice,Quot.sound,propext'.** Su único punto sospechoso de 'Classical.choice' es la capa 2, que es String puro: 'natToString' (Enumeration.lean:184, 'String.ofList'), 'natToString_surj' (:186-189, 'String.ofList_toList'), 'map_ofNat_toNat' (:178-182, 'Char.ofNat_toNat') — y el resto del fichero es 'unpair', 'omega', inducción sobre Nat y sobre cotas de tamaño, que no traen choice. Al generificar, 'natToString_surj' se sustituye por 'EnumSym.enum_surj', una proyección de instancia sin axiomas, y **el fichero deja de tocar String**. Por [[feedback-footprint-no-es-constructividad]] («en v4.31 todo lo que DESCOMPONE un String trae choice»), ESTIMADO: la fila BAJA. Y 'check-footprints.bash' compara CONJUNTOS EXACTOS (líneas 195-205 del script: ordena, pega con coma y hace '[ "$REAL" = "$ESP" ]') ⇒ **ROMPE TAMBIÉN HACIA ABAJO**, igual que 'check-axioms.bash' (M de [[feedback-estimacion-sin-etiqueta]]).
⚠️ Contraste que refuerza el diagnóstico: Fresh0 (filas 44-46) NO corre ese riesgo, porque su propio docstring (Fresh0.lean:55-59) declara que el 'Classical.choice' entra por DOS vías — 'cst_bound_sym' (tercio excluso, SOBREVIVE) y comparar String con ≠ (DESAPARECE). Como la primera sobrevive, la fila se queda. Enumeration no tiene segunda vía. Por eso es ÉSA y sólo ésa.

🔧 LA MEDICIÓN QUE HAY QUE HACER ANTES DE TOCAR NADA, y que es barata y no invasiva: añadir a 'sondeos/SymbolParamCoste.lean' (que está FUERA del build de FOL) un 'natToFormulaG {S} [EnumSym S]' con su sobreyectividad y un '#print axioms'. Eso mide la caída SIN mover ninguna fila publicada. Es exactamente lo que ADR-068 hizo con FreshSym/EnumSym, y es «antes de construir, medir».

⚠️ Los otros dos riesgos reales, por orden:
1. **El choque de nombres 'S'** — 280 ocurrencias CONTADAS. No es un riesgo matemático, es el que hace que la técnica anunciada de ADR-068 no se aplique tal cual y que el diff crezca de ~140 a ~400 líneas. Decisión previa, no incidental.
2. **'Model' en Semantics.lean:24** — 9 ficheros. No es de mi capa, pero es lo que impide entregar Canonical0 con la misma pasada que HenkinLimit0/Lindenbaum0.

⚠️ Y el riesgo que NO existe, contra lo que el encargo sospechaba: no hace falta 'DecidableEq S' en ninguno de los tres ficheros. MEDIDO en los tres sitios donde parecía hacer falta: Lindenbaum0.lean:98 (filter con 'decide') y :107 ('by_cases') los sirve 'open Classical' (:72); 'occursTerm' es Prop-valued (Eigenvariable.lean:357); y 'cst_bound_sym' (Fresh0.lean:155-161) decide '∃ k, cst k = s' con 'by_cases', no con una instancia.

**Estimación:** CONTADO (no estimado) — declaraciones a tocar en la capa: **83 de 86**.
· HenkinLimit0: 23 de 23 (6 sólo {S}; 17 con {S}+FreshSym+EnumSym)
· Lindenbaum0: 17 de 17 (9 sólo {S}; 7 con EnumSym; 1 con las dos)
· Canonical0: 37 de 39 (quotientOut :239 y quotientOut_eq :242 no se tocan; 31 sólo {S}; 6 con las dos clases)
· Compacity0 (fuera de capa): 6 de 7
CONTADO — apariciones de 'String' en el código: 13 (7 + 0 + 6), TODAS tipo-del-símbolo. Literales de cadena en el cuerpo de los tres ficheros: **0**. Usos de los shims noConfusion/injection/.inj: **0**.
CONTADO — líneas del cuerpo que nombran Term/Formula: 19 (HenkinLimit0) + 26 (Lindenbaum0) + 77 (Canonical0) = **122 líneas**, con 170 ocurrencias del token.
CONTADO — ocurrencias del identificador 'S' usado como TEORÍA: 40 + 72 + 168 = **280**, en 53 declaraciones.
CONTADO — filas de check-footprints de la capa: **11**; '#print axioms' que los ficheros imprimen: **15** ⇒ 4 titulares fuera del control.

ESTIMADO (y lo marco: NO lo ha medido el compilador, y el compilador es la única medida en este proyecto) — líneas a tocar:
· HenkinLimit0: ESTIMADO 25-35 líneas de 313
· Lindenbaum0: ESTIMADO 20-30 de 247
· Canonical0: ESTIMADO 80-110 de 607
· Compacity0: ESTIMADO 10-15 de 132
· TOTAL DE LA CAPA: **ESTIMADO 135-190 líneas**, SI se resuelve el choque de 'S' renombrando el parámetro de símbolos (1 decisión, 0 líneas extra).
· Si en cambio se renombra LA TEORÍA para que 'S' quede para los símbolos: **ESTIMADO 380-450 líneas** (las 135-190 más los 280 renombrados, mecánicos pero con riesgo de 'S' capturado en 'by_cases'/'obtain'/patrones).

⚠️ Y la cifra que NO doy porque no la puedo medir sin compilar, que es la que decide si esta capa es barata o cara: **si la fila 29 ('natToFormula_surj') baja de footprint al generificar Enumeration.** Si baja, hay que reabrir la tabla y eso pide ADR (ADR-041 depende de ella por transitividad). Si no baja, la capa es un diff mecánico. La medición cuesta ~30 líneas en 'sondeos/SymbolParamCoste.lean', fuera del build, y hay que hacerla ANTES de que esto entre en ningún plan — que es exactamente el aviso con el que el encargo lateral se cierra.

#### Módulos

| fichero | l. | decls. a tocar | clases | bloqueantes |
|---|---|---|---|---|
| `E:/dropbox/github/lean4/FOL/FOL/HenkinLimit0.lean` | 313 | 23 | §1 (6 declaraciones, líneas 93-174): sólo {S : Type}. §2-§4 (17 declaraciones, líneas 183-306): {S} + FreshSym S + EnumSym S. Motivo CONTADO: 'cst' aparece en :185, :223, :237, :238, :254, :264, :306 y 'natToFormula' en :194, :195, :197, :211, :223, :237, :305. NO hace falta DecidableEq S: 'occursTerm' es Prop-valued (Eigenvariable.lean:357-359, 'Or (s = c) …'), no usa 'decide'. | CERO bloqueantes propios, MEDIDO: las 7 apariciones de 'String' en el código (:93, :101, :111, :125, :135, :164, :304) son TODAS el tipo del símbolo ('c : String', 'd : String', '∃ c : String'). Cero literales de cadena, cero '++', cero '.length' (grep de literales en el cuerpo: sólo la 'local notation' de la línea 85). Cero usos de noConfusion/injection/.inj ⇒ los tres shims pinchados a String (FOL/FOL.lean:52, :63, :68) NO estorban. BLOQUEANTES DE ABAJO, todos fuera del fichero: (a) FOL/FOL.lean:103-142 — liftTerm/liftTerms/liftFormula/substTerm/substTerms/substFormula SIGUEN siendo String (15 de las 25 declaraciones de FOL/FOL.lean aún dicen Term/Formula), y §1 entero es literalmente sobre ellas; (b) Fresh0.lean:79, :91, :155, :193, :230 (shift, cst, cst_bound_sym, cst_bound_formula, shiftTheory); (c) Enumeration.lean:291, :374 (natToFormula, natToFormula_surj); (d) Henkin0.lean:82, :87, :90, :139 (DerivesSet₀, IsConsistent₀, henkinAx, henkin_step_consistent); (e) Eigenvariable.lean:357-373 (occursTerm/Terms/Formula). |
| `E:/dropbox/github/lean4/FOL/FOL/Lindenbaum0.lean` | 247 | 17 | 9 declaraciones con sólo {S} (derivesSet0_hyp :80, weakening :88, intro_impl :95, elim_impl :111, IsMaximalConsistent₀ :125, max_cons_bot :199, max_cons_contains :204, max_cons_impl :211, IsHenkin₀ :220). 7 con {S} + EnumSym S (LindenbaumStep :130, LindenbaumLimit :137, step_consistent :139, step_subset :148, step_mono :155, limit_bound :162, lindenbaum_lemma :174 — 'natToFormula' en :133, :134, :144, :151, :182, :183, :189). 1 con las DOS (henkin_completion :233, porque toca shiftTheory y henLimit). | CERO 'String' en el código: MEDIDO, la única aparición (:53) está en el docstring. El fichero es el más barato de los tres pese a contener la línea Π⁰₁. ⭐ El punto que parecía bloqueante y NO lo es: Lindenbaum0.lean:98 hace 'Γ.filter (fun y => decide (Not (y = A)))' y :107 'by_cases heq : x = A' — eso pide 'Decidable (y = A)' sobre FormulaG S, y lo sirve el 'open Classical' de la línea 72, no una instancia. ⇒ **NO hace falta DecidableEq S en Lindenbaum0.** Es la medición que descarta la tercera clase. ÚNICO bloqueante real: HenkinLimit0 tiene que ir antes (import en :15). |
| `E:/dropbox/github/lean4/FOL/FOL/Canonical0.lean` | 607 | 37 | De las 39 declaraciones, 2 NO se tocan: 'quotientOut' (:239) y 'quotientOut_eq' (:242) son genéricas en {α : Type u}. De las 37 restantes: 31 con sólo {S}; 6 con {S} + FreshSym S + EnumSym S, y son exactamente las que pasan por henkin_completion/shiftTheory — satisfiable_of_shift (:545), model_existence_lemma₀ (:552), completeness₀ (:563), derives0_complete_iff (:577), derives0_em (:589), derives0_peirce (:594). NO hace falta DecidableEq S: todo lo clásico va por 'open Classical' (:75), 'Classical.byContradiction' (:106, :127, :131, :133, :206, :347, :349, :564) y 'Classical.choose' (:240). | ⛔ EL BLOQUEANTE DURO DE LA CAPA, y está FUERA del fichero: **Semantics.lean:24-25 — 'structure Model (D : Type) where func : String → List D → D ; rel : String → List D → Prop'**. Canonical0 lo consume en :252-255 (canonicalModel), :473 (pullback ρ : String → String), :478, :487, :496. Hasta que 'Model' no sea 'Model S D', Canonical0 no se puede generificar, punto. Y 'Model' se usa en 9 ficheros MEDIDOS: Canonical0, Compacity0, Finitary0, Rename, Semantics, SequentSound0, Skolem0, SkolemN0, Soundness0. Segundo bloqueante externo: Eq0.lean:79 y :100 — 'derives0_eq_func_congr (p : String)' y 'derives0_atom_congr (p : String)', consumidos en Canonical0:211 y :228. Tercero: Soundness0 (import :18), consumido en :578 por derives0_complete_iff. Las 6 apariciones de 'String' en el propio fichero (:200, :216, :473, :478, :487, :496) son todas tipo-del-símbolo ⇒ triviales. Cero literales de cadena en el cuerpo. |
| `E:/dropbox/github/lean4/FOL/FOL/Compacity0.lean` | 132 | 6 | 6 de 7 ('CountableDom' :96 es genérica en D y no se toca). {S} + FreshSym S + EnumSym S en las 6, porque las 6 pasan por shiftTheory o por model_existence. ⚠️ Y aquí EnumSym NO es técnica: sin ella 'loewenheim_skolem_down' (:123) es FALSO, no sólo indemostrable. | Fuera de mi capa por el DAG (Compacity0 ← Canonical0), pero es donde el encargo puso la tercera cita y donde está la consecuencia semántica. Bloqueantes: Canonical0 entero, más 'natToTerm_surj' (Enumeration.lean:268) usado en :116, más 'Model' vía IsSatisfiable/IsSatisfiableCountable (:98-100). Cero 'String' en el código. |

#### ⚖️ La refutación — **MANDA ÉSTA**

NO SOBREVIVE. El plan mide muy bien lo que mira, pero su CADENA DE PREREQUISITOS —que es su producto principal, porque la propia conclusión del plan es «mi capa no puede ser la siguiente, va después de esto»— está incompleta en la raíz, y la pieza que falta es justamente la única clase de módulo donde la técnica que el plan invoca NO vale.

⛔ REFUTACIÓN 1 — el plan OMITE `Derives0` y `Lift0` de un DAG que tenía delante, y `Derives₀` es un INDUCTIVO.
MEDIDO: `E:/dropbox/github/lean4/FOL/FOL/Derives0.lean:98` declara `inductive Derives₀ : List Formula → Formula → Prop`, pinchado a `String` vía `Formula`. Aparece en 21 ficheros (grep -rl: Canonical0, Compacity0, Derives0, Derives1, Derives2, Eigenvariable, Eq0, Finitary0, Hauptsatz0, Henkin0, Herbrand0, HerbrandBlock0, Lift0, Lindenbaum0, Prenex0, PrenexNF0, Propositional0, Rename, SkolemHerbrand0, SkolemNF0, Soundness0). `Henkin0.lean:82` define `DerivesSet₀ (S) (f) := ∃ Γ, … ∧ (Γ ⊢₀ f)` — es decir, TODA la capa del plan es literalmente `Derives₀`.
El plan enumera su «orden real» en cuatro puntos: (1) FOL.lean:103-142, (2) Eigenvariable + Rename, (3) Henkin0, (4) Fresh0 y Enumeration. `Derives0` NO está. `Lift0` tampoco, y `Henkin0.lean:15` lo importa (`import FOL.Lift0`, 15 declaraciones MEDIDAS) y `Henkin0.lean:72` hace `open FOL.Lift0`. La frase del plan «HenkinLimit0 y Lindenbaum0 se pueden cerrar en cuanto estén FOL.lean, Eigenvariable, Rename, Henkin0, Fresh0 y Enumeration» es, por tanto, FALSA tal como está escrita.
Y no es una omisión cosmética: la técnica que el plan cita de ADR-068 («no hace falta renombrar nada, basta añadir {S} a la firma») es cierta para DEFINICIONES y TEOREMAS. Para un INDUCTIVO es exactamente donde ADR-068 midió el único coste real: `FOL/FOL.lean:49-69` documenta que con parámetro Lean 4.31 genera el `noConfusion` HETEROGÉNEO y NO genera `Ctor.inj`, y por eso hubo que escribir tres shims. Parametrizar `Derives₀` reabre ese coste con 22 constructores y en 21 ficheros. El plan no lo contempla en ninguna línea.

⛔ REFUTACIÓN 2 — `derives0_to_derives` aterriza en `Derives`, que es String Y está en lista negra M-11.
MEDIDO: `Derives0.lean:157` `theorem derives0_to_derives : ∀ {Γ f}, (Γ ⊢₀ f) → (Γ ⊢ f)`, con `induction h with` sobre los 22 constructores. `Derives` es `FOL/FOL.lean:211`, `inductive Derives : List Formula → Formula → Prop`, String. Al generificar `Derives₀` hay que DECIDIR: o `Derives` se parametriza también (y es el inductivo que ADR-029 prohíbe inducir de forma PERMANENTE, con lo que hay que escribir por qué parametrizarlo no toca M-11), o `derives0_to_derives` queda como teorema sólo-String y hay que decir dónde se corta. El plan dice «M-11 NO APLICA a esta capa» y ahí acierta, pero eso es una respuesta sobre SU capa a una pregunta que se plantea una capa más abajo, en el prerequisito que no listó.

⛔ REFUTACIÓN 3 — el bloqueante de `FOL.lean` está mal delimitado: falta la CAPA DE NOTACIÓN.
MEDIDO: `FOL/FOL.lean:73` `def neg (f : Formula) : Formula`, `:75` `def top`, `:77` `def iff` — las tres String. Y las notaciones que las usan: `:82` `prefix:75 "¬ " => neg`, `:81` `notation "⊤" => top`, `:87` `infix:55 " ⇔ " => iff`. Más `:92` `instance : Coe String Formula` — una instancia HUÉRFANA que, si no se re-clava, seguirá forzando `S := String` en la elaboración sin que nadie lo vea.
`Canonical0` usa `neg` en 13 sitios MEDIDOS (:134, :135, :139, :142, :145, :350, :352, :354, :356, :357, :565, :567, :571, :589) y `Henkin0.lean:98` también. El plan nombra como bloqueante de `FOL.lean` sólo `:103-142` (lift/subst) y se apoya en el agregado «15 de las 25 declaraciones». Un agregado no es una lista de bloqueantes: `neg` y su notación son lo que impide escribir la primera línea de §5 de Canonical0, y no aparecen.

⛔ REFUTACIÓN 4 — «CERO bloqueantes propios» es falso: hay un INDUCTIVO dentro de la capa.
MEDIDO: `Canonical0.lean:187` `inductive PointwiseEqv (S : Formula → Prop) : List Term → List Term → Prop`. El plan lo cuenta entre las «31 con sólo {S}» y afirma «Cero usos de noConfusion/injection/.inj ⇒ los tres shims pinchados a String NO estorban». Eso confunde dos cosas distintas: no usar los shims existentes no es no NECESITAR shims nuevos. Parametrizar `PointwiseEqv` es añadirle un segundo parámetro de tipo, que es el caso exacto donde ADR-068 midió el coste. (Atenuante MEDIDO por mí: sus tres pruebas — :194, :222, :263 — usan sólo `induction h with | nil | @cons`, sin `injection`, así que probablemente sobreviva; pero el plan no lo miró, y afirma lo contrario de lo que su propia evidencia soporta.)

⚠️ REFUTACIÓN 5 — el análisis de footprint mira en una sola dirección y deja fuera las filas más frágiles.
MEDIDO: `check-footprints.bash` compara conjuntos ORDENADOS con `[ "$REAL" = "$ESP" ]` (líneas 215-228) ⇒ rompe en las dos direcciones. El plan lo dice y lo usa bien para la fila 29. Pero de sus propias 11 filas, DOS están a `-` (línea 47 `FOL.HenkinLimit0.not_occurs_henkinAx`, línea 55 `FOL.Canonical0.eval_pullback_formula`) y el plan no pregunta ni una vez si sobreviven. Son las más frágiles de la tabla: cualquier fuga de `Classical` las rompe.
Y el árbol tiene la medición que lo hace probable: `FOL/Theorems/Eq.lean:5-27` documenta, MEDIDO y con contraejemplo, que «el footprint de una táctica automática no es propiedad del enunciado ni de la táctica: depende del ENTORNO de imports» — el MISMO teorema con las MISMAS tácticas dio `[propext, Classical.choice, Quot.sound]` con `import FOL.FOL` y `[propext, Quot.sound]` con `import ROBINSON_PlusPlus`. Generificar cambia el entorno de imports y cambia la resolución de instancias (hoy `Lindenbaum0:98` resuelve `decide` por `Classical.propDecidable` porque `DecEq.lean` NO está en la cadena — lo he medido; en cuanto Fresh0/Enumeration lleven instancias de clase, eso puede cambiar). ⇒ el «ESTIMADO: el footprint de completeness₀ NO se mueve» no se apoya en nada; lo honesto es NO MEDIDO.

⭐ REFUTACIÓN 6 — LENTE DE VACUIDAD: el plan no responde a la pregunta por la que existe el programa.
El objetivo declarado del paso 4 es poder INSTANCIAR `S`. MEDIDO: al final de esta capa, tal como el plan la describe, `S := List Char` sigue siendo IMPOSIBLE, y no sólo por `Model` (que el plan sí marca): siguen en String `Derives₀` (Derives0.lean:98), `Derives` (FOL.lean:211), `neg/top/iff` (FOL.lean:73-77), `Model` (Semantics.lean:24) y los 21 ficheros que nombran `Derives₀`. Además, las instancias `FreshSym (List Char)` y `EnumSym (List Char)` existen HOY sólo en `E:/dropbox/github/lean4/ROBINSON_PlusPlus/sondeos/SymbolParamCoste.lean:38` y `:87`, que está FUERA del build de FOL: ni siquiera después de la capa habría nada en el árbol de FOL instanciable en `List Char`. El plan compra un parámetro que nadie puede instanciar — que es exactamente lo que ADR-068 ya hizo un nivel más abajo. Un plan de migración que no nombra su primer hito INSTANCIABLE está resolviendo el problema equivocado.

⚠️ REFUTACIÓN 7 — el choque de `S` está inflado.
MEDIDO: `S : Formula → Prop` es la teoría en toda la capa (48 + 74 + 172 = 294 ocurrencias del token en bruto; las 280 «en código» del plan son plausibles). Pero `FOL/FOL.lean:27` liga `S` sólo DENTRO de la declaración de `TermG`: en el sitio de uso el parámetro de símbolos puede llamarse `σ` sin romper ninguna convención ni tocar una línea. Presentar la rama de 380-450 líneas como opción viva infla la estimación de la capa por un factor de ~3 sobre una decisión que tiene coste cero.

LO QUE SÍ SOBREVIVE, y es bastante:
· Los recuentos. He recontado declaraciones: 23 / 17 / 39 / 7 = 86. EXACTO.
· `Semantics.lean:24-25` `structure Model (D : Type) where func : String → List D → D ; rel : String → List D → Prop`. El bloqueante duro es REAL, y la identificación de Canonical0 como punto de unión de la rama sintáctica y la semántica es correcta y es el mejor dato del plan.
· `Eq0.lean:79` y `:100` con `(p : String)`. REAL.
· Cero `noConfusion|injection|.inj|injEq` en los cuatro ficheros: grep VACÍO. REAL.
· «No hace falta `DecidableEq S`»: CIERTO, y por una razón que el plan no da y que refuerza su conclusión — `FOL/DecEq.lean` no está en la cadena de imports de la capa (Lindenbaum0 ← HenkinLimit0 ← {Fresh0 ← Henkin0 ← Lift0 ← Eigenvariable ← Derives0 ← FOL} ∪ {Enumeration ← FOL}), luego `Decidable (¬(y = A))` en `Lindenbaum0:98` sólo puede venir del `open Classical` de `:72`. Es la medición más sólida del plan.
· HALLAZGO 1: `Fresh0.lean:91-93` `cst : Nat → String` aterriza dentro del tipo de símbolos y `:230` `shiftTheory` empuja a un sublenguaje. `EnumSym` basta. CORRECTO.
· HALLAZGO 3: `satisfiable_of_shift` (Canonical0:545) usa `pullback M shift` y NO necesita inverso de `shift`; `cst_bound_sym` (Fresh0:155-161) sale de `by_cases` + `cst_inj`. Las dos clases no tienen que hablarse. CORRECTO y bien citado.
· [A2] del encargo lateral: 15 `#print axioms` (4+4+7) contra 11 filas; los 4 titulares fuera del control son `FOL.HenkinLimit0.hen_consistent` (:311), `FOL.Lindenbaum0.derivesSet0_intro_impl` (:244), `FOL.Lindenbaum0.max_cons_contains` (:246), `FOL.Canonical0.derives0_peirce` (:607). VERIFICADO fila a fila.
· La mentira de docstring: `SymbolParamCoste.lean:24` dice «cst n := "c" ++ toString n», el árbol dice `cst 0 = "g"` / `cst (n+1) = "a" ++ cst n` (Fresh0.lean:91-93). VERIFICADO.
· La estimación va etiquetada ESTIMADO. La regla 1 del proyecto se cumple. (Salvo el «ESTIMADO: el footprint de completeness₀ NO se mueve», que no es una estimación sino una ausencia de medición.)
· Descuadre menor: la capa son 11 filas si Compacity0 queda fuera y 13 si queda dentro (47-51, 54-59, 119-120); la primera frase del plan mete Compacity0 y luego cuenta 11.

**Lo correcto:**

El plan debe reemitirse con SEIS cambios, y los dos primeros son de fondo:

(1) ⛔ AÑADIR `Derives0` y `Lift0` a la raíz de la cadena de prerequisitos, y marcar `Derives₀` (Derives0.lean:98) como INDUCTIVO. Escribir explícitamente que ahí la técnica de ADR-068 («basta añadir {S} a la firma») NO aplica y que reabre el coste medido de ADR-068 (noConfusion heterogéneo + ausencia de `.inj` ⇒ shims), con 22 constructores y 21 ficheros consumidores. El orden correcto MEDIDO es: FOL.lean (inductivos ya hechos; faltan lift/subst :103-142 Y la capa de notación, ver (3)) → Derives0 → {Eigenvariable, Rename} → Lift0 → Henkin0 → {Fresh0, Enumeration} (dos ramas paralelas) → HenkinLimit0 → Lindenbaum0 → [rama semántica: Semantics → Soundness0, más Eq0] → Canonical0 → Compacity0.

(2) ⛔ DECIDIR Y ESCRIBIR qué pasa con `derives0_to_derives` (Derives0.lean:157), cuyo codominio es `Derives` (FOL.lean:211), String y en lista negra M-11 PERMANENTE (ADR-029). Dos opciones, y hay que elegir antes de tocar nada: (a) parametrizar `Derives` también, con una nota razonada de por qué parametrizar un inductivo no reabre M-11 (M-11 prohíbe INDUCIR, no parametrizar); o (b) dejar `derives0_to_derives` como especialización sólo-String, que es la opción barata y coherente con «cuando un tipo está contaminado, se declara al lado el que sí sirve».

(3) ⛔ AMPLIAR el bloqueante de FOL.lean de `:103-142` a `:73-92`: `neg` (:73), `top` (:75), `iff` (:77), las notaciones `¬`/`⊤`/`⇔` que los invocan (:82, :81, :87) e `instance : Coe String Formula` (:92), que es una instancia huérfana y hay que decidir si se re-clava a `[Coe Sym (FormulaG Sym)]` o se retira. `Canonical0` usa `neg` 13 veces (:134,:135,:139,:142,:145,:350,:352,:354,:356,:357,:565,:567,:571,:589).

(4) ⛔ CORREGIR «cero bloqueantes propios» de Canonical0: `PointwiseEqv` (Canonical0:187) es un inductivo de la propia capa y hay que parametrizarlo. Medición ya hecha y que puede copiarse: sus tres consumidores (:194, :222, :263) usan sólo `induction ... with | nil | @cons`, sin `injection` ni `noConfusion`, luego ESTIMADO no necesita shim nuevo — pero eso hay que decirlo, no omitirlo.

(5) ⚠️ REESCRIBIR la sección de footprint en las dos direcciones y degradar la afirmación central. Concretamente: (a) añadir el análisis de las DOS filas a `-` (script líneas 47 `not_occurs_henkinAx` y 55 `eval_pullback_formula`), que son las que rompen ante cualquier fuga de `Classical`; (b) citar `FOL/Theorems/Eq.lean:5-27` — el footprint de una táctica depende del ENTORNO de imports, MEDIDO en este repo con contraejemplo — y concluir que el «ESTIMADO: completeness₀ no se mueve» no es una estimación sino un NO MEDIDO; (c) mantener, porque es correcto, el diagnóstico de la fila 29 (`natToFormula_surj`) y la receta del precedente `DecEq` (nombre viejo como especialización en String, `DecEq.lean:95`), que es la forma de blindar `completeness₀`; (d) ejecutar la medición barata que el propio plan propone —el `natToFormulaG {S} [EnumSym S]` con `#print axioms` en `sondeos/SymbolParamCoste.lean`, fuera del build— ANTES de que nada de esto entre en un plan, y con ella medir también qué le pasa a una fila a `-`.

(6) ⭐ AÑADIR la sección que falta y que es la razón de ser del programa: EL PRIMER HITO INSTANCIABLE. Hay que enunciar, con nombres del árbol, en qué punto exacto `S := List Char` deja de ser imposible, y decir que hoy las instancias `FreshSym (List Char)` y `EnumSym (List Char)` viven SÓLO en `ROBINSON_PlusPlus/sondeos/SymbolParamCoste.lean:38` y `:87`, fuera del build de FOL: mientras no aterricen en el árbol de FOL (o en un módulo `FOL/SymInstances.lean`), generificar capas sigue siendo añadir parámetros que nadie puede instanciar. Sin esta sección el plan es CIERTO y VACUO, que es la clase de fallo que ADR-067 costó caro.

Y una simplificación que quita trabajo: el choque de `S` no es una decisión de capa. El parámetro de símbolos se llama `σ` (o `Sym`) en estos tres ficheros y ya está — `FOL.lean:27` liga `S` sólo dentro de la declaración de `TermG`. La rama de «renombrar la teoría en 280 sitios» debe RETIRARSE del plan, no ofrecerse: infla la estimación de 135-190 a 380-450 líneas sin comprar nada.
