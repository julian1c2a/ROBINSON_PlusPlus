/-
📏 MEDICIÓN (B) 2026-08-23 — el COSTE de recodificar los símbolos por índice de tabla.

Teníamos el **beneficio** (sondeo S5: 424×) pero nunca el **coste**. Y S5 medía un **proxy** —la
suma de puntos Unicode de 10 símbolos (19 068) contra la de los índices 0..9 (45)—, no el tamaño
real de los códigos. Aquí se mide lo que importa.

## BENEFICIO — real, y MAYOR de lo que decía S5

| axioma | `formCode` hoy | símbolos | fracción | con índices |
|---|---:|---:|---:|---:|
| `ax_tc_zero` | 49 015 nodos | 48 528 | **99 %** | ~708 (**69×**) |
| `ax_L0_cons_def` | 14 754 | 14 570 | **98 %** | ~242 (**61×**) |
| `ax4_add_zero` | 142 | 97 | 68 % | ~51 (2,8×) |

`strCodeM "σ"` solo ya son **966 nodos** (963 `succ` anidados: U+03C3 = 963). En los axiomas del
verificador, **el 98‑99 % del código son los nombres de los símbolos**.

## COSTE — acotado, pero en la BASE del árbol

**~10 teoremas** a reescribir, en **4 módulos**, todos los que recurren char‑a‑char:

* `Meta/CodeDecode.lean` — `decodeChars_charsCodeM`, `decodeStr_strCodeM`, `decodeStr_inj`
  ⚠️ **es el módulo A de `NegVerifier`, hoy COMPLETO y verificado**
* `Meta/CodeDistinct.lean` — `charsCode_ne`, `strCode_ne`
* `Meta/CodeNumeralPrf.lean` — `prf_charsCode_numeral`, `prf_strCode_numeral`
* `Meta/DerivCondPrf.lean` — `liftTerm_charsCode/_strCode`, `substTerm_charsCode/_strCode`

✅ **Todo lo demás trata `strCode s` como OPACO** y no se entera: los constructores de código
(`consT`, `addcT`, `carcT`, `nthcT`, `mulcT`, `div2cT`, …) sólo lo pasan a `funcc`.

## ⚠️ PROBLEMA DE DISEÑO ENCONTRADO: una tabla pura NO es total

`Term.func : String → List Term → Term` admite **String arbitrario**. Los ~29 símbolos del proyecto
son finitos *en la práctica*, pero no *por tipo*. Una tabla necesita salida para lo demás.

**Diseño limpio: codificación ETIQUETADA.** `strCodeM s = cons tag payload`, con `tag = 0` ⟹ índice
de tabla, `tag = 1` ⟹ lista de chars (lo de hoy). Total, inyectiva, y un nodo extra por símbolo.
El precio: la recursión uniforme sobre chars pasa a ser un **análisis de casos** — que es justo lo
que los 10 teoremas tienen que absorber.

⛔ Restringir el lenguaje a un alfabeto finito **NO** vale: cambiaría el teorema (sería la
incompletitud de un lenguaje restringido).

## EL DATO QUE DECIDE: hoy NO es un cuello de botella

* Tiempos de build de los módulos afectados: **4‑11 s** (`CodeDecode` el peor, 11 s). Nada patológico.
* `codeNat φ` **nunca se reduce** (medido en S3): la magnitud no afecta a la elaboración.
* `axiomsCodeT` se mantiene **opaco a propósito** (`ax_axiomsCodeT_eq`), justo para no materializar
  el término gigante. **El proyecto ya rodeó el problema.**

## ⇒ RECOMENDACIÓN

Beneficio real (60‑70×) pero **teórico hoy**; coste = tocar `CodeDecode`, que está completo y
verificado. **Mala relación AHORA.**

**Hay un momento bueno, y es concreto:** *antes* de escribir los módulos **C‑F** de `NegVerifier`.
Ese rediseño va a tocar la codificación de todos modos (ver `sondeos/CodeNatInj.lean`), y hacerlo
después obligaría a reescribirlos dos veces.
-/
import ROBINSON_PlusPlus.Meta
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel

partial def tsize : Term → Nat
  | .var _ => 1
  | .func _ args => 1 + args.foldl (fun a t => a + tsize t) 0

/-- Todos los símbolos que aparecen en un término / fórmula, CON multiplicidad. -/
partial def symsT : Term → List String
  | .var _ => []
  | .func s args => s :: args.foldl (fun a t => a ++ symsT t) []
partial def symsF : Formula → List String
  | .bottom => []
  | .atom p ts => p :: ts.foldl (fun a t => a ++ symsT t) []
  | .eq t u => symsT t ++ symsT u
  | .impl a b => symsF a ++ symsF b
  | .and a b => symsF a ++ symsF b
  | .or a b => symsF a ++ symsF b
  | Formula.forall a => symsF a
  | .ex a => symsF a

/-- Índice de tabla: posición en la lista de símbolos distintos. -/
def tabla : List String :=
  [zero_sym, succ_sym, add_sym, mul_sym, pred_sym, div2_sym, mod2_sym, cons_sym,
   concat_sym, pow_sym, sqrt_sym, sub_sym, lt_sym,
   "::", "carc", "cdrc", "lenc", "nthc", "liftc", "liftfc", "liftsc",
   "substfc", "substtc", "substtsc", "tcFn", "runFn", "premsOf", "validProofFn", "axiomsCodeT"]
def idxOf (s : String) : Nat := (tabla.findIdx? (· == s)).getD 99

partial def report (nombre : String) (f : Formula) : String :=
  let ss := symsF f
  let costeUnicode := ss.foldl (fun a s => a + tsize (strCodeM s)) 0
  let costeIdx     := ss.foldl (fun a s => a + (idxOf s + 2)) 0
  let total := tsize (formCode f)
  s!"{nombre}: total={total} nodos | simbolos={ss.length} ocurrencias | \
coste simbolos: Unicode={costeUnicode} ({100*costeUnicode/total}%) -> indices={costeIdx} | \
formCode quedaria en ~{total - costeUnicode + costeIdx} nodos"

#eval report "ax_tc_zero     " ax_tc_zero
#eval report "ax_L0_cons_def " ax_L0_cons_def
#eval report "ax4_add_zero   " ax4_add_zero
