/-!
# LO QUE SE LE ESCAPO: al borrar los lemas de `EvalLiftcPrf` hay DOS referencias mas
  que ROMPEN el build, y no son «consumidores» en el sentido de uso en una prueba.

`EvalLiftcPrf.lean:673`  → el bloque `export ROBINSON_PlusPlus.Meta.EvalLiftcPrf (...)`
                            todavia LISTA los dos nombres.
`EvalLiftcPrf.lean:701`  → `#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_isTermCodeE1_of_In`

El preparador conto «UN solo consumidor en produccion, `EvalLiftcPrf.lean:417`».
Aqui se demuestra, COMPILADO, que las otras dos referencias son ERRORES DUROS, y que el
`open` del namespace de destino NO las salva.

Este fichero es el CONTROL POSITIVO (lo que si funciona). El control NEGATIVO va en
`ADV_T2e1_export_MAL.lean` y en `ADV_T2e1_print_MAL.lean`, que deben dar exit 1.
-/

namespace DESTINO
theorem lema : True := trivial
end DESTINO

namespace ORIGEN
-- el lema ya NO vive aqui: se ha «bajado» a DESTINO
end ORIGEN

open DESTINO   -- exactamente lo que hace `EvalLiftcPrf.lean:164` con `CodeWitnessPrf.SinWTs`

-- (a) el uso en una PRUEBA si se salva con el `open`  → esto es `EvalLiftcPrf.lean:417`
example : True := lema

-- (b) REMEDIO para el bloque `export`: re-exportar desde el namespace NUEVO
export DESTINO (lema)

-- (c) y el `#print axioms` hay que reapuntarlo al nombre NUEVO
#print axioms DESTINO.lema
