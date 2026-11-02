/-! CONTROL NEGATIVO 1: `export ORIGEN (lema)` cuando `lema` ya NO esta en `ORIGEN`.
    El `open DESTINO` NO lo salva. Reproduce `EvalLiftcPrf.lean:673`. DEBE dar exit 1. -/

namespace DESTINO
theorem lema : True := trivial
end DESTINO

namespace ORIGEN
end ORIGEN

open DESTINO

export ORIGEN (lema)
