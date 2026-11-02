/-! CONTROL NEGATIVO 2: `#print axioms ORIGEN.lema` cuando `lema` ya NO esta en `ORIGEN`.
    El `open DESTINO` NO lo salva (el nombre esta CUALIFICADO).
    Reproduce `EvalLiftcPrf.lean:701`. DEBE dar exit 1. -/

namespace DESTINO
theorem lema : True := trivial
end DESTINO

namespace ORIGEN
end ORIGEN

open DESTINO

#print axioms ORIGEN.lema
