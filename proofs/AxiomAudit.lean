/- Trust-base audit: run `lake env lean AxiomAudit.lean` and read the output.
   Each line prints the exact kernel axioms a theorem depends on. -/
import GateProofs
open PAPGate

#print axioms sound                 -- [propext]
#print axioms stale_refused         -- [propext]
#print axioms divergent_refused     -- [propext]
#print axioms noncompile_refused    -- [propext]
#print axioms unexecuted_refused    -- [propext]
#print axioms gate_discriminates    -- (no axioms)
#print axioms not_rubber_stamp      -- (no axioms)
#print axioms not_black_hole        -- (no axioms)
