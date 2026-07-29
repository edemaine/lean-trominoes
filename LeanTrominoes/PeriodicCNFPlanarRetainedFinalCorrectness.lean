import LeanTrominoes.PeriodicCNFPlanarRetainedPeriodicSoundness
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableGauge

/-!
# Correctness of the final retained periodic planar formula

The raw retained planarization preserves satisfiability of the source
periodic CNF.  The final positioned formula additionally wraps variables,
chooses canonical variable and clause gauges, and deduplicates clause
orbits.  Those transformations preserve semantics, so their composition
does too.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The final retained, wrapped, gauged, and deduplicated periodic planar
formula is satisfiable exactly when its source periodic CNF is satisfiable. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_source_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase.Satisfiable ↔
      formula.Satisfiable := by
  exact
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATFormula_satisfiable_iff
      formula).trans
      (retainedDrawingPeriodicPlanarSATFormula_satisfiable_iff
        formula wellFormed degree isLocal occurrences)

end PeriodicOrthocrossing
end LeanTrominoes
