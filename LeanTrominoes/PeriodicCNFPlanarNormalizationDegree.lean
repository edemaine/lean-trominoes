import LeanTrominoes.PeriodicCNFPlanarTerminalNormalizationDegree

/-!
# Degree eight for normalized planar SAT

The separately normalized component bounds transfer through global clause
deduplication to the actual unwrapped periodic planar-SAT formula.  Opaque
wrapping preserves every occurrence count, yielding the degree-eight premise
needed by the occurrence-splitting reduction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem
    deduplicatedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3) :
    (deduplicatedDrawingPeriodicPlanarSATFormula
      formula).OccurrencesAtMost 8 := by
  intro output
  have componentSublist :=
    deduplicatedDrawingPeriodicPlanarSATFormula_variableOccurrences_sublist
      formula
  have outputLe :
      (deduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.count output ≤
      (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula
        formula).variableOccurrences.count output :=
    componentSublist.subperm.count_le output
  cases output with
  | terminal indexed endpoint =>
      exact
        outputLe.trans
          (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_terminal_count_le_eight
            wellFormed degree isLocal indexed endpoint)
  | boundary boundary =>
      exact
        outputLe.trans
          ((componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_boundary_count_le_six
            wellFormed degree isLocal boundary).trans (by omega))
  | atom atom =>
      exact
        outputLe.trans
          ((componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_atom_count_le_six
            occurrences atom).trans (by omega))
  | crossoverInternal internal =>
      exact
        outputLe.trans
          (componentwiseDeduplicatedDrawingPeriodicPlanarSATFormula_crossoverInternal_count_le_eight
            wellFormed degree isLocal internal)

theorem
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3) :
    (deduplicatedWrappedDrawingPeriodicPlanarSATFormula
      formula).OccurrencesAtMost 8 := by
  rintro ⟨output⟩
  rw [
    deduplicatedWrappedDrawingPeriodicPlanarSATFormula_count
      formula output]
  exact
    deduplicatedDrawingPeriodicPlanarSATFormula_occurrencesAtMostEight
      wellFormed degree isLocal occurrences output

end PeriodicOrthocrossing
end LeanTrominoes
