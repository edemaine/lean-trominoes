/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarRoutePeriodicSoundness
import LeanTrominoes.PeriodicCNFPlanarVariableSoundness

/-!
# Variable-gadget soundness for retained periodic planarization

Complete retained-route propagation carries a routed literal from its clause
terminal to its variable terminal.  The variable duplicator family is
unchanged, so under the occurrence-three premise its existing finite
soundness theorem then identifies that target terminal with the central
periodic atom occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2000000

/-- Every enumerated incidence occurrence has equal source and target
terminal values under a satisfying retained periodic formula. -/
theorem retainedDrawingPeriodicPlanarSATFormula_source_eq_target
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (blockTranslate : Cell)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    planarSATFiniteAssignmentAt formula assignment blockTranslate
          (.inl (.carrier (.terminal
            (occurrence.sourceTerminal formula)))) =
      planarSATFiniteAssignmentAt formula assignment blockTranslate
          (.inl (.carrier (.terminal
            (occurrence.targetTerminal formula)))) := by
  have propagated :=
    retainedConstructedRouteTerminals_assignment_eq
      formula wellFormed degree isLocal assignment satisfies
      blockTranslate
      (occurrence.taggedEdge_mem formula occurrenceMem)
      occurrence.translate
      (occurrence.translate_neighbor formula occurrenceMem)
      defaultTaggedGridSegment
  simpa [CNFRouteOccurrence.sourceTerminal,
    CNFRouteOccurrence.targetTerminal,
    CNFRouteOccurrence.taggedSegments,
    CNFRouteOccurrence.edge,
    taggedRouteSegmentTerminal] using propagated

/-- In a satisfying retained periodic planar formula for an occurrence-three
source, each routed clause terminal equals the central lifted atom reached at
the other end of its incidence route. -/
theorem retainedDrawingPeriodicPlanarSATFormula_source_eq_atom
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (occurrences : formula.OccurrencesAtMost 3)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (blockTranslate : Cell)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    planarSATFiniteAssignmentAt formula assignment blockTranslate
          (.inl (.carrier (.terminal
            (occurrence.sourceTerminal formula)))) =
      planarSATFiniteAssignmentAt formula assignment blockTranslate
          (.inl (.atom occurrence.variableOccurrence)) := by
  let finiteAssignment :=
    planarSATFiniteAssignmentAt formula assignment blockTranslate
  have finiteHolds :
      FormulaHolds finiteAssignment
        (retainedDrawingPlanarSATFormula formula) :=
    (retainedDrawingPeriodicPlanarSATFormula_satisfies_iff
      formula assignment).mp satisfies blockTranslate
  have components :=
    (retainedDrawingPlanarSATFormula_holds_iff
      formula finiteAssignment).mp finiteHolds
  have routeEq :=
    retainedDrawingPeriodicPlanarSATFormula_source_eq_target
      formula wellFormed degree isLocal assignment satisfies
      blockTranslate occurrenceMem
  have targetEq :=
    drawingRoutedVariableFormula_target_eq_atom
      formula occurrences
      (finiteAssignment ∘ planarSATExternalVariableMap)
      components.2.2 occurrenceMem
  exact routeEq.trans targetEq

end PeriodicOrthocrossing
end LeanTrominoes
