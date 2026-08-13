/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarFormula

/-!
# Assignments on routed SAT incidences

A plane-wide assignment to the source atoms induces one value on every
translated incidence route: look up the metadata occurrence by its global
protoedge index and evaluate that literal's atom at the route's target cell.
This file proves the lookup law and uses it to satisfy every routed variable
duplicator.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Route values induced by a plane-wide source assignment.  Out-of-range
indices receive `false`; all constructed incidence routes are proved to have
in-range indices. -/
def incidenceRouteAssignment
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) :
    RouteOccurrenceKey → Bool :=
  fun key =>
    match (PeriodicCNF.incidencesWithMetadata formula)[key.1]? with
    | some incidence =>
        assignment incidence.literal.atom
          (Cell.add key.2 incidence.edge.offset)
    | none => false

/-- Central lifted atoms retain the original plane-wide assignment. -/
def incidenceAtomAssignment
    {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    VariableRouteSite Variable → Bool :=
  fun site => assignment site.1 site.2

/-- A tagged metadata occurrence and neighboring translation produce the
corresponding routed occurrence in the executable drawing list. -/
theorem CNFRouteOccurrence.mem_drawing_of_tagged
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMem :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata formula).zipIdx)
    (translate : Cell)
    (translateNeighbor : IsNeighborTranslation translate) :
    (⟨tagged.1, tagged.2, translate⟩ :
      CNFRouteOccurrence Variable) ∈
        drawingCNFRouteOccurrences formula := by
  apply List.mem_flatMap.mpr
  refine ⟨tagged, taggedMem, ?_⟩
  exact List.mem_map.mpr
    ⟨translate,
      (mem_neighborTranslations_iff translate).mpr
        translateNeighbor,
      rfl⟩

/-- On every enumerated route occurrence, indexed lookup recovers exactly
the metadata incidence used to construct that route. -/
theorem incidenceRouteAssignment_occurrence
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    incidenceRouteAssignment formula assignment occurrence.routeKey =
      assignment occurrence.incidence.literal.atom
        (Cell.add occurrence.translate occurrence.edge.offset) := by
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨tagged, taggedMem, occurrenceMem⟩
  rcases List.mem_map.mp occurrenceMem with
    ⟨translate, translateMem, occurrenceEq⟩
  subst occurrence
  have lookup :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMem
  simp [incidenceRouteAssignment, CNFRouteOccurrence.routeKey,
    CNFRouteOccurrence.edge, CNFIncidence.edge, lookup]

/-- The external assignment gives a routed target terminal the same value as
the central atom at the lifted variable vertex it reaches. -/
theorem routedPlanarSATExternalAssignment_target_eq_atom
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    routedPlanarSATExternalAssignment
        (incidenceRouteAssignment formula assignment)
        (incidenceAtomAssignment assignment)
        (.carrier (.terminal (occurrence.targetTerminal formula))) =
      routedPlanarSATExternalAssignment
        (incidenceRouteAssignment formula assignment)
        (incidenceAtomAssignment assignment)
        (.atom occurrence.variableOccurrence) := by
  change
    incidenceRouteAssignment formula assignment occurrence.routeKey =
      assignment occurrence.incidence.literal.atom
        (Cell.add occurrence.translate occurrence.edge.offset)
  exact incidenceRouteAssignment_occurrence
    formula assignment occurrenceMem

/-- If every listed node agrees with a default center, then every total
`getD` port selection agrees with that center as well. -/
theorem assignment_getD_eq_center
    {Node : Type*}
    (assignment : Node → Bool)
    (nodes : List Node) (center : Node)
    (allAgree :
      ∀ node ∈ nodes, assignment node = assignment center)
    (index : Nat) :
    assignment (nodes.getD index center) =
      assignment center := by
  by_cases inBounds : index < nodes.length
  · rw [List.getD_eq_getElem _ _ inBounds]
    exact allAgree nodes[index] (List.getElem_mem inBounds)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt inBounds)]

/-- The induced route and atom assignment satisfies every routed variable
duplicator. -/
theorem drawingRoutedVariableFormula_holds_incidenceAssignment
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) :
    FormulaHolds
      (routedPlanarSATExternalAssignment
        (incidenceRouteAssignment formula assignment)
        (incidenceAtomAssignment assignment))
      (drawingRoutedVariableFormula formula) := by
  let external :=
    routedPlanarSATExternalAssignment
      (incidenceRouteAssignment formula assignment)
      (incidenceAtomAssignment assignment)
  apply
    (drawingRoutedVariableFormula_holds_iff
      formula external).mpr
  intro site siteMem
  let nodes : List (PlanarSATNode Variable) :=
    routedVariableNodes formula site
  have allAgree :
      ∀ node ∈ nodes,
        external node = external (.atom site) := by
    intro node nodeMem
    rcases List.mem_map.mp (List.mem_dedup.mp nodeMem) with
      ⟨occurrence, occurrenceMem, nodeEq⟩
    subst node
    have occurrenceData :
        occurrence ∈ drawingCNFRouteOccurrences formula ∧
          occurrence.variableOccurrence = site := by
      simpa [variableRouteOccurrencesAt] using occurrenceMem
    rw [← occurrenceData.2]
    exact
      routedPlanarSATExternalAssignment_target_eq_atom
        formula assignment occurrenceData.1
  change
    external (nodes.getD 0 (.atom site)) = external (.atom site) ∧
      external (nodes.getD 1 (.atom site)) = external (.atom site) ∧
        external (nodes.getD 2 (.atom site)) = external (.atom site)
  exact
    ⟨assignment_getD_eq_center external nodes (.atom site)
        allAgree 0,
      assignment_getD_eq_center external nodes (.atom site)
        allAgree 1,
      assignment_getD_eq_center external nodes (.atom site)
        allAgree 2⟩

end PeriodicOrthocrossing
end LeanTrominoes
