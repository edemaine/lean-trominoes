/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.FinitePlanarCarrierOffsets
import LeanTrominoes.SAT.CNF.FiniteCNFUniformOffsets
import LeanTrominoes.SAT.Planar.EmbeddedClauseUniformOffsets
import LeanTrominoes.Graphs.Drawings.Orthogonal.Retained.PeriodicOrthocrossingRetainedPlanarSATPeriodicization

/-! # Every retained planar clause of a finite source has a common offset -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PlanarThreeSAT
set_option maxHeartbeats 1000000
variable {V : Type*} [DecidableEq V] (formula : PeriodicCNF V)

private def coreOffset (node : Sum CarrierNode (CrossingRecord×CrossoverInternal)) : Cell :=
  (normalizePlanarSATVariable formula (planarSATCoreVariableMap node)).2

private theorem bendLinks_offsets_equal {link : EqualityLink CarrierNode}
    (member : link∈drawingRouteBendLinks formula.incidenceGraph) :
    planarNodeOffset formula (.carrier link.first)=planarNodeOffset formula (.carrier link.second) := by
  obtain ⟨bend,_,linkEq⟩ := List.mem_map.mp member
  subst link
  rfl

private theorem core_uniform
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3) (zero : FiniteCNF.ZeroOffsets formula) :
    UniformOffsets (coreOffset formula) (retainedDrawingRoutePlanarCoreFormula formula.incidenceGraph) := by
  apply uniformOffsets_append
  · apply uniformOffsets_crossoverFamily _ _ _ _ _ (crossingPeriodShift formula.incidenceGraph)
    intro crossing _ role
    cases role <;> rfl
  · apply uniformOffsets_map _ Sum.inl id
    apply uniformOffsets_append
    · exact uniformOffsets_equalityFamily _ _ (fun _ member => retainedCarrierLink_offsets_equal formula wellFormed degree zero member)
    · exact uniformOffsets_equalityFamily _ _ (fun _ member => bendLinks_offsets_equal formula member)

private theorem clause_uniform : UniformOffsets (planarNodeOffset formula) (drawingRoutedClauseFormula formula) := by
  intro clause member
  obtain ⟨site,_,clauseEq⟩ := List.mem_map.mp member
  subst clause
  refine ⟨site.2,?_⟩
  intro literal hl
  obtain ⟨occurrence,occurrenceMember,literalEq⟩ := List.mem_map.mp hl
  subst literal
  obtain ⟨tagged,_,occurrenceEq⟩ := List.mem_map.mp occurrenceMember
  subst occurrence
  rfl

private theorem occurrence_edge_zero (zero : FiniteCNF.ZeroOffsets formula)
    {occurrence : CNFRouteOccurrence V} (member : occurrence∈drawingCNFRouteOccurrences formula) :
    occurrence.edge.offset=(0,0) := by
  obtain ⟨tagged,taggedMember,translated⟩ := List.mem_flatMap.mp member
  obtain ⟨translate,_,occurrenceEq⟩ := List.mem_map.mp translated
  subst occurrence
  exact FiniteCNF.incidenceGraph_zero formula zero _
    (List.fst_mem_of_mem_zipIdx (PeriodicCNF.tagged_incidence_edge_mem formula taggedMember))

private theorem variableNode_offset (zero : FiniteCNF.ZeroOffsets formula)
    (site : VariableRouteSite V) {node : PlanarSATNode V} (member : node∈routedVariableNodes formula site) :
    planarNodeOffset formula node=site.2 := by
  have mapped : node∈(variableRouteOccurrencesAt formula site).map (fun occurrence =>
      PlanarSATNode.carrier (.terminal (occurrence.targetTerminal formula))) := by
    simpa [routedVariableNodes] using member
  obtain ⟨occurrence,occurrenceMember,nodeEq⟩ := List.mem_map.mp mapped
  subst node
  simp only [variableRouteOccurrencesAt,List.mem_insertionSort,List.mem_filter,decide_eq_true_eq] at occurrenceMember
  have edgeZero := occurrence_edge_zero formula zero occurrenceMember.1
  have siteEq := congrArg Prod.snd occurrenceMember.2
  simpa [planarNodeOffset,normalizePlanarSATVariable,CNFRouteOccurrence.targetTerminal,
    CNFRouteOccurrence.variableOccurrence,edgeZero,Cell.add] using siteEq

private theorem variable_uniform (zero : FiniteCNF.ZeroOffsets formula) :
    UniformOffsets (planarNodeOffset formula) (drawingRoutedVariableFormula formula) := by
  intro clause member
  obtain ⟨site,_,clauseMember⟩ := List.mem_flatMap.mp member
  apply uniformOffsets_equalityFamily (planarNodeOffset formula) (routedVariableLinksAt formula site) ?_ clause clauseMember
  intro link linkMember
  obtain ⟨tagged,taggedMember,linkEq⟩ := List.mem_map.mp linkMember
  subst link
  exact variableNode_offset formula zero site
    (List.mem_of_mem_take (List.fst_mem_of_mem_zipIdx taggedMember))

theorem retainedDrawingPlanarSATFormula_uniform
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3) (zero : FiniteCNF.ZeroOffsets formula) :
    UniformOffsets (fun node => (normalizePlanarSATVariable formula node).2)
      (retainedDrawingPlanarSATFormula formula) := by
  apply uniformOffsets_append
  · apply uniformOffsets_append
    · exact uniformOffsets_map _ planarSATCoreVariableMap id _ (core_uniform formula wellFormed degree zero)
    · exact uniformOffsets_map _ planarSATExternalVariableMap id _ (clause_uniform formula)
  · exact uniformOffsets_map _ planarSATExternalVariableMap id _ (variable_uniform formula zero)

theorem retainedDrawingPeriodicPlanarSATFormula_uniform
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3) (zero : FiniteCNF.ZeroOffsets formula) :
    FiniteCNF.UniformOffsets (retainedDrawingPeriodicPlanarSATFormula formula) := by
  intro clause member
  obtain ⟨original,originalMember,clauseEq⟩ := List.mem_map.mp member
  subst clause
  obtain ⟨common,all⟩ := retainedDrawingPlanarSATFormula_uniform formula wellFormed degree zero original originalMember
  refine ⟨common,?_⟩
  intro literal hl
  obtain ⟨oldLiteral,oldMember,literalEq⟩ := List.mem_map.mp hl
  subst literal
  exact all oldLiteral oldMember

end LeanTrominoes.PeriodicOrthocrossing
