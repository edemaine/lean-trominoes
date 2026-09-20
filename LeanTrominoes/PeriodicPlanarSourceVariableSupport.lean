/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDegree
import LeanTrominoes.PeriodicCNFPlanarDegree

/-! # Original variable support survives retained planarization -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PlanarThreeSAT
set_option maxHeartbeats 1000000

theorem routed_variable_center_occurs {V : Type*} [DecidableEq V] (f : PeriodicCNF V)
    (occurrence : CNFRouteOccurrence V) (member : occurrence ∈ drawingCNFRouteOccurrences f) :
    ∃ clause ∈ drawingRoutedVariableFormula f, (.atom occurrence.variableOccurrence,false) ∈ clause.literals := by
  let site := occurrence.variableOccurrence
  have siteMember : site ∈ drawingVariableRouteSites f := by
    simp only [drawingVariableRouteSites,List.mem_dedup,List.mem_map]
    exact ⟨occurrence,member,rfl⟩
  have occurrenceMember : occurrence ∈ variableRouteOccurrencesAt f site := by
    simp [variableRouteOccurrencesAt,List.mem_insertionSort,member,site]
  have nodeMember : PlanarSATNode.carrier (.terminal (occurrence.targetTerminal f)) ∈ routedVariableNodes f site := by
    simp only [routedVariableNodes,List.mem_dedup,List.mem_map]
    exact ⟨occurrence,occurrenceMember,rfl⟩
  cases nodesEq : routedVariableNodes f site with
  | nil => simp [nodesEq] at nodeMember
  | cons first rest =>
      let positions := routedVariableEqualityPositions f site first.duplicatorArm
      let clause : EmbeddedClause (PlanarSATNode V) :=
        ⟨positions.forward,[(first,true),(.atom site,false)]⟩
      refine ⟨clause,?_,by simp [clause,site]⟩
      apply List.mem_flatMap.mpr
      refine ⟨site,siteMember,?_⟩
      unfold routedVariableFormulaAt equalityFamily
      apply List.mem_flatMap.mpr
      refine ⟨⟨first,.atom site,positions⟩,?_,by simp [equalityInstance,clause]⟩
      simp [routedVariableLinksAt,equalityTakeThreeLinks,nodesEq,positions]

theorem retained_periodic_atom_occurs {V : Type*} [DecidableEq V] (f : PeriodicCNF V)
    {atom : V} (member : atom ∈ f.variableOccurrences) :
    PeriodicPlanarSATVariable.atom atom ∈ (retainedDrawingPeriodicPlanarSATFormula f).variableOccurrences := by
  have mapped : atom ∈ (PeriodicCNF.incidencesWithMetadata f).map (fun i => i.literal.atom) := by
    rw [PeriodicCNF.incidencesWithMetadata_literal_atoms]
    exact member
  obtain ⟨incidence,incidenceMember,atomEq⟩ := List.mem_map.mp mapped
  obtain ⟨index,lookup⟩ := List.mem_iff_getElem?.mp incidenceMember
  let occurrence : CNFRouteOccurrence V := ⟨incidence,index,(0,0)⟩
  have occurrenceMember : occurrence ∈ drawingCNFRouteOccurrences f := by
    unfold drawingCNFRouteOccurrences
    apply List.mem_flatMap.mpr
    refine ⟨(incidence,index),List.mem_zipIdx_iff_getElem?.mpr lookup,?_⟩
    exact List.mem_map.mpr ⟨(0,0),by decide,rfl⟩
  obtain ⟨clause,clauseMember,literalMember⟩ := routed_variable_center_occurs f occurrence occurrenceMember
  let wrapped := clause.rename (@planarSATExternalVariableMap V)
  have wrappedMember : wrapped ∈ retainedDrawingPlanarSATFormula f := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨clause,clauseMember,rfl⟩
  simp only [PeriodicCNF.variableOccurrences,retainedDrawingPeriodicPlanarSATFormula,
    List.flatMap_map,List.mem_flatMap]
  refine ⟨wrapped,wrappedMember,?_⟩
  simp only [periodicizePlanarSATClause,List.map_map,List.mem_map,Function.comp_apply]
  refine ⟨(.inl (.atom occurrence.variableOccurrence),false),?_,?_⟩
  · exact List.mem_map.mpr ⟨(.atom occurrence.variableOccurrence,false),literalMember,rfl⟩
  · simpa [periodicizePlanarSATLiteral,normalizePlanarSATVariable,occurrence,
      CNFRouteOccurrence.variableOccurrence] using congrArg PeriodicPlanarSATVariable.atom atomEq

end LeanTrominoes.PeriodicOrthocrossing
