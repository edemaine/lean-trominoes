/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableVertices
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierPositionInjectivity
import LeanTrominoes.PeriodicOrthocrossingPlanarSATMacrocellCenters

/-!
# Injective positions of retained planar-SAT variables

The retained planar-SAT drawing has three kinds of variables: carrier nodes,
routed-variable centers, and internal crossover variables.  Their refined
positions are injective within each kind and disjoint across kinds.  The
proof separates the macrocell center from its bounded local coordinate.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem retainedCarrierNode_localPosition_isCarrierPort
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph) :
    IsCarrierPortLocalPosition node.localPosition := by
  cases node with
  | boundary boundary =>
      exact boundary.side.isCarrierPortLocalPosition
  | terminal terminal =>
      apply segmentTerminalLocalPosition_isCarrierPort
      apply drawing_isOrthogonal wellFormed isLocal degree
      exact retainedCarrierNode_indexed_mem graph nodeMem

theorem drawingPlanarSATAtom_eq_of_position_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : VariableRouteSite Variable}
    (firstMem : first ∈ drawingVariableRouteSites formula)
    (secondMem : second ∈ drawingVariableRouteSites formula)
    (positionEq :
      drawingPlanarSATVariablePosition formula (.inl (.atom first)) =
        drawingPlanarSATVariablePosition formula (.inl (.atom second))) :
    first = second := by
  have positionData :=
    planarSATMacrocellPosition_eq
      duplicatorArmCenterPosition_in_macrocell
      duplicatorArmCenterPosition_in_macrocell
      (by
        simpa [drawingPlanarSATVariablePosition,
          liftedIncidenceVertexMacroOrigin] using positionEq)
  exact
    liftedVariableRouteSite_eq formula firstMem secondMem positionData.1

theorem drawingPlanarSATInternal_eq_of_position_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstCrossing secondCrossing : CrossingRecord}
    {firstInternal secondInternal : CrossoverInternal}
    (firstMem :
      firstCrossing ∈ orientedCrossingHalo
        (PeriodicCNF.incidenceGraph formula))
    (secondMem :
      secondCrossing ∈ orientedCrossingHalo
        (PeriodicCNF.incidenceGraph formula))
    (positionEq :
      drawingPlanarSATVariablePosition formula
          (.inr (firstCrossing, firstInternal)) =
        drawingPlanarSATVariablePosition formula
          (.inr (secondCrossing, secondInternal))) :
    (firstCrossing, firstInternal) =
      (secondCrossing, secondInternal) := by
  have positionData :=
    planarSATMacrocellPosition_eq
      (CrossoverVariable.position_in_macrocell
        (crossoverInternalVariable firstInternal))
      (CrossoverVariable.position_in_macrocell
        (crossoverInternalVariable secondInternal))
      (by
        simpa [drawingPlanarSATVariablePosition,
          crossingMacroOrigin] using positionEq)
  have crossingEq :=
    orientedCrossing_eq_of_point_eq
      wellFormed degree isLocal firstMem secondMem positionData.1
  have internalEq :=
    crossoverInternalVariable_position_injective positionData.2
  exact Prod.ext crossingEq internalEq

theorem drawingPlanarSATCarrier_ne_atom
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrier : CarrierNode}
    (carrierMem :
      carrier ∈ retainedDrawingCarrierNodes
        (PeriodicCNF.incidenceGraph formula))
    (site : VariableRouteSite Variable) :
    drawingPlanarSATVariablePosition formula (.inl (.carrier carrier)) ≠
      drawingPlanarSATVariablePosition formula (.inl (.atom site)) := by
  intro positionEq
  have positionData :=
    planarSATMacrocellPosition_eq
      (CarrierNode.localPosition_in_macrocell carrier)
      duplicatorArmCenterPosition_in_macrocell
      (by
        simpa [drawingPlanarSATVariablePosition,
          CarrierNode.position_eq_scale_add_local,
          liftedIncidenceVertexMacroOrigin] using positionEq)
  exact
    (retainedCarrierNode_localPosition_isCarrierPort
      wellFormed degree isLocal carrierMem
      ).ne_duplicatorArmCenterPosition positionData.2

theorem drawingPlanarSATCarrier_ne_internal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrier : CarrierNode}
    (carrierMem :
      carrier ∈ retainedDrawingCarrierNodes
        (PeriodicCNF.incidenceGraph formula))
    (crossing : CrossingRecord) (internal : CrossoverInternal) :
    drawingPlanarSATVariablePosition formula (.inl (.carrier carrier)) ≠
      drawingPlanarSATVariablePosition formula
        (.inr (crossing, internal)) := by
  intro positionEq
  have positionData :=
    planarSATMacrocellPosition_eq
      (CarrierNode.localPosition_in_macrocell carrier)
      (CrossoverVariable.position_in_macrocell
        (crossoverInternalVariable internal))
      (by
        simpa [drawingPlanarSATVariablePosition,
          CarrierNode.position_eq_scale_add_local,
          crossingMacroOrigin] using positionEq)
  exact
    (retainedCarrierNode_localPosition_isCarrierPort
      wellFormed degree isLocal carrierMem
      ).ne_crossoverInternalPosition internal positionData.2

theorem drawingPlanarSATAtom_ne_internal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (crossing : CrossingRecord) (internal : CrossoverInternal) :
    drawingPlanarSATVariablePosition formula (.inl (.atom site)) ≠
      drawingPlanarSATVariablePosition formula
        (.inr (crossing, internal)) := by
  intro positionEq
  have positionData :=
    planarSATMacrocellPosition_eq
      duplicatorArmCenterPosition_in_macrocell
      (CrossoverVariable.position_in_macrocell
        (crossoverInternalVariable internal))
      (by
        simpa [drawingPlanarSATVariablePosition,
          liftedIncidenceVertexMacroOrigin,
          crossingMacroOrigin] using positionEq)
  exact
    crossoverInternalPosition_ne_duplicatorArmCenterPosition
      internal positionData.2.symm

theorem drawingPlanarSATVariable_eq_of_valid_of_position_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {first second : PlanarSATVariable Variable}
    (firstValid : RetainedDrawingPlanarSATVariableValid formula first)
    (secondValid : RetainedDrawingPlanarSATVariableValid formula second)
    (positionEq :
      drawingPlanarSATVariablePosition formula first =
        drawingPlanarSATVariablePosition formula second) :
    first = second := by
  rcases first with (⟨firstCarrier⟩ | ⟨firstSite⟩) |
    ⟨firstCrossing, firstInternal⟩
  · rcases second with (⟨secondCarrier⟩ | ⟨secondSite⟩) |
      ⟨secondCrossing, secondInternal⟩
    · congr 2
      exact retainedCarrierNode_eq_of_position_eq
        wellFormed degree isLocal firstValid secondValid positionEq
    · exact False.elim
        (drawingPlanarSATCarrier_ne_atom
          formula wellFormed degree isLocal firstValid secondSite positionEq)
    · exact False.elim
        (drawingPlanarSATCarrier_ne_internal
          formula wellFormed degree isLocal firstValid
          secondCrossing secondInternal positionEq)
  · rcases second with (⟨secondCarrier⟩ | ⟨secondSite⟩) |
      ⟨secondCrossing, secondInternal⟩
    · exact False.elim
        (drawingPlanarSATCarrier_ne_atom
          formula wellFormed degree isLocal secondValid firstSite
          positionEq.symm)
    · congr 2
      exact drawingPlanarSATAtom_eq_of_position_eq
        formula firstValid secondValid positionEq
    · exact False.elim
        (drawingPlanarSATAtom_ne_internal
          formula firstSite secondCrossing secondInternal positionEq)
  · rcases second with (⟨secondCarrier⟩ | ⟨secondSite⟩) |
      ⟨secondCrossing, secondInternal⟩
    · exact False.elim
        (drawingPlanarSATCarrier_ne_internal
          formula wellFormed degree isLocal secondValid
          firstCrossing firstInternal positionEq.symm)
    · exact False.elim
        (drawingPlanarSATAtom_ne_internal
          formula secondSite firstCrossing firstInternal positionEq.symm)
    · congr 1
      exact drawingPlanarSATInternal_eq_of_position_eq
        formula wellFormed degree isLocal
        firstValid secondValid positionEq

/-- The position map is injective on the variables actually used by the
assembled retained incidence drawing. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_variablePosition_injective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    ∀ first ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).variableVertices,
      ∀ second ∈
          (retainedDrawingPlanarSATLocalIncidenceDrawing
            formula).variableVertices,
        (retainedDrawingPlanarSATLocalIncidenceDrawing
            formula).variablePosition first =
            (retainedDrawingPlanarSATLocalIncidenceDrawing
              formula).variablePosition second →
          first = second := by
  intro first firstMem second secondMem positionEq
  apply drawingPlanarSATVariable_eq_of_valid_of_position_eq
    formula wellFormed degree isLocal
  · exact
      retainedDrawingPlanarSATLocalIncidenceDrawing_variableVertices_valid
        formula wellFormed degree isLocal first firstMem
  · exact
      retainedDrawingPlanarSATLocalIncidenceDrawing_variableVertices_valid
        formula wellFormed degree isLocal second secondMem
  · simpa using positionEq

end LeanTrominoes.PeriodicOrthocrossing
