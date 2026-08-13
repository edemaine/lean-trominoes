/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedClausePositionInjectivity

/-!
# Final gauged incidence-vertex positions

This file combines the independently injective variable and clause
positions of the retained planar-SAT construction.  It proves that a
variable position cannot meet a clause position, even across a physical
period translation, and concludes that the complete deduplicated incidence
vertex list has no repetitions and lies in the open fundamental square.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem orientedCrossing_point_ne_drawingRouteBend_drawingPoint_translate
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph)
    (shift : Cell) :
    crossing.point ≠
      Cell.add (routeBend.drawingPoint graph)
        ((drawing graph).periodTranslation shift) := by
  intro pointEq
  rcases drawingRouteBend_adjacentClassifiedSegments
      graph routeBendMem with
    ⟨edge, edgeIndex, incoming, outgoing,
      edgeMem, incomingMem, outgoingMem,
      routeIndexEq, incomingIndexEq, outgoingIndexEq,
      incomingSegmentEq, outgoingSegmentEq⟩
  have geometry :=
    drawingRouteBend_cornerGeometry
      wellFormed degree isLocal routeBendMem
  rcases geometry.incomingAligned with
    incomingHorizontal | incomingVertical
  · have incomingHorizontal' :
        incoming.1.segment.IsHorizontal := by
      rw [incomingSegmentEq]
      exact incomingHorizontal
    apply
      orientedCrossing_point_ne_horizontal_classified_endpoint
        wellFormed degree isLocal crossingMem
        edgeMem incomingMem incomingHorizontal'
        (Cell.add routeBend.translate shift) .finish
    rw [incomingSegmentEq]
    rw [pointEq]
    apply Prod.ext <;>
      simp [RouteBend.drawingPoint,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale] <;>
      ring
  · rcases geometry.outgoingAligned with
      outgoingHorizontal | outgoingVertical
    · have outgoingHorizontal' :
          outgoing.1.segment.IsHorizontal := by
        rw [outgoingSegmentEq]
        exact outgoingHorizontal
      apply
        orientedCrossing_point_ne_horizontal_classified_endpoint
          wellFormed degree isLocal crossingMem
          edgeMem outgoingMem outgoingHorizontal'
          (Cell.add routeBend.translate shift) .start
      rw [outgoingSegmentEq]
      rw [pointEq]
      apply Prod.ext <;>
        simp [RouteBend.drawingPoint,
          PeriodicGridDrawing.periodTranslation,
          Cell.add, Cell.scale] <;>
        ring
    · have incomingVertical' :
          incoming.1.segment.IsVertical := by
        rw [incomingSegmentEq]
        exact incomingVertical
      have outgoingVertical' :
          outgoing.1.segment.IsVertical := by
        rw [outgoingSegmentEq]
        exact outgoingVertical
      rcases drawingRouteBend_centerPlacement
          graph isLocal routeBendMem with
        ⟨placementEdge, placementEdgeIndex,
          placement, placementIndex,
          placementEdgeMem, placementMem,
          placementRouteIndexEq, placementIndexEq,
          placementPointEq⟩
      have edgeIndexEq :
          placementEdgeIndex = edgeIndex := by
        rw [← placementRouteIndexEq, ← routeIndexEq]
      have taggedEdgeEq :
          (placementEdge, placementEdgeIndex) =
            (edge, edgeIndex) :=
        tagged_eq_of_mem_zipIdx_of_snd_eq
          placementEdgeMem edgeMem edgeIndexEq
      have placementEdgeEq :
          placementEdge = edge :=
        congrArg Prod.fst taggedEdgeEq
      subst placementEdge
      rw [edgeIndexEq] at placementMem
      have incomingPlacementIndexEq :
          incoming.2 = placementIndex := by
        omega
      have outgoingPlacementIndexEq :
          outgoing.2 = placementIndex + 1 := by
        omega
      rcases
          routeBendCenterPlacement_kind_port_of_adjacent_vertical
            graph edge edgeIndex placementMem
            incomingMem outgoingMem
            incomingPlacementIndexEq
            outgoingPlacementIndexEq
            incomingVertical' outgoingVertical' with
        ⟨port, placementKindEq⟩
      apply
        orientedCrossing_point_snd_ne_portRow crossingMem
          (Cell.add
            (Cell.add routeBend.translate placement.offset)
            shift).2
      have pointYEq := congrArg Prod.snd pointEq
      have placementYEq := congrArg Prod.snd placementPointEq
      rw [placementKindEq] at placementYEq
      simp [RouteBend.drawingPoint,
        RouteBendCenterKind.position,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale] at pointYEq placementYEq ⊢
      ring_nf at pointYEq placementYEq ⊢
      omega

theorem planarSATMacrocellData_eq_of_position_eq_translate
    {firstPosition secondPosition firstCenter secondCenter
      firstLocal secondLocal shift : Cell}
    (periodFactor : Nat)
    (firstBounds :
      0 ≤ firstLocal.1 ∧ firstLocal.1 < planarMacroScale ∧
        0 ≤ firstLocal.2 ∧ firstLocal.2 < planarMacroScale)
    (secondBounds :
      0 ≤ secondLocal.1 ∧ secondLocal.1 < planarMacroScale ∧
        0 ≤ secondLocal.2 ∧ secondLocal.2 < planarMacroScale)
    (firstPositionEq :
      firstPosition =
        Cell.add
          (Cell.scale planarMacroScale firstCenter) firstLocal)
    (secondPositionEq :
      secondPosition =
        Cell.add
          (Cell.scale planarMacroScale secondCenter) secondLocal)
    (positionEq :
      firstPosition =
        Cell.add secondPosition
          (Cell.scale
            (planarMacroScale * periodFactor) shift)) :
    firstCenter =
        Cell.add secondCenter
          (Cell.scale periodFactor shift) ∧
      firstLocal = secondLocal := by
  apply planarSATMacrocellPosition_eq firstBounds secondBounds
  rw [← firstPositionEq, positionEq, secondPositionEq]
  rcases secondCenter with ⟨secondCenterX, secondCenterY⟩
  rcases secondLocal with ⟨secondLocalX, secondLocalY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  apply Prod.ext <;>
    simp [Cell.add, Cell.scale] <;>
    ring

theorem retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_eq_emod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
        ⟨atom⟩ =
      ((drawingPeriodicPlanarSATVariablePosition formula atom).1 %
          (drawingPeriodicPlanarSATPlacement formula).period,
        (drawingPeriodicPlanarSATVariablePosition formula atom).2 %
          (drawingPeriodicPlanarSATPlacement formula).period) := by
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_mk,
    PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position]
  rfl

theorem periodicVariablePosition_eq_clausePosition_translate_of_eq_residue
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (positionEq :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
          ⟨atom⟩ =
        clauseResidue formula clause) :
    ∃ shift,
      drawingPeriodicPlanarSATVariablePosition formula atom =
        Cell.add clause.position
          (Cell.scale
            (drawingPeriodicPlanarSATPlacement formula).period
            shift) := by
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_eq_emod]
      at positionEq
  refine
    ⟨((drawingPeriodicPlanarSATVariablePosition formula atom).1 /
          (drawingPeriodicPlanarSATPlacement formula).period -
        clause.position.1 /
          (drawingPeriodicPlanarSATPlacement formula).period,
      (drawingPeriodicPlanarSATVariablePosition formula atom).2 /
          (drawingPeriodicPlanarSATPlacement formula).period -
        clause.position.2 /
          (drawingPeriodicPlanarSATPlacement formula).period),
      ?_⟩
  apply cell_eq_add_scale_of_emod_eq
  · exact congrArg Prod.fst positionEq
  · exact congrArg Prod.snd positionEq

theorem periodicPlanarSATVariableLocalPosition_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PeriodicPlanarSATVariable Variable)
    (valid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula atom) :
    IsRetainedPlanarSATVariableLocalPosition
      (periodicPlanarSATVariableLocalPosition atom) := by
  cases atom with
  | terminal indexed endpoint =>
      apply Or.inl
      apply segmentTerminalLocalPosition_isCarrierPort
      exact drawing_isOrthogonal wellFormed isLocal degree indexed valid
  | boundary boundary =>
      exact Or.inl boundary.side.isCarrierPortLocalPosition
  | atom atom =>
      exact Or.inr (Or.inl rfl)
  | crossoverInternal internal =>
      exact Or.inr (Or.inr ⟨internal.2, rfl⟩)

theorem carrierClauseLocalPositions_avoid_periodicVariables :
    ∀ offset ∈ carrierClauseLocalPositions,
      ¬IsRetainedPlanarSATVariableLocalPosition offset := by
  intro offset offsetMem
  simp [carrierClauseLocalPositions] at offsetMem
  rcases offsetMem with rfl | rfl | rfl | rfl
  all_goals
    simp [IsRetainedPlanarSATVariableLocalPosition,
      IsCarrierPortLocalPosition, duplicatorArmCenterPosition]
  all_goals
    intro internal
    cases internal <;>
      norm_num [crossoverInternalVariable,
        CrossoverVariable.position]

theorem retainedGaugedVariablePosition_ne_clauseResidue
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PeriodicPlanarSATVariable Variable)
    (atomValid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula atom)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataValid : metadata.RetainedValid formula) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
        ⟨atom⟩ ≠
      clauseResidue formula metadata.clause := by
  intro positionResidueEq
  rcases periodicVariablePosition_eq_clausePosition_translate_of_eq_residue
      formula atom metadata.clause positionResidueEq with
    ⟨shift, positionEq⟩
  have atomPositionEq :=
    drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local
      formula atom
  have atomBoundsStrict :=
    periodicPlanarSATVariableLocalPosition_in_macrocell atom
  have atomBounds :
      0 ≤ (periodicPlanarSATVariableLocalPosition atom).1 ∧
        (periodicPlanarSATVariableLocalPosition atom).1 <
          planarMacroScale ∧
        0 ≤ (periodicPlanarSATVariableLocalPosition atom).2 ∧
        (periodicPlanarSATVariableLocalPosition atom).2 <
          planarMacroScale :=
    ⟨le_of_lt atomBoundsStrict.1, atomBoundsStrict.2.1,
      le_of_lt atomBoundsStrict.2.2.1, atomBoundsStrict.2.2.2⟩
  rcases metadata with ⟨clause, source⟩
  cases source with
  | carrier link localClauseIndex =>
      rcases carrierClause_exists_localOffset_mem
          wellFormed degree isLocal metadataValid.1 metadataValid.2 with
        ⟨offset, clausePositionEq, offsetMem⟩
      have offsetBounds : 0 ≤ offset.1 ∧
          offset.1 < planarMacroScale ∧
          0 ≤ offset.2 ∧ offset.2 < planarMacroScale := by
        simp [carrierClauseLocalPositions] at offsetMem
        rcases offsetMem with rfl | rfl | rfl | rfl <;>
          norm_num [planarMacroScale]
      have data :=
        planarSATMacrocellData_eq_of_position_eq_translate
          (drawingGridSize (PeriodicCNF.incidenceGraph formula))
          atomBounds offsetBounds atomPositionEq clausePositionEq
          (by simpa [drawingPeriodicPlanarSATPlacement,
            planarMacroScale] using positionEq)
      apply
        carrierClauseLocalPositions_avoid_periodicVariables
          offset offsetMem
      rw [← data.2]
      exact periodicPlanarSATVariableLocalPosition_valid
        formula wellFormed degree isLocal atom atomValid
  | crossover crossing localClauseIndex =>
      rcases crossoverClause_localPosition_avoids_carrier_or_internal
          metadataValid.2 with
        ⟨offset, clausePositionEq, offsetBounds, offsetAvoids⟩
      have clausePositionEq' :
          clause.position =
            Cell.add
              (Cell.scale planarMacroScale crossing.point) offset := by
        simpa [crossingMacroOrigin] using clausePositionEq
      have data :=
        planarSATMacrocellData_eq_of_position_eq_translate
          (drawingGridSize (PeriodicCNF.incidenceGraph formula))
          atomBounds offsetBounds atomPositionEq clausePositionEq'
          (by simpa [drawingPeriodicPlanarSATPlacement,
            planarMacroScale] using positionEq)
      cases atom with
      | terminal indexed endpoint =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inl
            (segmentTerminalLocalPosition_isCarrierPort
              indexed.segment endpoint
              (drawing_isOrthogonal wellFormed isLocal degree
                indexed atomValid))
      | boundary boundary =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inl boundary.side.isCarrierPortLocalPosition
      | atom sourceAtom =>
          have centerEq := data.1
          have reverseEq :=
            pointEq_translate_symm
              (PeriodicCNF.incidenceGraph formula) shift centerEq
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree metadataValid.1
              (drawingVariableRouteSite_vertex_mem formula atomValid)
              (Cell.neg shift))
              (by
                simpa [periodicPlanarSATVariableDrawingPoint,
                  liftedIncidenceVertexPosition,
                  PeriodicGridDrawing.periodTranslation,
                  drawing_gridSize, Cell.add, Cell.scale] using reverseEq)
      | crossoverInternal internal =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inr ⟨internal.2, rfl⟩
  | bend routeBend localClauseIndex =>
      rcases bendClause_localPosition_avoids_carrier_or_atom
          (PeriodicCNF.incidenceGraph formula) routeBend
          metadataValid.2 with
        ⟨offset, clausePositionEq, offsetBounds, offsetAvoids⟩
      have data :=
        planarSATMacrocellData_eq_of_position_eq_translate
          (drawingGridSize (PeriodicCNF.incidenceGraph formula))
          atomBounds offsetBounds atomPositionEq clausePositionEq
          (by simpa [drawingPeriodicPlanarSATPlacement,
            planarMacroScale] using positionEq)
      cases atom with
      | terminal indexed endpoint =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inl
            (segmentTerminalLocalPosition_isCarrierPort
              indexed.segment endpoint
              (drawing_isOrthogonal wellFormed isLocal degree
                indexed atomValid))
      | boundary boundary =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inl boundary.side.isCarrierPortLocalPosition
      | atom sourceAtom =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inr rfl
      | crossoverInternal internal =>
          exact
            (orientedCrossing_point_ne_drawingRouteBend_drawingPoint_translate
              wellFormed degree isLocal
              (orientedCrossings_subset_orientedCrossingHalo
                (PeriodicCNF.incidenceGraph formula) atomValid)
              ((List.mem_dedup).mp metadataValid.1) shift)
              data.1
  | routedClause site =>
      rcases routedClause_localPosition_avoids_variables
          formula site metadataValid.2 with
        ⟨offset, clausePositionEq, offsetBounds, offsetAvoids⟩
      have clausePositionEq' :
          clause.position =
            Cell.add
              (Cell.scale planarMacroScale
                (liftedIncidenceVertexPosition
                  formula (.clause site.1) site.2)) offset := by
        simpa [routedClauseOrigin,
          liftedIncidenceVertexMacroOrigin] using clausePositionEq
      have data :=
        planarSATMacrocellData_eq_of_position_eq_translate
          (drawingGridSize (PeriodicCNF.incidenceGraph formula))
          atomBounds offsetBounds atomPositionEq clausePositionEq'
          (by simpa [drawingPeriodicPlanarSATPlacement,
            planarMacroScale] using positionEq)
      apply offsetAvoids
      rw [← data.2]
      exact periodicPlanarSATVariableLocalPosition_valid
        formula wellFormed degree isLocal _ atomValid
  | routedVariable site armIndex arm link localClauseIndex =>
      have linkMem :
          link ∈ routedVariableLinksAt formula site :=
        List.fst_mem_of_mem_zipIdx metadataValid.2.1
      have positionsEq :
          link.positions =
            ⟨Cell.add (routedVariableOrigin formula site)
                (duplicatorArmEqualityPositions arm).forward,
              Cell.add (routedVariableOrigin formula site)
                (duplicatorArmEqualityPositions arm).backward⟩ := by
        rw [routedVariableLink_positions formula site linkMem,
          metadataValid.2.2.1]
        rfl
      rcases
          routedVariableClause_localPosition_avoids_carrier_or_atom
            (routedVariableOrigin formula site) arm link positionsEq
            metadataValid.2.2.2 with
        ⟨offset, clausePositionEq, offsetBounds, offsetAvoids⟩
      have clausePositionEq' :
          clause.position =
            Cell.add
              (Cell.scale planarMacroScale
                (liftedIncidenceVertexPosition
                  formula (.variable site.1) site.2)) offset := by
        simpa [routedVariableOrigin,
          liftedIncidenceVertexMacroOrigin] using clausePositionEq
      have data :=
        planarSATMacrocellData_eq_of_position_eq_translate
          (drawingGridSize (PeriodicCNF.incidenceGraph formula))
          atomBounds offsetBounds atomPositionEq clausePositionEq'
          (by simpa [drawingPeriodicPlanarSATPlacement,
            planarMacroScale] using positionEq)
      cases atom with
      | terminal indexed endpoint =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inl
            (segmentTerminalLocalPosition_isCarrierPort
              indexed.segment endpoint
              (drawing_isOrthogonal wellFormed isLocal degree
                indexed atomValid))
      | boundary boundary =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inl boundary.side.isCarrierPortLocalPosition
      | atom sourceAtom =>
          apply offsetAvoids
          rw [← data.2]
          exact Or.inr rfl
      | crossoverInternal internal =>
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree
              (orientedCrossings_subset_orientedCrossingHalo
                (PeriodicCNF.incidenceGraph formula) atomValid)
              (drawingVariableRouteSite_vertex_mem
                formula metadataValid.1)
              (Cell.add site.2 shift))
              (by
                calc
                  internal.1.point =
                      Cell.add
                        (liftedIncidenceVertexPosition
                          formula (.variable site.1) site.2)
                        ((drawing
                          (PeriodicCNF.incidenceGraph formula)).periodTranslation
                            shift) := by
                    simpa [periodicPlanarSATVariableDrawingPoint,
                      PeriodicGridDrawing.periodTranslation,
                      drawing_gridSize] using data.1
                  _ = _ :=
                    liftedIncidenceVertexPosition_add_periodTranslation
                      formula (.variable site.1) site.2 shift)

theorem deduplicated_clause_exists_metadata
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses) :
    ∃ metadata ∈ retainedDrawingPlanarSATClauseMetadata formula,
      metadata.RetainedValid formula ∧
        clause.position = clauseResidue formula metadata.clause := by
  apply deduplicateByLiterals_clausePositions_satisfy
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (fun position =>
      ∃ metadata ∈ retainedDrawingPlanarSATClauseMetadata formula,
        metadata.RetainedValid formula ∧
          position = clauseResidue formula metadata.clause)
  · intro position positionMember
    rw [anchorNormalized_clausePositions_eq_metadata_residues
      formula wellFormed degree isLocal clausesNonempty] at positionMember
    rcases List.mem_map.mp positionMember with
      ⟨metadata, metadataMember, positionEq⟩
    exact
      ⟨metadata, metadataMember,
        retainedDrawingPlanarSATClauseMetadata_valid
          formula metadataMember, positionEq.symm⟩
  · exact List.mem_map.mpr ⟨clause, clauseMember, rfl⟩

theorem deduplicated_variableClausePositions_disjoint
    {Variable : Type*} [DecidableEq Variable]
    [wrappedDecidableEq :
      DecidableEq (WrappedPeriodicPlanarSATVariable Variable)]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    List.Disjoint
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.incidenceVariableVertices.map fun vertex =>
        match vertex with
        | CNFVertex.variable atom =>
            (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              formula).position atom
        | .clause _ => (0, 0))
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.map PositionedPeriodicClause.position) := by
  rw [List.disjoint_left]
  intro position variablePositionMem clausePositionMem
  rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
    at variablePositionMem
  rcases List.mem_map.mp variablePositionMem with
    ⟨atom, atomMember, variablePositionEq⟩
  rcases List.mem_map.mp clausePositionMem with
    ⟨clause, clauseMember, clausePositionEq⟩
  rcases deduplicated_clause_exists_metadata
      formula wellFormed degree isLocal clausesNonempty
      clause clauseMember with
    ⟨metadata, metadataMember, metadataValid,
      metadataPositionEq⟩
  have atomValid :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
      formula wellFormed degree isLocal ((List.mem_dedup).mp atomMember)
  apply
    retainedGaugedVariablePosition_ne_clauseResidue
      formula wellFormed degree isLocal atom.original atomValid
      metadata metadataValid
  calc
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
        ⟨atom.original⟩ =
        position := by
      cases atom
      simpa using variablePositionEq
    _ = clause.position := clausePositionEq.symm
    _ = clauseResidue formula metadata.clause := metadataPositionEq

theorem PositionedPeriodicCNF.incidenceVertexPositions_nodup_of
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (variableNodup :
      (source.erase.incidenceVariableVertices.map fun vertex =>
        match vertex with
        | CNFVertex.variable atom => placement.position atom
        | CNFVertex.clause _ => (0, 0)).Nodup)
    (clauseNodup :
      (source.clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          placement)).Nodup)
    (disjoint :
      List.Disjoint
        (source.erase.incidenceVariableVertices.map fun vertex =>
          match vertex with
          | CNFVertex.variable atom => placement.position atom
          | CNFVertex.clause _ => (0, 0))
        (source.clauses.map
          (PositionedPeriodicCNF.canonicalClausePosition
            placement))) :
    (source.incidenceVertexPositions placement).Nodup := by
  exact List.Nodup.append variableNodup clauseNodup disjoint

theorem deduplicated_canonicalClausePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.map
      (PositionedPeriodicCNF.canonicalClausePosition
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula))).Nodup := by
  rw [deduplicated_canonicalClausePositions_eq_stored]
  exact deduplicated_storedClausePositions_nodup
    formula wellFormed degree isLocal clausesNonempty

theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_incidenceVertexPositions_nodup
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    [wrappedDecidableEq :
      DecidableEq (WrappedPeriodicPlanarSATVariable Variable)]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (PositionedPeriodicCNF.incidenceVertexPositions
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula)).Nodup := by
  refine @PositionedPeriodicCNF.incidenceVertexPositions_nodup_of
    (WrappedPeriodicPlanarSATVariable Variable)
    wrappedDecidableEq
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
    ?_ ?_ ?_
  · rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
    apply
      (List.nodup_dedup
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.variableOccurrences).map_on
    intro first firstMem second secondMem positionEq
    apply
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_injective_of_valid
        formula wellFormed degree isLocal
    · exact
        retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
          formula wellFormed degree isLocal
          ((List.mem_dedup).mp firstMem)
    · exact
        retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
          formula wellFormed degree isLocal
          ((List.mem_dedup).mp secondMem)
    · simpa [Function.comp_def] using positionEq
  · exact @deduplicated_canonicalClausePositions_nodup
      Variable variableDecidableEq
      formula wellFormed degree isLocal clausesNonempty
  · rw [deduplicated_canonicalClausePositions_eq_stored]
    rw [List.disjoint_left]
    intro position variablePositionMem clausePositionMem
    rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
      at variablePositionMem
    rcases List.mem_map.mp variablePositionMem with
      ⟨atom, atomMember, variablePositionEq⟩
    rcases List.mem_map.mp clausePositionMem with
      ⟨clause, clauseMember, clausePositionEq⟩
    rcases deduplicated_clause_exists_metadata
        formula wellFormed degree isLocal clausesNonempty
        clause clauseMember with
      ⟨metadata, metadataMember, metadataValid,
        metadataPositionEq⟩
    have atomValid :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
        formula wellFormed degree isLocal ((List.mem_dedup).mp atomMember)
    apply
      retainedGaugedVariablePosition_ne_clauseResidue
        formula wellFormed degree isLocal atom.original atomValid
        metadata metadataValid
    calc
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
          ⟨atom.original⟩ =
          position := by
        cases atom
        simpa using variablePositionEq
      _ = clause.position := clausePositionEq.symm
      _ = clauseResidue formula metadata.clause := metadataPositionEq

theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_incidenceVertexPositions_inSquare
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    [wrappedDecidableEq :
      DecidableEq (WrappedPeriodicPlanarSATVariable Variable)]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (position : Cell)
    (positionMem :
      position ∈
        PositionedPeriodicCNF.incidenceVertexPositions
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)) :
    0 < position.1 ∧
      position.1 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period ∧
      0 < position.2 ∧
      position.2 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
  rw [PositionedPeriodicCNF.incidenceVertexPositions] at positionMem
  rcases List.mem_append.mp positionMem with
    variablePositionMem | clausePositionMem
  · rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
      at variablePositionMem
    rcases List.mem_map.mp variablePositionMem with
      ⟨atom, _atomMem, positionEq⟩
    rw [← positionEq]
    exact
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
        formula atom
  · rw [deduplicated_canonicalClausePositions_eq_stored]
      at clausePositionMem
    exact deduplicated_storedClausePositions_inSquare
      formula wellFormed degree isLocal clausesNonempty
      position clausePositionMem

end LeanTrominoes.PeriodicOrthocrossing
