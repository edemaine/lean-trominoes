import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits

/-!
# Global retained planar-SAT clause orbits

This module separates straight-carrier clauses from all four non-carrier
gadget families modulo the physical drawing period.  It then combines that
separation with the carrier and non-carrier classifications to show that an
equal clause-position residue determines one gauged normalized clause.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

def noncarrierClauseLocalPositions : List Cell :=
  crossoverClauseLocalPositions ++
    bendClauseLocalPositions ++
    [(10, 10),
      (2, 7), (5, 6),
      (4, 9), (6, 8),
      (6, 6), (8, 9)]

theorem routedVariableClause_position_eq_localOffset
    {Variable : Type*}
    (origin : Cell)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (positionsEq :
      link.positions =
        ⟨Cell.add origin
            (duplicatorArmEqualityPositions arm).forward,
          Cell.add origin
            (duplicatorArmEqualityPositions arm).backward⟩)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (member :
      (clause, clauseIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx) :
    ∃ finiteIndex : Fin 2,
      clauseIndex = finiteIndex.1 ∧
        clause.position =
          Cell.add origin
            (routedVariableClauseLocalOffset (arm, finiteIndex)) := by
  have sourceMember := member
  unfold drawingPlanarSATRoutedVariableFormulaAt at sourceMember
  rw [List.zipIdx_map] at sourceMember
  rcases List.mem_map.mp sourceMember with
    ⟨sourceTagged, sourceTaggedMember, sourceTaggedEq⟩
  have sourceData :=
    equalityInstance_clausePosition_and_index sourceTaggedMember
  rcases sourceData with
      ⟨indexEq, positionEq⟩ |
      ⟨indexEq, positionEq⟩
  · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · exact (congrArg Prod.snd sourceTaggedEq).symm.trans indexEq
    · have mappedPositionEq :=
        congrArg (fun tagged => tagged.1.position) sourceTaggedEq
      simp [EmbeddedClause.rename,
        EmbeddedClause.map] at mappedPositionEq
      rw [← mappedPositionEq, positionEq, positionsEq]
      simp [routedVariableClauseLocalOffset]
  · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
    · exact (congrArg Prod.snd sourceTaggedEq).symm.trans indexEq
    · have mappedPositionEq :=
        congrArg (fun tagged => tagged.1.position) sourceTaggedEq
      simp [EmbeddedClause.rename,
        EmbeddedClause.map] at mappedPositionEq
      rw [← mappedPositionEq, positionEq, positionsEq]
      simp [routedVariableClauseLocalOffset]

theorem routedVariableClauseLocalOffset_mem_noncarrier
    (arm : DuplicatorArm) (index : Fin 2) :
    routedVariableClauseLocalOffset (arm, index) ∈
      noncarrierClauseLocalPositions := by
  fin_cases index <;> cases arm <;>
    native_decide

theorem noncarrierClause_exists_localOffset_mem
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (notCarrier :
      ¬∃ link, metadata.source.component = .carrier link)
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula =
        some center) :
    ∃ offset,
      metadata.clause.position =
          Cell.add (Cell.scale planarMacroScale center) offset ∧
        offset ∈ noncarrierClauseLocalPositions := by
  rcases metadata with ⟨clause, source⟩
  cases source with
  | crossover crossing localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEq
      subst center
      rcases crossoverClause_localPosition_strict valid.2 with
        ⟨offset, positionEq, _bounds⟩
      refine ⟨offset, by
        simpa [crossingMacroOrigin] using positionEq, ?_⟩
      unfold noncarrierClauseLocalPositions
      simp only [List.mem_append]
      left
      left
      exact crossoverClause_localOffset_mem valid.2 positionEq
  | carrier link localClauseIndex =>
      exact False.elim (notCarrier ⟨link, rfl⟩)
  | bend bend localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEq
      subst center
      rcases bendClause_localPosition_strict
          (PeriodicCNF.incidenceGraph formula)
          bend valid.2 with
        ⟨offset, positionEq, _bounds⟩
      refine ⟨offset, positionEq, ?_⟩
      unfold noncarrierClauseLocalPositions
      simp only [List.mem_append]
      left
      right
      exact bendClause_localOffset_mem
        (PeriodicCNF.incidenceGraph formula) valid.2 positionEq
  | routedClause site =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEq
      subst center
      refine ⟨(10, 10), ?_, ?_⟩
      · rw [valid.2]
        simp [routedClauseAt,
          liftedIncidenceVertexMacroOrigin,
          EmbeddedClause.rename, EmbeddedClause.map,
          Cell.add, Cell.scale, planarMacroScale]
      · simp [noncarrierClauseLocalPositions]
  | routedVariable site armIndex arm link localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEq
      subst center
      have linkMem :
          link ∈ routedVariableLinksAt formula site :=
        List.fst_mem_of_mem_zipIdx valid.2.1
      have positionsEq :
          link.positions =
            ⟨Cell.add (routedVariableOrigin formula site)
                (duplicatorArmEqualityPositions arm).forward,
              Cell.add (routedVariableOrigin formula site)
                (duplicatorArmEqualityPositions arm).backward⟩ := by
        rw [routedVariableLink_positions formula site linkMem,
          valid.2.2.1]
        rfl
      rcases routedVariableClause_position_eq_localOffset
          (routedVariableOrigin formula site)
          arm link positionsEq valid.2.2.2 with
        ⟨finiteIndex, _indexEq, positionEq⟩
      refine
        ⟨routedVariableClauseLocalOffset (arm, finiteIndex),
          ?_, routedVariableClauseLocalOffset_mem_noncarrier
            arm finiteIndex⟩
      simpa [routedVariableOrigin,
        liftedIncidenceVertexMacroOrigin] using positionEq

def carrierClauseLocalPositions : List Cell :=
  [(14, 6), (17, 6), (6, 14), (6, 17)]

theorem retainedDrawingCompleteCarrierLink_first_localPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    if link.first.isHorizontal then
      link.first.localPosition = (11, 6)
    else
      link.first.localPosition = (6, 11) := by
  cases firstNode : link.first with
  | boundary boundary =>
      rcases retainedDrawingCompleteCarrierLink_first_boundary_side
          wellFormed degree isLocal linkMem firstNode with
        sideEq | sideEq
      · rcases boundary with ⟨crossing, side⟩
        simp only at sideEq
        subst side
        simp [CarrierNode.isHorizontal,
          CarrierNode.localPosition, CrossingSide.localPosition,
          CrossoverVariable.position]
      · rcases boundary with ⟨crossing, side⟩
        simp only at sideEq
        subst side
        simp [CarrierNode.isHorizontal,
          CarrierNode.localPosition, CrossingSide.localPosition,
          CrossoverVariable.position]
  | terminal terminal =>
      have lower :=
        retainedDrawingCompleteCarrierLink_first_terminal_isLower
          wellFormed degree isLocal linkMem firstNode
      have aligned :=
        retainedDrawingCompleteCarrierLink_terminal_axisAligned
          wellFormed degree isLocal linkMem (Or.inl firstNode)
      rcases aligned with horizontal | vertical
      · rw [if_pos (show
          (CarrierNode.terminal terminal).isHorizontal = true by
            simp [CarrierNode.isHorizontal, horizontal])]
        change
          segmentTerminalLocalPosition
              terminal.indexed.segment terminal.endpoint =
            (11, 6)
        simpa [CornerPort.position] using
          segmentTerminalLocalPosition_eq_east_of_isLower
            terminal horizontal lower
      · have notHorizontal :
            ¬terminal.indexed.segment.IsHorizontal := by
          intro horizontal
          exact vertical.2 horizontal.1
        rw [if_neg (show
          ¬(CarrierNode.terminal terminal).isHorizontal = true by
            simp [CarrierNode.isHorizontal, notHorizontal])]
        change
          segmentTerminalLocalPosition
              terminal.indexed.segment terminal.endpoint =
            (6, 11)
        simpa [CornerPort.position] using
          segmentTerminalLocalPosition_eq_north_of_isLower
            terminal vertical lower

theorem carrierClause_exists_localOffset_mem
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link).zipIdx) :
    ∃ offset,
      (clause.position =
          Cell.add
            (Cell.scale planarMacroScale
              (link.first.drawingPoint
                (PeriodicCNF.incidenceGraph formula)))
            offset) ∧
        offset ∈ carrierClauseLocalPositions := by
  have localPosition :=
    retainedDrawingCompleteCarrierLink_first_localPosition
      wellFormed degree isLocal linkMem
  have position :=
    carrierClause_position_eq_first_add_offset
      wellFormed degree isLocal linkMem clauseMember
  have indexCases := carrierClause_position_and_index clauseMember
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal] at localPosition
    rcases indexCases with
        ⟨indexEq, _clausePosition⟩ |
        ⟨indexEq, _clausePosition⟩
    · refine ⟨(14, 6), ?_, by
        simp [carrierClauseLocalPositions]⟩
      rw [position, CarrierNode.position_eq_scale_add_local,
        localPosition, indexEq, horizontal]
      simp [carrierClauseOffset, Cell.add]
      all_goals omega
    · refine ⟨(17, 6), ?_, by
        simp [carrierClauseLocalPositions]⟩
      rw [position, CarrierNode.position_eq_scale_add_local,
        localPosition, indexEq, horizontal]
      simp [carrierClauseOffset, Cell.add]
      all_goals omega
  · rw [if_neg horizontal] at localPosition
    rcases indexCases with
        ⟨indexEq, _clausePosition⟩ |
        ⟨indexEq, _clausePosition⟩
    · refine ⟨(6, 14), ?_, by
        simp [carrierClauseLocalPositions]⟩
      rw [position, CarrierNode.position_eq_scale_add_local,
        localPosition, indexEq]
      simp [carrierClauseOffset, horizontal, Cell.add]
      all_goals omega
    · refine ⟨(6, 17), ?_, by
        simp [carrierClauseLocalPositions]⟩
      rw [position, CarrierNode.position_eq_scale_add_local,
        localPosition, indexEq]
      simp [carrierClauseOffset, horizontal, Cell.add]
      all_goals omega

theorem cell_emod_planarMacroScale_eq_of_planarSATPeriodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : Cell} (shift : Cell)
    (equal :
      first =
        Cell.add second
          (Cell.scale
            (drawingPeriodicPlanarSATPlacement formula).period
            shift)) :
    first.1 % planarMacroScale =
        second.1 % planarMacroScale ∧
      first.2 % planarMacroScale =
        second.2 % planarMacroScale := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  constructor
  · have coordinateEq := congrArg Prod.fst equal
    simp [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] at coordinateEq
    change firstX % 20 = secondX % 20
    rw [coordinateEq]
    rw [show
      secondX +
          20 *
            (drawingGridSize
              (PeriodicCNF.incidenceGraph formula) : Int) *
            shiftX =
        secondX +
          20 *
            ((drawingGridSize
              (PeriodicCNF.incidenceGraph formula) : Int) *
              shiftX) by ring,
      Int.add_mul_emod_self_left]
  · have coordinateEq := congrArg Prod.snd equal
    simp [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] at coordinateEq
    change firstY % 20 = secondY % 20
    rw [coordinateEq]
    rw [show
      secondY +
          20 *
            (drawingGridSize
              (PeriodicCNF.incidenceGraph formula) : Int) *
            shiftY =
        secondY +
          20 *
            ((drawingGridSize
              (PeriodicCNF.incidenceGraph formula) : Int) *
              shiftY) by ring,
      Int.add_mul_emod_self_left]

theorem localOffset_emod_eq_of_position_eq_translate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstPosition secondPosition firstCenter secondCenter
      firstOffset secondOffset shift : Cell}
    (firstPositionEq :
      firstPosition =
        Cell.add
          (Cell.scale planarMacroScale firstCenter)
          firstOffset)
    (secondPositionEq :
      secondPosition =
        Cell.add
          (Cell.scale planarMacroScale secondCenter)
          secondOffset)
    (positionEq :
      firstPosition =
        Cell.add secondPosition
          (Cell.scale
            (drawingPeriodicPlanarSATPlacement formula).period
            shift)) :
    firstOffset.1 % planarMacroScale =
        secondOffset.1 % planarMacroScale ∧
      firstOffset.2 % planarMacroScale =
        secondOffset.2 % planarMacroScale := by
  have positionResidues :=
    cell_emod_planarMacroScale_eq_of_planarSATPeriodTranslate
      formula shift positionEq
  rcases firstPosition with ⟨firstPositionX, firstPositionY⟩
  rcases secondPosition with ⟨secondPositionX, secondPositionY⟩
  rcases firstCenter with ⟨firstCenterX, firstCenterY⟩
  rcases secondCenter with ⟨secondCenterX, secondCenterY⟩
  rcases firstOffset with ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffset with ⟨secondOffsetX, secondOffsetY⟩
  have firstXEq := congrArg Prod.fst firstPositionEq
  have firstYEq := congrArg Prod.snd firstPositionEq
  have secondXEq := congrArg Prod.fst secondPositionEq
  have secondYEq := congrArg Prod.snd secondPositionEq
  simp only [Cell.add, Cell.scale, planarMacroScale] at firstXEq firstYEq secondXEq secondYEq
  constructor
  · rw [firstXEq, secondXEq] at positionResidues
    simpa [planarMacroScale, Int.add_emod,
      Int.mul_emod] using positionResidues.1
  · rw [firstYEq, secondYEq] at positionResidues
    simpa [planarMacroScale, Int.add_emod,
      Int.mul_emod] using positionResidues.2

theorem carrier_noncarrier_localOffset_emod_ne :
    ∀ carrierOffset ∈ carrierClauseLocalPositions,
      ∀ noncarrierOffset ∈ noncarrierClauseLocalPositions,
        ¬(carrierOffset.1 % planarMacroScale =
              noncarrierOffset.1 % planarMacroScale ∧
            carrierOffset.2 % planarMacroScale =
              noncarrierOffset.2 % planarMacroScale) := by
  native_decide

theorem carrier_clauseResidue_ne_noncarrier_clauseResidue
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (carrierMetadata otherMetadata :
      DrawingPlanarSATClauseMetadata Variable)
    (carrierValid : carrierMetadata.RetainedValid formula)
    (otherValid : otherMetadata.RetainedValid formula)
    {link : EqualityLink CarrierNode}
    {localClauseIndex : Nat}
    (carrierSource :
      carrierMetadata.source =
        .carrier link localClauseIndex)
    (otherNotCarrier :
      ¬∃ otherLink,
        otherMetadata.source.component = .carrier otherLink) :
    clauseResidue formula carrierMetadata.clause ≠
      clauseResidue formula otherMetadata.clause := by
  intro residueEq
  have carrierValid' := carrierValid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at carrierValid'
  rw [carrierSource] at carrierValid'
  rcases carrierClause_exists_localOffset_mem
      wellFormed degree isLocal carrierValid'.1 carrierValid'.2 with
    ⟨carrierOffset, carrierPositionEq, carrierOffsetMem⟩
  rcases
      otherMetadata.source.component.exists_macrocellCenter_of_not_carrier
        formula otherNotCarrier with
    ⟨otherCenter, otherCenterEq⟩
  rcases noncarrierClause_exists_localOffset_mem
      otherMetadata otherValid otherNotCarrier
      otherCenter otherCenterEq with
    ⟨otherOffset, otherPositionEq, otherOffsetMem⟩
  rcases clausePosition_eq_translate_of_residue_eq
      formula residueEq with
    ⟨shift, positionEq⟩
  have offsetResidueEq :=
    localOffset_emod_eq_of_position_eq_translate
      formula carrierPositionEq otherPositionEq positionEq
  exact
    carrier_noncarrier_localOffset_emod_ne
      carrierOffset carrierOffsetMem otherOffset otherOffsetMem
      offsetResidueEq

theorem metadataGaugedNormalizedClause_eq_of_residue_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (firstNonempty : first.clause.literals ≠ [])
    (secondNonempty : second.clause.literals ≠ [])
    (residueEq :
      clauseResidue formula first.clause =
        clauseResidue formula second.clause) :
    metadataGaugedNormalizedClause formula first =
      metadataGaugedNormalizedClause formula second := by
  by_cases firstCarrier :
      ∃ link, first.source.component = .carrier link
  · rcases firstCarrier with ⟨firstLink, firstComponentEq⟩
    rcases first.source.exists_eq_carrier_of_component_eq
        firstLink firstComponentEq with
      ⟨firstIndex, firstSourceEq⟩
    by_cases secondCarrier :
        ∃ link, second.source.component = .carrier link
    · rcases secondCarrier with ⟨secondLink, secondComponentEq⟩
      rcases second.source.exists_eq_carrier_of_component_eq
          secondLink secondComponentEq with
        ⟨secondIndex, secondSourceEq⟩
      exact
        carrier_metadataGaugedNormalizedClause_eq_of_residue_eq
          wellFormed degree isLocal first second
          firstValid secondValid firstSourceEq secondSourceEq residueEq
    · exact False.elim
        ((carrier_clauseResidue_ne_noncarrier_clauseResidue
          wellFormed degree isLocal first second
          firstValid secondValid firstSourceEq secondCarrier) residueEq)
  · by_cases secondCarrier :
      ∃ link, second.source.component = .carrier link
    · rcases secondCarrier with ⟨secondLink, secondComponentEq⟩
      rcases second.source.exists_eq_carrier_of_component_eq
          secondLink secondComponentEq with
        ⟨secondIndex, secondSourceEq⟩
      exact False.elim
        ((carrier_clauseResidue_ne_noncarrier_clauseResidue
          wellFormed degree isLocal second first
          secondValid firstValid secondSourceEq firstCarrier)
            residueEq.symm)
    · exact
        noncarrier_metadataGaugedNormalizedClause_eq_of_residue_eq
          wellFormed degree isLocal first second
          firstValid secondValid firstCarrier secondCarrier
          firstNonempty secondNonempty residueEq

end LeanTrominoes.PeriodicOrthocrossing
