/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits

/-!
# Carrier geometry under clause-anchor normalization

The quotient drawing represents every retained local clause after subtracting
the lattice anchor of its canonically gauged clause.  For a carrier clause,
this translation leaves the first carrier node on a neighboring occurrence
of its supporting drawing segment.  This is the geometric part of aligning a
carrier occurrence with another periodic representative; selected carrier
links themselves still obey their separate zero-owner convention.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- The closed-segment version of `between_shift_is_neighbor`: a translated
expanded-square segment meeting the canonical interval, possibly at an
endpoint, still uses a neighboring lattice shift. -/
theorem between_closed_shift_is_neighbor
    {period first last shift point : Int}
    (periodPositive : 0 < period)
    (firstLower : -period < first)
    (firstUpper : first < 2 * period)
    (lastLower : -period < last)
    (lastUpper : last < 2 * period)
    (pointLower : 0 ≤ point)
    (pointUpper : point < period)
    (between :
      GridSegment.Between
        (first + period * shift)
        (last + period * shift) point) :
    shift = -1 ∨ shift = 0 ∨ shift = 1 := by
  have notTooLow : ¬shift ≤ -2 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper : period * shift ≤ -2 * period := by
      nlinarith
    unfold GridSegment.Between at between
    rcases between with between | between <;>
      omega
  have notTooHigh : ¬2 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower : 2 * period ≤ period * shift := by
      nlinarith
    unfold GridSegment.Between at between
    rcases between with between | between <;>
      omega
  omega

/-- An occurrence whose closed segment meets the canonical drawing square
uses one of the nine neighboring lattice translations. -/
theorem drawing_occurrence_translate_isNeighbor_of_contains
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    {translate point : Cell}
    (pointFundamental : InFundamentalDrawingSquare graph point)
    (contains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation translate)).Contains point) :
    IsNeighborTranslation translate := by
  have endpointBounds :=
    drawing_indexedSegment_endpoints_inExpandedDrawingSquare
      wellFormed degree isLocal indexedMem
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  rcases endpointBounds with ⟨startBounds, finishBounds⟩
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases pointFundamental with
    ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
  rcases contains with
      ⟨horizontal, pointYEq, pointXBetween⟩ |
      ⟨vertical, pointXEq, pointYBetween⟩
  · have pointYEq' :
        point.2 =
          indexed.segment.start.2 +
            drawingGridSize graph * translate.2 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointYEq
    have pointXBetween' :
        GridSegment.Between
          (indexed.segment.start.1 +
            drawingGridSize graph * translate.1)
          (indexed.segment.finish.1 +
            drawingGridSize graph * translate.1)
          point.1 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointXBetween
    exact
      ⟨between_closed_shift_is_neighbor
          periodPositive startXLower startXUpper
          finishXLower finishXUpper pointXLower pointXUpper
          pointXBetween',
        lane_shift_is_neighbor
          periodPositive startYLower startYUpper
          pointYLower pointYUpper pointYEq'⟩
  · have pointXEq' :
        point.1 =
          indexed.segment.start.1 +
            drawingGridSize graph * translate.1 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointXEq
    have pointYBetween' :
        GridSegment.Between
          (indexed.segment.start.2 +
            drawingGridSize graph * translate.2)
          (indexed.segment.finish.2 +
            drawingGridSize graph * translate.2)
          point.2 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointYBetween
    exact
      ⟨lane_shift_is_neighbor
          periodPositive startXLower startXUpper
          pointXLower pointXUpper pointXEq',
        between_closed_shift_is_neighbor
          periodPositive startYLower startYUpper
          finishYLower finishYUpper pointYLower pointYUpper
          pointYBetween'⟩

/-- The gauged source-clause anchor is exactly the coordinatewise period
quotient of the finite clause position. -/
theorem DrawingPlanarSATClauseMetadata.sourceClauseAnchor_eq_position_ediv
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ []) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals =
      (metadata.clause.position.1 /
          (drawingPeriodicPlanarSATPlacement formula).period,
        metadata.clause.position.2 /
          (drawingPeriodicPlanarSATPlacement formula).period) := by
  let period :=
    (drawingPeriodicPlanarSATPlacement formula).period
  let anchor :=
    PeriodicCNF.clauseAnchor
      (metadataGaugedPositionedClause formula metadata).literals
  have canonical :=
    metadata_canonicalClausePosition_eq_residue
      wellFormed degree isLocal metadata valid nonempty
  change
    Cell.sub metadata.clause.position
        (Cell.scale period anchor) =
      clauseResidue formula metadata.clause
    at canonical
  have periodPositive : 0 < period := by
    simpa only [period] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have periodPositiveInt : (0 : Int) < period := by
    exact_mod_cast periodPositive
  have horizontal :=
    congrArg Prod.fst canonical
  have vertical :=
    congrArg Prod.snd canonical
  simp only [Cell.sub, Cell.scale, clauseResidue] at horizontal vertical
  change
    metadata.clause.position.1 - (period : Int) * anchor.1 =
      metadata.clause.position.1 % (period : Int)
    at horizontal
  change
    metadata.clause.position.2 - (period : Int) * anchor.2 =
      metadata.clause.position.2 % (period : Int)
    at vertical
  apply Prod.ext
  · change anchor.1 = metadata.clause.position.1 / period
    have decomposition :=
      Int.emod_add_mul_ediv metadata.clause.position.1 period
    have multiplied :
        period * anchor.1 =
          period * (metadata.clause.position.1 / period) := by
      linear_combination - decomposition - horizontal
    exact mul_left_cancel₀ (ne_of_gt periodPositiveInt) multiplied
  · change anchor.2 = metadata.clause.position.2 / period
    have decomposition :=
      Int.emod_add_mul_ediv metadata.clause.position.2 period
    have multiplied :
        period * anchor.2 =
          period * (metadata.clause.position.2 / period) := by
      linear_combination - decomposition - vertical
    exact mul_left_cancel₀ (ne_of_gt periodPositiveInt) multiplied

/-- For a retained carrier clause, the source-clause anchor is equivalently
the coordinatewise period quotient of the first carrier-node position. -/
theorem
    DrawingPlanarSATClauseMetadata.carrier_sourceClauseAnchor_eq_firstPosition_ediv
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .carrier link localClauseIndex) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals =
      ((link.first.position formula.incidenceGraph).1 /
          (drawingPeriodicPlanarSATPlacement formula).period,
        (link.first.position formula.incidenceGraph).2 /
          (drawingPeriodicPlanarSATPlacement formula).period) := by
  have validData :=
    (metadata.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp valid
  have clauseMember :
      (metadata.clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link).zipIdx := by
    have localMember := validData.2
    rw [sourceEq] at localMember
    simpa [DrawingPlanarSATClauseSource.localClauseIndex,
      DrawingPlanarSATClauseSource.clauseFormula] using localMember
  have linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph := by
    have sourceMember := validData.1
    rw [sourceEq] at sourceMember
    exact sourceMember
  cases literalsEq : metadata.clause.literals with
  | nil =>
      exact False.elim (nonempty literalsEq)
  | cons first rest =>
      have firstLiteralEq :
          first.1 = .inl (.carrier link.first) := by
        simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
          EmbeddedClause.rename, EmbeddedClause.map] at clauseMember
        rcases clauseMember with
            ⟨clauseEq, _⟩ | ⟨clauseEq, _⟩ <;>
          rw [clauseEq] at literalsEq <;>
          simp at literalsEq
        all_goals exact (congrArg Prod.fst literalsEq.1).symm
      have quotients :=
        carrier_clause_first_quotient
          wellFormed degree isLocal linkMember
          clauseMember first rest literalsEq
      rw [firstLiteralEq] at quotients
      change
        metadata.clause.position.1 /
              (drawingPeriodicPlanarSATPlacement formula).period =
            (link.first.position formula.incidenceGraph).1 /
              (drawingPeriodicPlanarSATPlacement formula).period ∧
          metadata.clause.position.2 /
              (drawingPeriodicPlanarSATPlacement formula).period =
            (link.first.position formula.incidenceGraph).2 /
              (drawingPeriodicPlanarSATPlacement formula).period
        at quotients
      rw [metadata.sourceClauseAnchor_eq_position_ediv
        wellFormed degree isLocal valid nonempty]
      exact Prod.ext quotients.1 quotients.2

/-- Subtracting a retained carrier clause's gauged anchor puts the first
carrier-node drawing point in the half-open fundamental drawing square. -/
theorem
    DrawingPlanarSATClauseMetadata.carrier_firstDrawingPoint_anchorNormalize_inFundamental
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .carrier link localClauseIndex) :
    InFundamentalDrawingSquare formula.incidenceGraph
      (Cell.sub
        (link.first.drawingPoint formula.incidenceGraph)
        ((drawing formula.incidenceGraph).periodTranslation
          (PeriodicCNF.clauseAnchor
            (metadataGaugedPositionedClause
              formula metadata).literals))) := by
  let graph := formula.incidenceGraph
  let drawingPeriod : Int := drawingGridSize graph
  let macroPeriod : Nat :=
    (drawingPeriodicPlanarSATPlacement formula).period
  let anchor :=
    PeriodicCNF.clauseAnchor
      (metadataGaugedPositionedClause formula metadata).literals
  have validData :=
    (metadata.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp valid
  have linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks graph := by
    have sourceMember := validData.1
    rw [sourceEq] at sourceMember
    exact sourceMember
  have anchorEq :=
    metadata.carrier_sourceClauseAnchor_eq_firstPosition_ediv
      wellFormed degree isLocal valid nonempty
      link localClauseIndex sourceEq
  change
    anchor =
      ((link.first.position graph).1 / macroPeriod,
        (link.first.position graph).2 / macroPeriod)
    at anchorEq
  have localPosition :=
    retainedDrawingCompleteCarrierLink_first_localPosition
      wellFormed degree isLocal linkMember
  have localBounds :
      0 ≤ link.first.localPosition.1 ∧
        link.first.localPosition.1 < planarMacroScale ∧
        0 ≤ link.first.localPosition.2 ∧
        link.first.localPosition.2 < planarMacroScale := by
    by_cases horizontal : link.first.isHorizontal = true
    · rw [if_pos horizontal] at localPosition
      rw [localPosition]
      norm_num [planarMacroScale]
    · rw [if_neg horizontal] at localPosition
      rw [localPosition]
      norm_num [planarMacroScale]
  have positionEq :=
    CarrierNode.position_eq_scale_add_local graph link.first
  have macroPeriodEq :
      (macroPeriod : Int) =
        planarMacroScale * drawingPeriod := by
    norm_num [macroPeriod, drawingPeriod, graph,
      drawingPeriodicPlanarSATPlacement,
      planarMacroScale]
  have drawingPeriodPositive : 0 < drawingPeriod := by
    dsimp [drawingPeriod]
    exact_mod_cast drawingGridSize_pos graph
  have macroPeriodPositive : (0 : Int) < macroPeriod := by
    rw [macroPeriodEq]
    norm_num [planarMacroScale]
    exact drawingPeriodPositive
  have horizontalDecomposition :=
    Int.emod_add_mul_ediv
      (link.first.position graph).1 (macroPeriod : Int)
  have verticalDecomposition :=
    Int.emod_add_mul_ediv
      (link.first.position graph).2 (macroPeriod : Int)
  have horizontalRemainderNonnegative :
      0 ≤ (link.first.position graph).1 % (macroPeriod : Int) :=
    Int.emod_nonneg _ (ne_of_gt macroPeriodPositive)
  have horizontalRemainderLt :
      (link.first.position graph).1 % (macroPeriod : Int) <
        macroPeriod :=
    Int.emod_lt_of_pos _ macroPeriodPositive
  have verticalRemainderNonnegative :
      0 ≤ (link.first.position graph).2 % (macroPeriod : Int) :=
    Int.emod_nonneg _ (ne_of_gt macroPeriodPositive)
  have verticalRemainderLt :
      (link.first.position graph).2 % (macroPeriod : Int) <
        macroPeriod :=
    Int.emod_lt_of_pos _ macroPeriodPositive
  have normalizedHorizontal :
      planarMacroScale *
            ((link.first.drawingPoint graph).1 -
              drawingPeriod * anchor.1) +
          link.first.localPosition.1 =
        (link.first.position graph).1 % (macroPeriod : Int) := by
    rw [macroPeriodEq]
    have positionHorizontal := congrArg Prod.fst positionEq
    simp only [Cell.add, Cell.scale] at positionHorizontal
    have decomposition := horizontalDecomposition
    have anchorHorizontal :=
      congrArg Prod.fst anchorEq
    simp only at anchorHorizontal
    rw [← anchorHorizontal, macroPeriodEq] at decomposition
    norm_num [planarMacroScale] at positionHorizontal decomposition ⊢
    calc
      planarMacroScale *
              ((link.first.drawingPoint graph).1 -
                drawingPeriod * anchor.1) +
            link.first.localPosition.1 =
          (planarMacroScale *
              (link.first.drawingPoint graph).1 +
            link.first.localPosition.1) -
              planarMacroScale * drawingPeriod * anchor.1 := by ring
      _ =
          (link.first.position graph).1 -
            planarMacroScale * drawingPeriod * anchor.1 := by
              rw [positionHorizontal]
              norm_num [planarMacroScale]
      _ =
          (link.first.position graph).1 %
            (planarMacroScale * drawingPeriod) := by
              norm_num [planarMacroScale] at decomposition ⊢
              omega
  have normalizedVertical :
      planarMacroScale *
            ((link.first.drawingPoint graph).2 -
              drawingPeriod * anchor.2) +
          link.first.localPosition.2 =
        (link.first.position graph).2 % (macroPeriod : Int) := by
    rw [macroPeriodEq]
    have positionVertical := congrArg Prod.snd positionEq
    simp only [Cell.add, Cell.scale] at positionVertical
    have decomposition := verticalDecomposition
    have anchorVertical :=
      congrArg Prod.snd anchorEq
    simp only at anchorVertical
    rw [← anchorVertical, macroPeriodEq] at decomposition
    norm_num [planarMacroScale] at positionVertical decomposition ⊢
    calc
      planarMacroScale *
              ((link.first.drawingPoint graph).2 -
                drawingPeriod * anchor.2) +
            link.first.localPosition.2 =
          (planarMacroScale *
              (link.first.drawingPoint graph).2 +
            link.first.localPosition.2) -
              planarMacroScale * drawingPeriod * anchor.2 := by ring
      _ =
          (link.first.position graph).2 -
            planarMacroScale * drawingPeriod * anchor.2 := by
              rw [positionVertical]
              norm_num [planarMacroScale]
      _ =
          (link.first.position graph).2 %
            (planarMacroScale * drawingPeriod) := by
              norm_num [planarMacroScale] at decomposition ⊢
              omega
  rw [macroPeriodEq] at horizontalRemainderNonnegative horizontalRemainderLt verticalRemainderNonnegative verticalRemainderLt
  rw [macroPeriodEq] at normalizedHorizontal normalizedVertical
  norm_num [planarMacroScale] at localBounds normalizedHorizontal normalizedVertical
  norm_num [planarMacroScale] at horizontalRemainderNonnegative horizontalRemainderLt verticalRemainderNonnegative verticalRemainderLt
  generalize horizontalRemainderEq :
      (link.first.position graph).1 %
          (20 * drawingPeriod) =
        horizontalRemainder
    at normalizedHorizontal horizontalRemainderNonnegative
      horizontalRemainderLt
  generalize verticalRemainderEq :
      (link.first.position graph).2 %
          (20 * drawingPeriod) =
        verticalRemainder
    at normalizedVertical verticalRemainderNonnegative
      verticalRemainderLt
  have horizontalBounds :
      0 ≤
          (link.first.drawingPoint graph).1 -
            drawingPeriod * anchor.1 ∧
        (link.first.drawingPoint graph).1 -
            drawingPeriod * anchor.1 <
          drawingPeriod := by
    omega
  have verticalBounds :
      0 ≤
          (link.first.drawingPoint graph).2 -
            drawingPeriod * anchor.2 ∧
        (link.first.drawingPoint graph).2 -
            drawingPeriod * anchor.2 <
          drawingPeriod := by
    omega
  exact
    ⟨horizontalBounds.1, horizontalBounds.2,
      verticalBounds.1, verticalBounds.2⟩

/-- Translating both a closed segment occurrence and a contained point by
the negative of a drawing-period translation preserves containment. -/
theorem segment_periodTranslate_sub_contains
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (segment : GridSegment)
    (sourceShift anchor point : Cell)
    (contains :
      (segment.translate
        ((drawing graph).periodTranslation sourceShift)).Contains point) :
    (segment.translate
        ((drawing graph).periodTranslation
          (Cell.sub sourceShift anchor))).Contains
      (Cell.sub point
        ((drawing graph).periodTranslation anchor)) := by
  simpa [PeriodicGridDrawing.normalizePoint] using
    ((PeriodicGridDrawing.contains_normalize
      (drawing graph) segment sourceShift anchor point).mp contains)

/-- Subtracting a retained carrier clause's source anchor leaves the first
carrier node on one of the nine retained occurrences of its supporting
drawing segment. -/
theorem
    DrawingPlanarSATClauseMetadata.carrier_first_anchorNormalize_translate_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .carrier link localClauseIndex) :
    IsNeighborTranslation
      ((link.first.periodTranslate formula.incidenceGraph
        (Cell.neg
          (PeriodicCNF.clauseAnchor
            (metadataGaugedPositionedClause
              formula metadata).literals))).translate) := by
  let graph := formula.incidenceGraph
  let anchor :=
    PeriodicCNF.clauseAnchor
      (metadataGaugedPositionedClause formula metadata).literals
  have validData :=
    (metadata.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp valid
  have linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks graph := by
    have sourceMember := validData.1
    rw [sourceEq] at sourceMember
    exact sourceMember
  have firstMember :=
    (retainedDrawingCompleteCarrierLink_endpoints_mem
      graph linkMember).1
  have indexedMember :=
    retainedCarrierNode_indexed_mem graph firstMember
  have axisAligned :
      link.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      link.first.indexed indexedMember
  have sourceContains :=
    retainedCarrierNode_drawingPoint_contains
      graph firstMember axisAligned
  have targetContains :
      (link.first.indexed.segment.translate
          ((drawing graph).periodTranslation
            (Cell.sub link.first.translate anchor))).Contains
        (Cell.sub
          (link.first.drawingPoint graph)
          ((drawing graph).periodTranslation anchor)) := by
    exact segment_periodTranslate_sub_contains
      graph link.first.indexed.segment link.first.translate
      anchor (link.first.drawingPoint graph) sourceContains
  have targetNeighbor :=
    drawing_occurrence_translate_isNeighbor_of_contains
      wellFormed degree isLocal indexedMember
      (metadata.carrier_firstDrawingPoint_anchorNormalize_inFundamental
        wellFormed degree isLocal valid nonempty
        link localClauseIndex sourceEq)
      targetContains
  have translateEq :
      Cell.add link.first.translate (Cell.neg anchor) =
        Cell.sub link.first.translate anchor := by
    rcases link.first.translate with ⟨translateX, translateY⟩
    rcases anchor with ⟨anchorX, anchorY⟩
    simp only [Cell.neg, Cell.add, Cell.sub, Prod.mk.injEq]
    constructor <;> ring
  rw [CarrierNode.translate_periodTranslate, translateEq]
  exact targetNeighbor

/-- Anchor normalization preserves the complete carrier link in the raw
retained window.  No representative claim is made here: the selected carrier
list separately keeps only the link whose ownership shift is zero. -/
theorem
    DrawingPlanarSATClauseMetadata.carrier_anchorNormalize_mem_raw
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .carrier link localClauseIndex) :
    carrierLinkPeriodTranslate formula.incidenceGraph link
        (Cell.neg
          (PeriodicCNF.clauseAnchor
            (metadataGaugedPositionedClause
              formula metadata).literals)) ∈
      retainedDrawingCompleteCarrierLinksRaw
        formula.incidenceGraph := by
  have validData :=
    (metadata.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp valid
  have linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph := by
    have sourceMember := validData.1
    rw [sourceEq] at sourceMember
    exact sourceMember
  apply retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
    wellFormed degree isLocal
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      formula.incidenceGraph link).mp linkMember).1
  · exact retainedDrawingCompleteCarrierLink_first_translate_neighbor
      formula.incidenceGraph linkMember
  · exact
      metadata.carrier_first_anchorNormalize_translate_neighbor
        wellFormed degree isLocal valid nonempty
        link localClauseIndex sourceEq

/-- Negation of a lattice cell is zero exactly when the cell is zero. -/
@[simp]
theorem Cell.neg_eq_zero_iff (cell : Cell) :
    Cell.neg cell = (0, 0) ↔ cell = (0, 0) := by
  rcases cell with ⟨horizontal, vertical⟩
  simp only [Cell.neg, Cell.sub, Prod.mk.injEq]
  constructor
  · rintro ⟨horizontalEq, verticalEq⟩
    constructor <;> omega
  · rintro ⟨horizontalEq, verticalEq⟩
    subst horizontal
    subst vertical
    norm_num

/-- The representative-owner shift of an anchor-normalized selected carrier
link is the negative of the clause anchor. -/
theorem
    DrawingPlanarSATClauseMetadata.carrier_anchorNormalize_representativeShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .carrier link localClauseIndex) :
    carrierLinkRepresentativeShift formula.incidenceGraph
        (carrierLinkPeriodTranslate formula.incidenceGraph link
          (Cell.neg
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause
                formula metadata).literals))) =
      Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula metadata).literals) := by
  have validData :=
    (metadata.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp valid
  have linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph := by
    have sourceMember := validData.1
    rw [sourceEq] at sourceMember
    exact sourceMember
  have representative :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      formula.incidenceGraph link).mp linkMember).2
  change
    carrierLinkRepresentativeShift formula.incidenceGraph link =
      (0, 0)
    at representative
  rw [carrierLinkRepresentativeShift_periodTranslate]
  rw [representative]
  rcases
      PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals with
    ⟨anchorX, anchorY⟩
  simp [Cell.add]

/-- Anchor normalization remains in the selected carrier family exactly in
the zero-anchor case.  For a nonzero anchor it remains geometrically present
in the raw retained window but is not the unique zero-owner representative. -/
theorem
    DrawingPlanarSATClauseMetadata.carrier_anchorNormalize_mem_iff_anchor_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .carrier link localClauseIndex) :
    carrierLinkPeriodTranslate formula.incidenceGraph link
          (Cell.neg
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause
                formula metadata).literals)) ∈
        retainedDrawingCompleteCarrierLinks formula.incidenceGraph ↔
      PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals =
        (0, 0) := by
  rw [mem_retainedDrawingCompleteCarrierLinks_iff]
  have rawMember :=
    metadata.carrier_anchorNormalize_mem_raw
      wellFormed degree isLocal valid nonempty
      link localClauseIndex sourceEq
  rw [and_iff_right rawMember]
  unfold CarrierLinkIsRepresentative
  rw [
    metadata.carrier_anchorNormalize_representativeShift
      valid link localClauseIndex sourceEq,
    Cell.neg_eq_zero_iff]

end PeriodicOrthocrossing
end LeanTrominoes
