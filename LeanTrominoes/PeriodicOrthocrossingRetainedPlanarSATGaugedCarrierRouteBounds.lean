import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierRouteBounds
import LeanTrominoes.PeriodicOrthocrossingTranslationDegree

/-!
# Expanded-square bounds for normalized carrier routes

Every retained equality lens stays inside the narrow corridor between two
consecutive carrier nodes.  The axial separation of those nodes is strictly
less than one physical planar-SAT period because their supporting drawing
segment has span at most one underlying drawing period.  Transversely, the
lens extends only two cells below and one cell above its carrier.

Clause-anchor normalization subtracts the period quotient shared by a
carrier clause and the first carrier node.  The axial one-period span and
the fixed transverse width then place every normalized lens route point in
the open neighboring-period square `(-P, 2P)²`.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Consecutive selected carrier-node positions are strictly less than one
physical planar-SAT period apart along their carrier axis. -/
theorem retainedDrawingCompleteCarrierLink_position_span_lt_period
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    if link.first.isHorizontal then
      (link.second.position graph).1 -
          (link.first.position graph).1 <
        planarMacroScale * drawingGridSize graph
    else
      (link.second.position graph).2 -
          (link.first.position graph).2 <
        planarMacroScale * drawingGridSize graph := by
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMem
  have indexedMem :=
    retainedCarrierNode_indexed_mem graph endpoints.1
  have aligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      link.first.indexed indexedMem
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal]
    have horizontalSegment :
        link.first.indexed.segment.IsHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph endpoints.1 aligned).mp horizontal
    have span :=
      drawing_indexedSegment_horizontal_span_le_period
        wellFormed degree isLocal indexedMem horizontalSegment
    have supportBounds :=
      retainedDrawingCompleteCarrierLink_horizontal_support_bounded
        wellFormed degree isLocal linkMem horizontal
    have translatedSpan :
        max (link.first.supportingSegment graph).start.1
              (link.first.supportingSegment graph).finish.1 -
            min (link.first.supportingSegment graph).start.1
              (link.first.supportingSegment graph).finish.1 ≤
          drawingGridSize graph := by
      rcases le_total
          link.first.indexed.segment.start.1
          link.first.indexed.segment.finish.1 with forward | backward
      · have difference :=
          span.1
        simp only [CarrierNode.supportingSegment,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, Cell.add, Cell.scale]
        rw [min_eq_left (by omega), max_eq_right (by omega)]
        omega
      · have difference :=
          span.2
        simp only [CarrierNode.supportingSegment,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, Cell.add, Cell.scale]
        rw [min_eq_right (by omega), max_eq_left (by omega)]
        omega
    norm_num [planarMacroScale] at supportBounds ⊢
    omega
  · rw [if_neg horizontal]
    have verticalSegment :
        link.first.indexed.segment.IsVertical :=
      aligned.resolve_left fun horizontalSegment =>
        horizontal
          ((retainedCarrierNode_isHorizontal_iff
            graph endpoints.1 aligned).mpr horizontalSegment)
    have span :=
      drawing_indexedSegment_vertical_span_le_period
        isLocal indexedMem verticalSegment
    have supportBounds :=
      retainedDrawingCompleteCarrierLink_vertical_support_bounded
        wellFormed degree isLocal linkMem horizontal
    have translatedSpan :
        max (link.first.supportingSegment graph).start.2
              (link.first.supportingSegment graph).finish.2 -
            min (link.first.supportingSegment graph).start.2
              (link.first.supportingSegment graph).finish.2 ≤
          drawingGridSize graph := by
      rcases le_total
          link.first.indexed.segment.start.2
          link.first.indexed.segment.finish.2 with forward | backward
      · have difference :=
          span.1
        simp only [CarrierNode.supportingSegment,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, Cell.add, Cell.scale]
        rw [min_eq_left (by omega), max_eq_right (by omega)]
        omega
      · have difference :=
          span.2
        simp only [CarrierNode.supportingSegment,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, Cell.add, Cell.scale]
        rw [min_eq_right (by omega), max_eq_left (by omega)]
        omega
    norm_num [planarMacroScale] at supportBounds ⊢
    omega

/-- Subtracting a clause's canonical period translation from another point
is its displacement from a quotient-aligned reference plus that reference's
period residue. -/
theorem normalizeCoordinate_eq_sub_add_emod_of_canonical_quotient
    {period clause first point translation : Int}
    (canonical :
      clause - translation = clause % period)
    (quotient : clause / period = first / period) :
    point - translation =
      point - first + first % period := by
  have clauseDivision :=
    Int.emod_add_mul_ediv clause period
  have firstDivision :=
    Int.emod_add_mul_ediv first period
  have quotientMul :=
    congrArg (fun value => period * value) quotient
  omega

/-- Every point of an explicitly selected retained carrier lens lies in the
expanded square after normalization by one of its clauses. -/
theorem carrier_normalizedRoutePoint_inExpanded
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {link : EqualityLink CarrierNode}
    {localClauseIndex : Nat}
    (valid :
      (⟨clause, .carrier link localClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (nonempty : clause.literals ≠ [])
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).routes localClauseIndex literalIndex) :
    let normalized :=
      Cell.sub point
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation
          (PeriodicCNF.clauseAnchor
            ((wrapPeriodicPlanarSATClause
              (periodicizePlanarSATClause formula
                clause)).variableGauge
                  (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                    formula))))
    let period : Int :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).period
    (-period < normalized.1) ∧ normalized.1 < 2 * period ∧
      -period < normalized.2 ∧ normalized.2 < 2 * period := by
  change
    link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula) ∧
      (clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link).zipIdx at valid
  have localClauseMember :
      (clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
        wellFormed degree isLocal valid.1]
    exact valid.2
  have pointBounds :=
    (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
      wellFormed degree isLocal valid.1).of_members
        localClauseMember literalMember pointMember
  have span :=
    retainedDrawingCompleteCarrierLink_position_span_lt_period
      wellFormed degree isLocal valid.1
  cases literalsEq : clause.literals with
  | nil =>
      exact (nonempty literalsEq).elim
  | cons first rest =>
      have quotients :=
        carrier_clause_first_quotient
          wellFormed degree isLocal valid.1 valid.2
          first rest literalsEq
      have firstLiteralEq :
          first.1 = .inl (.carrier link.first) := by
        simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
          EmbeddedClause.rename, EmbeddedClause.map] at valid
        rcases valid.2 with ⟨clauseEq, _⟩ | ⟨clauseEq, _⟩ <;>
          rw [clauseEq] at literalsEq <;>
          simp at literalsEq
        all_goals exact (congrArg Prod.fst literalsEq.1).symm
      rw [firstLiteralEq] at quotients
      change
        clause.position.1 /
              (planarMacroScale *
                drawingGridSize
                  (PeriodicCNF.incidenceGraph formula)) =
            (link.first.position
              (PeriodicCNF.incidenceGraph formula)).1 /
              (planarMacroScale *
                drawingGridSize
                  (PeriodicCNF.incidenceGraph formula)) ∧
          clause.position.2 /
              (planarMacroScale *
                drawingGridSize
                  (PeriodicCNF.incidenceGraph formula)) =
            (link.first.position
              (PeriodicCNF.incidenceGraph formula)).2 /
              (planarMacroScale *
                drawingGridSize
                  (PeriodicCNF.incidenceGraph formula)) at quotients
      have canonical :=
        metadata_canonicalClausePosition_eq_residue
          wellFormed degree isLocal
          (⟨clause, .carrier link localClauseIndex⟩ :
            DrawingPlanarSATClauseMetadata Variable)
          valid nonempty
      change
        Cell.sub clause.position
            ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              formula).translation
              (PeriodicCNF.clauseAnchor
                ((wrapPeriodicPlanarSATClause
                  (periodicizePlanarSATClause formula
                    clause)).variableGauge
                      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                        formula)))) =
          (clause.position.1 %
              (planarMacroScale *
                drawingGridSize
                  (PeriodicCNF.incidenceGraph formula)),
            clause.position.2 %
              (planarMacroScale *
                drawingGridSize
                  (PeriodicCNF.incidenceGraph formula))) at canonical
      let translation :=
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation
          (PeriodicCNF.clauseAnchor
            ((wrapPeriodicPlanarSATClause
              (periodicizePlanarSATClause formula
                clause)).variableGauge
                  (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                    formula)))
      let period : Int :=
        planarMacroScale *
          drawingGridSize (PeriodicCNF.incidenceGraph formula)
      have normalizedX :
          point.1 - translation.1 =
            point.1 -
                (link.first.position
                  (PeriodicCNF.incidenceGraph formula)).1 +
              (link.first.position
                (PeriodicCNF.incidenceGraph formula)).1 % period := by
        apply normalizeCoordinate_eq_sub_add_emod_of_canonical_quotient
        · simpa [translation, period, Cell.sub] using
            congrArg Prod.fst canonical
        · simpa [period] using quotients.1
      have normalizedY :
          point.2 - translation.2 =
            point.2 -
                (link.first.position
                  (PeriodicCNF.incidenceGraph formula)).2 +
              (link.first.position
                (PeriodicCNF.incidenceGraph formula)).2 % period := by
        apply normalizeCoordinate_eq_sub_add_emod_of_canonical_quotient
        · simpa [translation, period, Cell.sub] using
            congrArg Prod.snd canonical
        · simpa [period] using quotients.2
      have periodPositive : 2 < period := by
        dsimp [period]
        have sizePositive :
            0 < drawingGridSize
              (PeriodicCNF.incidenceGraph formula) :=
          drawingGridSize_pos _
        norm_num [planarMacroScale] at sizePositive ⊢
        omega
      have firstXModNonnegative :
          0 ≤
            (link.first.position
              (PeriodicCNF.incidenceGraph formula)).1 % period :=
        Int.emod_nonneg _ (ne_of_gt (show 0 < period by omega))
      have firstXModLt :
          (link.first.position
              (PeriodicCNF.incidenceGraph formula)).1 % period <
            period :=
        Int.emod_lt_of_pos _ (show 0 < period by omega)
      have firstYModNonnegative :
          0 ≤
            (link.first.position
              (PeriodicCNF.incidenceGraph formula)).2 % period :=
        Int.emod_nonneg _ (ne_of_gt (show 0 < period by omega))
      have firstYModLt :
          (link.first.position
              (PeriodicCNF.incidenceGraph formula)).2 % period <
            period :=
        Int.emod_lt_of_pos _ (show 0 < period by omega)
      dsimp only
      change
        -period < point.1 - translation.1 ∧
          point.1 - translation.1 < 2 * period ∧
          -period < point.2 - translation.2 ∧
          point.2 - translation.2 < 2 * period
      unfold drawingCompleteCarrierLinkRectangleLower
        drawingCompleteCarrierLinkRectangleUpper
        InClosedGridRectangle at pointBounds
      by_cases horizontal : link.first.isHorizontal = true
      · rw [if_pos horizontal] at pointBounds span
        simp only [horizontal, if_true] at pointBounds
        have span' :
            (link.second.position
                (PeriodicCNF.incidenceGraph formula)).1 -
                (link.first.position
                  (PeriodicCNF.incidenceGraph formula)).1 <
              period := by
          simpa [period] using span
        rw [normalizedX, normalizedY]
        omega
      · rw [if_neg horizontal] at pointBounds span
        have horizontalFalse :
            link.first.isHorizontal = false :=
          Bool.eq_false_of_not_eq_true horizontal
        simp only [horizontalFalse, Bool.false_eq_true, if_false] at pointBounds
        have span' :
            (link.second.position
                (PeriodicCNF.incidenceGraph formula)).2 -
                (link.first.position
                  (PeriodicCNF.incidenceGraph formula)).2 <
              period := by
          simpa [period] using span
        rw [normalizedX, normalizedY]
        omega

/-- Metadata-level carrier route points satisfy the expanded-square bound
used by finite periodic planarity. -/
theorem metadata_normalizedRoutePoint_inExpanded_of_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (link : EqualityLink CarrierNode)
    (componentEq :
      metadata.source.component = .carrier link)
    (nonempty : metadata.clause.literals ≠ [])
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex) :
    let normalized :=
      Cell.sub point
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation
          (PeriodicCNF.clauseAnchor
            ((wrapPeriodicPlanarSATClause
              (periodicizePlanarSATClause formula
                metadata.clause)).variableGauge
                  (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                    formula))))
    let period : Int :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).period
    (-period < normalized.1) ∧ normalized.1 < 2 * period ∧
      -period < normalized.2 ∧ normalized.2 < 2 * period := by
  rcases metadata with ⟨clause, source⟩
  rcases source.exists_eq_carrier_of_component_eq
      link componentEq with
    ⟨localClauseIndex, sourceEq⟩
  subst source
  apply carrier_normalizedRoutePoint_inExpanded
    wellFormed degree isLocal valid nonempty literalMember
  simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex] using pointMember

end LeanTrominoes.PeriodicOrthocrossing
