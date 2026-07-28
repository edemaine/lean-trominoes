import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions

/-!
# Gauged clause positions in the retained periodic planar-SAT drawing

This module identifies the canonical position of every retained clause with
the coordinatewise residue of its finite drawing position.  It proves the
quotient alignment needed for both carrier and macrocell gadgets, establishes
strictly interior clause residues, and transfers those bounds through
clause-orbit deduplication.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

theorem canonicalClausePosition_eq_emod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (first : PlanarSATVariable Variable × Bool)
    (rest : List (PlanarSATVariable Variable × Bool))
    (literalsEq : clause.literals = first :: rest)
    (horizontalQuotient :
      clause.position.1 /
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period =
        (drawingPlanarSATVariablePosition formula first.1).1 /
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period)
    (verticalQuotient :
      clause.position.2 /
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period =
        (drawingPlanarSATVariablePosition formula first.1).2 /
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period) :
    PositionedPeriodicCNF.canonicalClausePosition
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        ⟨clause.position,
          (wrapPeriodicPlanarSATClause
            (periodicizePlanarSATClause formula clause)).variableGauge
              (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                formula)⟩ =
      (clause.position.1 %
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period,
        clause.position.2 %
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period) := by
  have physical :=
    periodicizePlanarSATLiteral_position formula first
  rcases normalizedEq :
      normalizePlanarSATVariable formula first.1 with
    ⟨atom, ⟨offsetX, offsetY⟩⟩
  rcases baseEq :
      drawingPeriodicPlanarSATVariablePosition formula atom with
    ⟨baseX, baseY⟩
  rcases finiteEq :
      drawingPlanarSATVariablePosition formula first.1 with
    ⟨finiteX, finiteY⟩
  simp [periodicizePlanarSATLiteral, normalizedEq] at physical
  have physicalX : baseX +
        (drawingPeriodicPlanarSATPlacement formula).period * offsetX =
      finiteX := by
    have := congrArg Prod.fst physical
    simpa [PeriodicVariablePlacement.literalPosition,
      drawingPeriodicPlanarSATPlacement,
      PeriodicVariablePlacement.translation,
      baseEq, finiteEq, Cell.add, Cell.scale] using this
  have physicalY : baseY +
        (drawingPeriodicPlanarSATPlacement formula).period * offsetY =
      finiteY := by
    have := congrArg Prod.snd physical
    simpa [PeriodicVariablePlacement.literalPosition,
      drawingPeriodicPlanarSATPlacement,
      PeriodicVariablePlacement.translation,
      baseEq, finiteEq, Cell.add, Cell.scale] using this
  have periodNe :
      ((drawingPeriodicPlanarSATPlacement formula).period : Int) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (drawingPeriodicPlanarSATPlacement_period_pos formula)
  have physicalQuotientX :
      finiteX / (drawingPeriodicPlanarSATPlacement formula).period =
        baseX / (drawingPeriodicPlanarSATPlacement formula).period +
          offsetX := by
    rw [← physicalX, Int.add_ediv_of_dvd_right]
    · rw [Int.mul_ediv_cancel_left]
      exact periodNe
    · exact dvd_mul_right _ _
  have physicalQuotientY :
      finiteY / (drawingPeriodicPlanarSATPlacement formula).period =
        baseY / (drawingPeriodicPlanarSATPlacement formula).period +
          offsetY := by
    rw [← physicalY, Int.add_ediv_of_dvd_right]
    · rw [Int.mul_ediv_cancel_left]
      exact periodNe
    · exact dvd_mul_right _ _
  have horizontalQuotient' :
      clause.position.1 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        finiteX /
          (drawingPeriodicPlanarSATPlacement formula).period := by
    simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement, finiteEq] using
        horizontalQuotient
  have verticalQuotient' :
      clause.position.2 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        finiteY /
          (drawingPeriodicPlanarSATPlacement formula).period := by
    simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement, finiteEq] using
        verticalQuotient
  have anchorEq :
      PeriodicCNF.clauseAnchor
          ((wrapPeriodicPlanarSATClause
            (periodicizePlanarSATClause formula clause)).variableGauge
              (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                formula)) =
        (offsetX +
            baseX /
              (drawingPeriodicPlanarSATPlacement formula).period,
          offsetY +
            baseY /
              (drawingPeriodicPlanarSATPlacement formula).period) := by
    simp [PeriodicClause.variableGauge,
      wrapPeriodicPlanarSATClause,
      periodicizePlanarSATClause, literalsEq,
      PeriodicCNF.clauseAnchor,
      wrapPeriodicPlanarSATLiteral,
      periodicizePlanarSATLiteral,
      normalizedEq, PeriodicLiteral.variableGauge,
      retainedDrawingWrappedPeriodicPlanarSATVariableGauge,
      wrappedDrawingPeriodicPlanarSATPlacement,
      PeriodicVariablePlacement.canonicalPositionGauge,
      drawingPeriodicPlanarSATPlacement, baseEq, Cell.add]
  apply Prod.ext
  · simp only [PositionedPeriodicCNF.canonicalClausePosition,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement,
      PeriodicVariablePlacement.variableGauge,
      drawingPeriodicPlanarSATPlacement,
      PeriodicVariablePlacement.translation,
      Cell.sub, Cell.scale, anchorEq]
    change
      clause.position.1 -
          (drawingPeriodicPlanarSATPlacement formula).period *
            (offsetX +
              baseX /
                (drawingPeriodicPlanarSATPlacement formula).period) =
        clause.position.1 %
          (drawingPeriodicPlanarSATPlacement formula).period
    have division :=
      Int.emod_add_mul_ediv clause.position.1
        (drawingPeriodicPlanarSATPlacement formula).period
    have anchorQuotient :
        offsetX +
            baseX /
              (drawingPeriodicPlanarSATPlacement formula).period =
          clause.position.1 /
            (drawingPeriodicPlanarSATPlacement formula).period := by
      omega
    rw [anchorQuotient]
    omega
  · simp only [PositionedPeriodicCNF.canonicalClausePosition,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement,
      PeriodicVariablePlacement.variableGauge,
      drawingPeriodicPlanarSATPlacement,
      PeriodicVariablePlacement.translation,
      Cell.sub, Cell.scale, anchorEq]
    change
      clause.position.2 -
          (drawingPeriodicPlanarSATPlacement formula).period *
            (offsetY +
              baseY /
                (drawingPeriodicPlanarSATPlacement formula).period) =
        clause.position.2 %
          (drawingPeriodicPlanarSATPlacement formula).period
    have division :=
      Int.emod_add_mul_ediv clause.position.2
        (drawingPeriodicPlanarSATPlacement formula).period
    have anchorQuotient :
        offsetY +
            baseY /
              (drawingPeriodicPlanarSATPlacement formula).period =
          clause.position.2 /
            (drawingPeriodicPlanarSATPlacement formula).period := by
      omega
    rw [anchorQuotient]
    omega

theorem macrocellQuotient_eq
    {center first second : Cell} {periodFactor : Int}
    (firstBounded : InPlanarSATMacrocell center first)
    (secondBounded : InPlanarSATMacrocell center second) :
    first.1 / (planarMacroScale * periodFactor) =
        second.1 / (planarMacroScale * periodFactor) ∧
      first.2 / (planarMacroScale * periodFactor) =
        second.2 / (planarMacroScale * periodFactor) := by
  rcases center with ⟨centerX, centerY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  norm_num [InPlanarSATMacrocell,
    planarSATMacrocellRouteLower,
    planarSATMacrocellRouteUpper,
    InClosedGridRectangle, Cell.scale, Cell.add,
    planarMacroScale] at firstBounded secondBounded ⊢
  have firstXDivision := Int.emod_add_mul_ediv firstX 20
  have firstXModNonnegative : 0 ≤ firstX % 20 :=
    Int.emod_nonneg _ (by norm_num)
  have firstXModSmall : firstX % 20 < 20 :=
    Int.emod_lt_of_pos _ (by norm_num)
  have secondXDivision := Int.emod_add_mul_ediv secondX 20
  have secondXModNonnegative : 0 ≤ secondX % 20 :=
    Int.emod_nonneg _ (by norm_num)
  have secondXModSmall : secondX % 20 < 20 :=
    Int.emod_lt_of_pos _ (by norm_num)
  have firstYDivision := Int.emod_add_mul_ediv firstY 20
  have firstYModNonnegative : 0 ≤ firstY % 20 :=
    Int.emod_nonneg _ (by norm_num)
  have firstYModSmall : firstY % 20 < 20 :=
    Int.emod_lt_of_pos _ (by norm_num)
  have secondYDivision := Int.emod_add_mul_ediv secondY 20
  have secondYModNonnegative : 0 ≤ secondY % 20 :=
    Int.emod_nonneg _ (by norm_num)
  have secondYModSmall : secondY % 20 < 20 :=
    Int.emod_lt_of_pos _ (by norm_num)
  have quotientEq :
      firstX / 20 = centerX ∧ secondX / 20 = centerX ∧
        firstY / 20 = centerY ∧ secondY / 20 = centerY := by
    omega
  constructor
  · rw [Int.ediv_mul, Int.ediv_mul]
    norm_num
    rw [quotientEq.1, quotientEq.2.1]
  · rw [Int.ediv_mul, Int.ediv_mul]
    norm_num
    rw [quotientEq.2.2.1, quotientEq.2.2.2]

theorem add_small_quotient_eq
    {coordinate periodFactor delta : Int}
    (residue : coordinate % 10 = 1)
    (deltaNonnegative : 0 ≤ delta)
    (deltaSmall : delta < 9) :
    (coordinate + delta) / (10 * periodFactor) =
      coordinate / (10 * periodFactor) := by
  rw [Int.ediv_mul, Int.ediv_mul]
  simp only [show ¬(10 : Int) < 0 by norm_num, false_and,
    if_false]
  have addMod : (coordinate + delta) % 10 = 1 + delta := by
    rw [Int.add_emod, residue]
    have deltaMod : delta % 10 = delta :=
      Int.emod_eq_of_lt deltaNonnegative (by omega)
    rw [deltaMod]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have firstDivision :=
    Int.emod_add_mul_ediv coordinate 10
  have secondDivision :=
    Int.emod_add_mul_ediv (coordinate + delta) 10
  have divTen : (coordinate + delta) / 10 =
      coordinate / 10 := by
    omega
  rw [divTen]

theorem carrier_clause_first_quotient
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
          (Variable := Variable) link).zipIdx)
    (first : PlanarSATVariable Variable × Bool)
    (rest : List (PlanarSATVariable Variable × Bool))
    (literalsEq : clause.literals = first :: rest) :
    clause.position.1 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        (drawingPlanarSATVariablePosition formula first.1).1 /
          (drawingPeriodicPlanarSATPlacement formula).period ∧
      clause.position.2 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        (drawingPlanarSATVariablePosition formula first.1).2 /
          (drawingPeriodicPlanarSATPlacement formula).period := by
  have firstLiteralEq :
      first.1 = .inl (.carrier link.first) := by
    simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
      EmbeddedClause.rename, EmbeddedClause.map] at clauseMember
    rcases clauseMember with ⟨clauseEq, _⟩ | ⟨clauseEq, _⟩ <;>
      rw [clauseEq] at literalsEq <;>
      simp at literalsEq
    all_goals exact (congrArg Prod.fst literalsEq.1).symm
  have positionCases :=
    carrierClause_position_eq_forward_or_backward clauseMember
  have geometry :=
    retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem
  have direction :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal linkMem
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      (PeriodicCNF.incidenceGraph formula) linkMem
  have common :=
    retainedDrawingCompleteCarrierLinks_common_key
      (PeriodicCNF.incidenceGraph formula) linkMem
  have axisData :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal endpoints.1 endpoints.2 common
  rw [geometry.positions] at positionCases
  change
    AxisDirection.between
        (link.first.position (PeriodicCNF.incidenceGraph formula))
        (link.second.position (PeriodicCNF.incidenceGraph formula)) =
      (if link.first.isHorizontal then .east else .north)
    at direction
  rw [direction] at positionCases
  rw [firstLiteralEq]
  change
    clause.position.1 /
          (planarMacroScale *
            drawingGridSize (PeriodicCNF.incidenceGraph formula)) =
        (link.first.position
            (PeriodicCNF.incidenceGraph formula)).1 /
          (planarMacroScale *
            drawingGridSize (PeriodicCNF.incidenceGraph formula)) ∧
      clause.position.2 /
          (planarMacroScale *
            drawingGridSize (PeriodicCNF.incidenceGraph formula)) =
        (link.first.position
            (PeriodicCNF.incidenceGraph formula)).2 /
          (planarMacroScale *
            drawingGridSize (PeriodicCNF.incidenceGraph formula))
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal] at positionCases axisData
    rcases positionCases with positionEq | positionEq <;>
      rw [positionEq] <;>
      simp only [AxisDirection.placePoint,
        AxisDirection.orientPoint, Cell.add]
    · constructor
      · convert
          add_small_quotient_eq
            (periodFactor :=
              2 * drawingGridSize
                (PeriodicCNF.incidenceGraph formula))
            axisData.2.1 (by norm_num : (0 : Int) ≤ 3)
              (by norm_num : (3 : Int) < 9) using 1 <;>
            norm_num [planarMacroScale] <;> ring_nf
      · simp
    · constructor
      · convert
          add_small_quotient_eq
            (periodFactor :=
              2 * drawingGridSize
                (PeriodicCNF.incidenceGraph formula))
            axisData.2.1 (by norm_num : (0 : Int) ≤ 6)
              (by norm_num : (6 : Int) < 9) using 1 <;>
            norm_num [planarMacroScale] <;> ring_nf
      · simp
  · rw [if_neg horizontal] at positionCases axisData
    rcases positionCases with positionEq | positionEq <;>
      rw [positionEq] <;>
      simp only [AxisDirection.placePoint,
        AxisDirection.orientPoint, Cell.add]
    · constructor
      · simp
      · convert
          add_small_quotient_eq
            (periodFactor :=
              2 * drawingGridSize
                (PeriodicCNF.incidenceGraph formula))
            axisData.2.1 (by norm_num : (0 : Int) ≤ 3)
              (by norm_num : (3 : Int) < 9) using 1 <;>
            norm_num [planarMacroScale] <;> ring_nf
    · constructor
      · simp
      · convert
          add_small_quotient_eq
            (periodFactor :=
              2 * drawingGridSize
                (PeriodicCNF.incidenceGraph formula))
            axisData.2.1 (by norm_num : (0 : Int) ≤ 6)
              (by norm_num : (6 : Int) < 9) using 1 <;>
            norm_num [planarMacroScale] <;> ring_nf

theorem noncarrier_clause_first_in_macrocell
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
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula = some center)
    (first : PlanarSATVariable Variable × Bool)
    (firstMember :
      (first, 0) ∈ metadata.clause.literals.zipIdx) :
    InPlanarSATMacrocell center
      (drawingPlanarSATVariablePosition formula first.1) := by
  have notCarrier :
      ¬∃ link, metadata.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at centerEq
    simp [DrawingPlanarSATComponent.macrocellCenter] at centerEq
  have originalValid : metadata.Valid formula :=
    metadata.valid_of_retainedValid_of_not_carrier valid notCarrier
  have clauseMember :=
    metadata.retainedLocalClauseMember
      wellFormed degree isLocal valid
  have routesMatch :=
    metadata.retainedLocalDrawingRoutesMatch
      wellFormed degree isLocal valid
  have endpoints :=
    (metadata.source.incidenceDrawing formula).physicalRoutesMatch
      routesMatch metadata.clause
      metadata.source.localClauseIndex clauseMember
      first 0 firstMember
  rw [DrawingPlanarSATClauseSource.incidenceDrawing_variablePosition]
    at endpoints
  have positionMember :
      drawingPlanarSATVariablePosition formula first.1 ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex 0 :=
    mem_of_getLast?_eq_some endpoints.2
  exact
    metadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal originalValid
      center centerEq firstMember positionMember

theorem noncarrier_clause_first_quotient
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
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula = some center)
    (first : PlanarSATVariable Variable × Bool)
    (rest : List (PlanarSATVariable Variable × Bool))
    (literalsEq : metadata.clause.literals = first :: rest) :
    metadata.clause.position.1 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        (drawingPlanarSATVariablePosition formula first.1).1 /
          (drawingPeriodicPlanarSATPlacement formula).period ∧
      metadata.clause.position.2 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        (drawingPlanarSATVariablePosition formula first.1).2 /
          (drawingPeriodicPlanarSATPlacement formula).period := by
  have firstMember :
      (first, 0) ∈ metadata.clause.literals.zipIdx := by
    simp [literalsEq]
  have clauseBounded :=
    metadata.retainedClausePosition_in_macrocell
      wellFormed degree isLocal valid center centerEq
        (by simp [literalsEq])
  have firstBounded :=
    noncarrier_clause_first_in_macrocell
      wellFormed degree isLocal metadata valid center centerEq
      first firstMember
  simpa [drawingPeriodicPlanarSATPlacement, planarMacroScale] using
    (macrocellQuotient_eq
      (periodFactor :=
        drawingGridSize (PeriodicCNF.incidenceGraph formula))
      clauseBounded firstBounded)

theorem retained_clause_first_quotient
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
    (first : PlanarSATVariable Variable × Bool)
    (rest : List (PlanarSATVariable Variable × Bool))
    (literalsEq : metadata.clause.literals = first :: rest) :
    metadata.clause.position.1 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        (drawingPlanarSATVariablePosition formula first.1).1 /
          (drawingPeriodicPlanarSATPlacement formula).period ∧
      metadata.clause.position.2 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        (drawingPlanarSATVariablePosition formula first.1).2 /
          (drawingPeriodicPlanarSATPlacement formula).period := by
  rcases metadata with ⟨clause, source⟩
  cases source with
  | carrier link localClauseIndex =>
      exact carrier_clause_first_quotient
        wellFormed degree isLocal valid.1 valid.2
        first rest literalsEq
  | crossover crossing localClauseIndex =>
      apply noncarrier_clause_first_quotient
        wellFormed degree isLocal
        ⟨clause, .crossover crossing localClauseIndex⟩ valid
        crossing.point
      · simp [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.macrocellCenter]
      · exact literalsEq
  | bend routeBend localClauseIndex =>
      apply noncarrier_clause_first_quotient
        wellFormed degree isLocal
        ⟨clause, .bend routeBend localClauseIndex⟩ valid
        (routeBend.drawingPoint
          (PeriodicCNF.incidenceGraph formula))
      · simp [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.macrocellCenter]
      · exact literalsEq
  | routedClause site =>
      apply noncarrier_clause_first_quotient
        wellFormed degree isLocal
        ⟨clause, .routedClause site⟩ valid
        (liftedIncidenceVertexPosition formula
          (.clause site.1) site.2)
      · simp [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.macrocellCenter]
      · exact literalsEq
  | routedVariable site armIndex arm link localClauseIndex =>
      apply noncarrier_clause_first_quotient
        wellFormed degree isLocal
        ⟨clause,
          .routedVariable site armIndex arm link localClauseIndex⟩
        valid
        (liftedIncidenceVertexPosition formula
          (.variable site.1) site.2)
      · simp [DrawingPlanarSATClauseSource.component,
          DrawingPlanarSATComponent.macrocellCenter]
      · exact literalsEq

def clauseResidue
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable)) : Cell :=
  (clause.position.1 %
      (drawingPeriodicPlanarSATPlacement formula).period,
    clause.position.2 %
      (drawingPeriodicPlanarSATPlacement formula).period)

theorem metadata_canonicalClausePosition_eq_residue
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
    (nonempty : metadata.clause.literals ≠ []) :
    PositionedPeriodicCNF.canonicalClausePosition
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        ⟨metadata.clause.position,
          (wrapPeriodicPlanarSATClause
            (periodicizePlanarSATClause formula
              metadata.clause)).variableGauge
                (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                  formula)⟩ =
      clauseResidue formula metadata.clause := by
  cases literalsEq : metadata.clause.literals with
  | nil => exact (nonempty literalsEq).elim
  | cons first rest =>
      apply canonicalClausePosition_eq_emod
        formula metadata.clause first rest literalsEq
      · exact
          (retained_clause_first_quotient
            wellFormed degree isLocal metadata valid
            first rest literalsEq).1
      · exact
          (retained_clause_first_quotient
            wellFormed degree isLocal metadata valid
            first rest literalsEq).2

theorem anchorNormalized_clausePositions_eq_residues
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
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.map PositionedPeriodicClause.position =
      (retainedDrawingPlanarSATFormula formula).map
        (clauseResidue formula) := by
  unfold
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedDrawingPositionedPeriodicPlanarSATFormula
    positionPeriodicizedPlanarSATFormula
    PositionedPeriodicCNF.anchorNormalize
    PositionedPeriodicCNF.variableGauge
    PositionedPeriodicCNF.rename
  simp only [List.map_map]
  rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
  simp only [List.map_map]
  apply List.map_congr_left
  intro metadata metadataMember
  change
    PositionedPeriodicCNF.canonicalClausePosition
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        ⟨metadata.clause.position,
          (wrapPeriodicPlanarSATClause
            (periodicizePlanarSATClause formula
              metadata.clause)).variableGauge
                (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
                  formula)⟩ =
      clauseResidue formula metadata.clause
  apply metadata_canonicalClausePosition_eq_residue
    wellFormed degree isLocal metadata
  · exact retainedDrawingPlanarSATClauseMetadata_valid
      formula metadataMember
  · exact clausesNonempty metadata.clause
      (by
        rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
        exact List.mem_map.mpr
          ⟨metadata, metadataMember, rfl⟩)

theorem crossoverClause_localPosition_strict
    {Variable : Type*}
    {crossing : CrossingRecord}
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (member :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) crossing).zipIdx) :
    ∃ offset,
      clause.position =
        Cell.add (crossingMacroOrigin crossing) offset ∧
      0 < offset.1 ∧ offset.1 < planarMacroScale ∧
        0 < offset.2 ∧ offset.2 < planarMacroScale := by
  have indexLt := List.snd_lt_of_mem_zipIdx member
  simp [drawingPlanarSATCrossoverFormulaAt,
    scopedCrossoverInstance, instantiateFormula,
    crossoverFormula] at indexLt
  interval_cases clauseIndex <;>
    simp_all [drawingPlanarSATCrossoverFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      EmbeddedClause.rename, EmbeddedClause.map,
      crossoverFormula, crossoverClause, EmbeddedClause.place,
      crossingMacroOrigin, Cell.add, Cell.scale, planarMacroScale]

theorem bendClause_localPosition_strict
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (member :
      (clause, clauseIndex) ∈
        (drawingPlanarSATBendFormulaAt
          (Variable := Variable) graph routeBend).zipIdx) :
    ∃ offset,
      clause.position =
        Cell.add
          (Cell.scale planarMacroScale
            (routeBend.drawingPoint graph)) offset ∧
      0 < offset.1 ∧ offset.1 < planarMacroScale ∧
        0 < offset.2 ∧ offset.2 < planarMacroScale := by
  have indexLt := List.snd_lt_of_mem_zipIdx member
  simp [drawingPlanarSATBendFormulaAt,
    drawingPlanarSATCarrierFormulaAt, equalityInstance] at indexLt
  interval_cases clauseIndex <;>
    simp_all [drawingPlanarSATBendFormulaAt,
      drawingPlanarSATCarrierFormulaAt, equalityInstance,
      RouteBend.equalityLink, routeBendEqualityPositions,
      EmbeddedClause.rename, EmbeddedClause.map,
      Cell.add, Cell.scale, planarMacroScale]

theorem routedClause_localPosition_strict
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    (equal :
      clause =
        (routedClauseAt formula site).rename
          planarSATExternalVariableMap) :
    ∃ offset,
      clause.position =
        Cell.add (routedClauseOrigin formula site) offset ∧
      0 < offset.1 ∧ offset.1 < planarMacroScale ∧
        0 < offset.2 ∧ offset.2 < planarMacroScale := by
  subst clause
  refine ⟨(10, 10), ?_⟩
  simp [routedClauseAt, routedClauseOrigin,
    liftedIncidenceVertexMacroOrigin,
    EmbeddedClause.rename, EmbeddedClause.map,
    Cell.add, Cell.scale, planarMacroScale]

theorem routedVariableClause_localPosition_strict
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
    ∃ offset,
      clause.position = Cell.add origin offset ∧
      0 < offset.1 ∧ offset.1 < planarMacroScale ∧
        0 < offset.2 ∧ offset.2 < planarMacroScale := by
  have indexLt := List.snd_lt_of_mem_zipIdx member
  simp [drawingPlanarSATRoutedVariableFormulaAt,
    equalityInstance] at indexLt
  interval_cases clauseIndex <;>
    simp_all [drawingPlanarSATRoutedVariableFormulaAt,
      equalityInstance, EmbeddedClause.rename,
      EmbeddedClause.map, Cell.add, planarMacroScale] <;>
    cases arm <;>
      simp_all [duplicatorArmEqualityPositions]

theorem carrierNode_position_emod_ten_ne_zero
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) :
    (node.position graph).1 % 10 ≠ 0 ∧
      (node.position graph).2 % 10 ≠ 0 := by
  cases node with
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      cases side <;>
        norm_num [CarrierNode.position, CrossingBoundary.position,
          crossingMacroOrigin, CrossingSide.localPosition,
          CrossoverVariable.position, Cell.add, Cell.scale,
          planarMacroScale, Int.add_emod, Int.mul_emod]
  | terminal terminal =>
      rcases terminal with ⟨indexed, translate, endpoint⟩
      change
        (SegmentTerminal.position graph
            ⟨indexed, translate, endpoint⟩).1 % 10 ≠ 0 ∧
          (SegmentTerminal.position graph
            ⟨indexed, translate, endpoint⟩).2 % 10 ≠ 0
      unfold SegmentTerminal.position segmentTerminalLocalPosition
      split_ifs <;> cases endpoint <;>
        norm_num [SegmentTerminal.drawingPoint,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, Cell.add, Cell.scale,
          planarMacroScale, Int.add_emod, Int.mul_emod]

theorem carrierClause_position_emod_ten_ne_zero
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
    clause.position.1 % 10 ≠ 0 ∧
      clause.position.2 % 10 ≠ 0 := by
  have positionCases :=
    carrierClause_position_eq_forward_or_backward clauseMember
  have geometry :=
    retainedDrawingCompleteCarrierLink_lensGeometry
      wellFormed degree isLocal linkMem
  have direction :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal linkMem
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      (PeriodicCNF.incidenceGraph formula) linkMem
  have common :=
    retainedDrawingCompleteCarrierLinks_common_key
      (PeriodicCNF.incidenceGraph formula) linkMem
  have axisData :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal endpoints.1 endpoints.2 common
  have firstNonzero :=
    carrierNode_position_emod_ten_ne_zero
      (PeriodicCNF.incidenceGraph formula) link.first
  rw [geometry.positions] at positionCases
  change
    AxisDirection.between
        (link.first.position (PeriodicCNF.incidenceGraph formula))
        (link.second.position (PeriodicCNF.incidenceGraph formula)) =
      (if link.first.isHorizontal then .east else .north)
    at direction
  rw [direction] at positionCases
  by_cases horizontal : link.first.isHorizontal = true
  · rw [if_pos horizontal] at positionCases axisData
    rcases positionCases with positionEq | positionEq <;>
      rw [positionEq] <;>
      simp only [AxisDirection.placePoint,
        AxisDirection.orientPoint, Cell.add]
    · constructor
      · rw [Int.add_emod, axisData.2.1]
        norm_num
      · simpa using firstNonzero.2
    · constructor
      · rw [Int.add_emod, axisData.2.1]
        norm_num
      · simpa using firstNonzero.2
  · rw [if_neg horizontal] at positionCases axisData
    rcases positionCases with positionEq | positionEq <;>
      rw [positionEq] <;>
      simp only [AxisDirection.placePoint,
        AxisDirection.orientPoint, Cell.add]
    · constructor
      · simpa using firstNonzero.1
      · rw [Int.add_emod, axisData.2.1]
        norm_num
    · constructor
      · simpa using firstNonzero.1
      · rw [Int.add_emod, axisData.2.1]
        norm_num

theorem emod_multiple_ne_zero
    {coordinate factor multiple : Int}
    (factorResidueNonzero : coordinate % factor ≠ 0) :
    coordinate % (factor * multiple) ≠ 0 := by
  intro zero
  have multipleDvdCoordinate :
      factor * multiple ∣ coordinate :=
    Int.dvd_of_emod_eq_zero zero
  have factorDvdCoordinate : factor ∣ coordinate :=
    (dvd_mul_right factor multiple).trans multipleDvdCoordinate
  exact factorResidueNonzero
    (Int.emod_eq_zero_of_dvd factorDvdCoordinate)

theorem scale_add_local_coordinate_emod_ne_zero
    {macroPeriod : Nat} {center localPosition : Cell}
    (localBounds :
      0 < localPosition.1 ∧
        localPosition.1 < planarMacroScale ∧
        0 < localPosition.2 ∧
        localPosition.2 < planarMacroScale) :
    (Cell.add (Cell.scale planarMacroScale center)
          localPosition).1 %
          (planarMacroScale * macroPeriod) ≠ 0 ∧
      (Cell.add (Cell.scale planarMacroScale center)
          localPosition).2 %
          (planarMacroScale * macroPeriod) ≠ 0 := by
  constructor
  · simpa [Cell.add, Cell.scale] using
      (macrocellCoordinate_emod_period_ne_zero
        (macroPeriod := macroPeriod)
        localBounds.1 localBounds.2.1)
  · simpa [Cell.add, Cell.scale] using
      (macrocellCoordinate_emod_period_ne_zero
        (macroPeriod := macroPeriod)
        localBounds.2.2.1 localBounds.2.2.2)

theorem metadata_clausePosition_emod_period_ne_zero
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula) :
    metadata.clause.position.1 %
          (drawingPeriodicPlanarSATPlacement formula).period ≠ 0 ∧
      metadata.clause.position.2 %
          (drawingPeriodicPlanarSATPlacement formula).period ≠ 0 := by
  rcases metadata with ⟨clause, source⟩
  cases source with
  | carrier link localClauseIndex =>
      have modTen :=
        carrierClause_position_emod_ten_ne_zero
          wellFormed degree isLocal valid.1 valid.2
      constructor
      · convert emod_multiple_ne_zero
          (multiple :=
            2 * drawingGridSize
              (PeriodicCNF.incidenceGraph formula))
          modTen.1 using 1
        all_goals
          norm_num [drawingPeriodicPlanarSATPlacement,
            planarMacroScale]
        all_goals ring_nf
      · convert emod_multiple_ne_zero
          (multiple :=
            2 * drawingGridSize
              (PeriodicCNF.incidenceGraph formula))
          modTen.2 using 1
        all_goals
          norm_num [drawingPeriodicPlanarSATPlacement,
            planarMacroScale]
        all_goals ring_nf
  | crossover crossing localClauseIndex =>
      rcases crossoverClause_localPosition_strict valid.2 with
        ⟨offset, positionEq, bounds⟩
      rw [positionEq]
      simpa [crossingMacroOrigin,
        drawingPeriodicPlanarSATPlacement, planarMacroScale] using
        (scale_add_local_coordinate_emod_ne_zero
          (macroPeriod :=
            drawingGridSize
              (PeriodicCNF.incidenceGraph formula))
          bounds)
  | bend routeBend localClauseIndex =>
      rcases bendClause_localPosition_strict
          (PeriodicCNF.incidenceGraph formula)
          routeBend valid.2 with
        ⟨offset, positionEq, bounds⟩
      rw [positionEq]
      simpa [drawingPeriodicPlanarSATPlacement,
        planarMacroScale] using
        (scale_add_local_coordinate_emod_ne_zero
          (macroPeriod :=
            drawingGridSize
              (PeriodicCNF.incidenceGraph formula))
          bounds)
  | routedClause site =>
      rcases routedClause_localPosition_strict
          formula site valid.2 with
        ⟨offset, positionEq, bounds⟩
      rw [positionEq]
      simpa [routedClauseOrigin,
        liftedIncidenceVertexMacroOrigin,
        drawingPeriodicPlanarSATPlacement,
        planarMacroScale] using
        (scale_add_local_coordinate_emod_ne_zero
          (macroPeriod :=
            drawingGridSize
              (PeriodicCNF.incidenceGraph formula))
          bounds)
  | routedVariable site armIndex arm link localClauseIndex =>
      have linkMember :=
        List.fst_mem_of_mem_zipIdx valid.2.1
      have linkPositions :=
        routedVariableLink_positions formula site linkMember
      have positionsEq :
          link.positions =
            ⟨Cell.add (routedVariableOrigin formula site)
                (duplicatorArmEqualityPositions arm).forward,
              Cell.add (routedVariableOrigin formula site)
                (duplicatorArmEqualityPositions arm).backward⟩ := by
        rw [linkPositions, valid.2.2.1]
        rfl
      rcases routedVariableClause_localPosition_strict
          (routedVariableOrigin formula site) arm link positionsEq
          valid.2.2.2 with
        ⟨offset, positionEq, bounds⟩
      rw [positionEq]
      simpa [routedVariableOrigin,
        liftedIncidenceVertexMacroOrigin,
        drawingPeriodicPlanarSATPlacement,
        planarMacroScale] using
        (scale_add_local_coordinate_emod_ne_zero
          (macroPeriod :=
            drawingGridSize
              (PeriodicCNF.incidenceGraph formula))
          bounds)

theorem anchorNormalized_clausePositions_eq_metadata_residues
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
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).clauses.map PositionedPeriodicClause.position =
      (retainedDrawingPlanarSATClauseMetadata formula).map
        (fun metadata =>
          clauseResidue formula metadata.clause) := by
  rw [anchorNormalized_clausePositions_eq_residues
    formula wellFormed degree isLocal clausesNonempty]
  rw [← retainedDrawingPlanarSATClauseMetadata_clauses,
    List.map_map]
  rfl

theorem anchorNormalized_clausePositions_inSquare
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
    (position : Cell)
    (positionMem :
      position ∈
        (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.map PositionedPeriodicClause.position) :
    0 < position.1 ∧
      position.1 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period ∧
      0 < position.2 ∧
      position.2 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
  rw [anchorNormalized_clausePositions_eq_metadata_residues
    formula wellFormed degree isLocal clausesNonempty] at positionMem
  rcases List.mem_map.mp positionMem with
    ⟨metadata, metadataMember, positionEq⟩
  have valid :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula metadataMember
  have nonzero :=
    metadata_clausePosition_emod_period_ne_zero
      wellFormed degree isLocal metadata valid
  have periodPositiveNat :=
    drawingPeriodicPlanarSATPlacement_period_pos formula
  have periodPositive :
      (0 : Int) <
        (drawingPeriodicPlanarSATPlacement formula).period := by
    exact_mod_cast periodPositiveNat
  rw [← positionEq]
  change
    0 <
        metadata.clause.position.1 %
          (drawingPeriodicPlanarSATPlacement formula).period ∧
      metadata.clause.position.1 %
          (drawingPeriodicPlanarSATPlacement formula).period <
        (drawingPeriodicPlanarSATPlacement formula).period ∧
      0 <
        metadata.clause.position.2 %
          (drawingPeriodicPlanarSATPlacement formula).period ∧
      metadata.clause.position.2 %
          (drawingPeriodicPlanarSATPlacement formula).period <
        (drawingPeriodicPlanarSATPlacement formula).period
  exact
    ⟨lt_of_le_of_ne
        (Int.emod_nonneg _ (ne_of_gt periodPositive))
        (Ne.symm nonzero.1),
      Int.emod_lt_of_pos _ periodPositive,
      lt_of_le_of_ne
        (Int.emod_nonneg _ (ne_of_gt periodPositive))
        (Ne.symm nonzero.2),
      Int.emod_lt_of_pos _ periodPositive⟩

theorem deduplicateByLiterals_clausePositions_satisfy
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (predicate : Cell → Prop)
    (sourceSatisfies :
      ∀ position ∈
          source.clauses.map PositionedPeriodicClause.position,
        predicate position)
    (position : Cell)
    (positionMem :
      position ∈
        source.deduplicateByLiterals.clauses.map
          PositionedPeriodicClause.position) :
    predicate position := by
  rw [PositionedPeriodicCNF.deduplicateByLiterals,
    List.map_map] at positionMem
  rcases List.mem_map.mp positionMem with
    ⟨literals, literalsMember, positionEq⟩
  have literalsSourceMember :
      literals ∈ source.erase.clauses := by
    simpa using literalsMember
  rcases PositionedPeriodicCNF.exists_representativeClause
      source literals literalsSourceMember with
    ⟨sourceClause, sourceLookup, _sourceLiterals,
      sourcePosition⟩
  have sourceClauseMember : sourceClause ∈ source.clauses := by
    exact List.mem_iff_getElem.mpr
      ⟨source.representativeClauseIndex literals,
        (List.getElem?_eq_some_iff.mp sourceLookup).1,
        (List.getElem?_eq_some_iff.mp sourceLookup).2⟩
  rw [← sourcePosition.trans positionEq]
  exact sourceSatisfies sourceClause.position
    (List.mem_map.mpr ⟨sourceClause, sourceClauseMember, rfl⟩)

theorem deduplicated_storedClausePositions_inSquare
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
    (position : Cell)
    (positionMem :
      position ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.map PositionedPeriodicClause.position) :
    0 < position.1 ∧
      position.1 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period ∧
      0 < position.2 ∧
      position.2 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
  apply deduplicateByLiterals_clausePositions_satisfy
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (fun position =>
      0 < position.1 ∧
        position.1 <
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period ∧
        0 < position.2 ∧
        position.2 <
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).period)
  · exact anchorNormalized_clausePositions_inSquare
      formula wellFormed degree isLocal clausesNonempty
  · exact positionMem

end LeanTrominoes.PeriodicOrthocrossing
