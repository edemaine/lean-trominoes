/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableGauge

/-!
# Gauged retained periodic planar-SAT variable positions

Canonical variable gauging reduces every routed-SAT prototype position
modulo the refined drawing period.  Every local variable coordinate is
strictly inside its `20 × 20` macrocell, so the reduced point lies in the
open fundamental square.  To prove quotient injectivity, terminals are
lifted back into their neighboring finite route cells while all other
variables use their canonical zero lift.  Finite retained-position
injectivity then proves that the gauged periodic variable positions are
pairwise distinct.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- An interior macrocell coordinate cannot be zero modulo any whole number
of macrocells. -/
theorem macrocellCoordinate_emod_period_ne_zero
    {macroPeriod : Nat}
    {center localCoordinate : Int}
    (localPositive : 0 < localCoordinate)
    (localSmall : localCoordinate < planarMacroScale) :
    (planarMacroScale * center + localCoordinate) %
        (planarMacroScale * macroPeriod) ≠ 0 := by
  intro zero
  have divides :
      (planarMacroScale * (macroPeriod : Int)) ∣
        planarMacroScale * center + localCoordinate :=
    Int.dvd_of_emod_eq_zero zero
  rcases divides with ⟨quotient, equal⟩
  have localMultiple :
      localCoordinate =
        planarMacroScale *
          ((macroPeriod : Int) * quotient - center) := by
    linear_combination equal
  norm_num [planarMacroScale] at localPositive localSmall localMultiple
  omega

/-- A point in a canonical macrocell has macrocell-period quotient zero. -/
theorem macrocellCoordinate_ediv_period_eq_zero
    {macroPeriod : Nat} (macroPeriodPositive : 0 < macroPeriod)
    {center localCoordinate : Int}
    (centerNonnegative : 0 ≤ center)
    (centerSmall : center < macroPeriod)
    (localNonnegative : 0 ≤ localCoordinate)
    (localSmall : localCoordinate < planarMacroScale) :
    (planarMacroScale * center + localCoordinate) /
        (planarMacroScale * macroPeriod) = 0 := by
  have macroPeriodPositiveInt : (0 : Int) < macroPeriod := by
    exact_mod_cast macroPeriodPositive
  have denominatorPositive :
      (0 : Int) <
        planarMacroScale * (macroPeriod : Int) := by
    exact mul_pos (by norm_num [planarMacroScale])
      macroPeriodPositiveInt
  apply Int.ediv_eq_zero_of_lt_abs
  · nlinarith [show (0 : Int) < planarMacroScale by
      norm_num [planarMacroScale]]
  · rw [abs_of_pos denominatorPositive]
    have centerUpper : center ≤ (macroPeriod : Int) - 1 := by
      omega
    nlinarith [show (0 : Int) < planarMacroScale by
      norm_num [planarMacroScale]]

/-- Drawing-grid macrocell containing a periodic routed-SAT variable. -/
def periodicPlanarSATVariableDrawingPoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicPlanarSATVariable Variable → Cell
  | .terminal indexed endpoint =>
      SegmentTerminal.drawingPoint
        (PeriodicCNF.incidenceGraph formula)
        ⟨indexed, (0, 0), endpoint⟩
  | .boundary boundary => boundary.crossing.point
  | .atom atom =>
      liftedIncidenceVertexPosition
        formula (.variable atom) (0, 0)
  | .crossoverInternal (crossing, _) => crossing.point

/-- Strictly interior local coordinate of a periodic routed-SAT variable. -/
def periodicPlanarSATVariableLocalPosition
    {Variable : Type*} :
    PeriodicPlanarSATVariable Variable → Cell
  | .terminal indexed endpoint =>
      segmentTerminalLocalPosition indexed.segment endpoint
  | .boundary boundary => boundary.side.localPosition
  | .atom _ => duplicatorArmCenterPosition
  | .crossoverInternal (_, internal) =>
      CrossoverVariable.position
        (crossoverInternalVariable internal)

/-- Every routed-SAT variable uses a strictly interior local coordinate. -/
theorem periodicPlanarSATVariableLocalPosition_in_macrocell
    {Variable : Type*}
    (atom : PeriodicPlanarSATVariable Variable) :
    let position := periodicPlanarSATVariableLocalPosition atom
    0 < position.1 ∧ position.1 < planarMacroScale ∧
      0 < position.2 ∧ position.2 < planarMacroScale := by
  cases atom with
  | terminal indexed endpoint =>
      exact segmentTerminalLocalPosition_in_macrocell
        indexed.segment endpoint
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      cases side <;>
        norm_num [periodicPlanarSATVariableLocalPosition,
          CrossingSide.localPosition,
          CrossoverVariable.position, planarMacroScale]
  | atom atom =>
      norm_num [periodicPlanarSATVariableLocalPosition,
        duplicatorArmCenterPosition, planarMacroScale]
  | crossoverInternal internal =>
      rcases internal with ⟨crossing, internal⟩
      cases internal <;>
        norm_num [periodicPlanarSATVariableLocalPosition,
          crossoverInternalVariable,
          CrossoverVariable.position, planarMacroScale]

/-- Every routed-SAT variable position splits into a scaled drawing point
and its local macrocell coordinate. -/
theorem drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    drawingPeriodicPlanarSATVariablePosition formula atom =
      Cell.add
        (Cell.scale planarMacroScale
          (periodicPlanarSATVariableDrawingPoint formula atom))
        (periodicPlanarSATVariableLocalPosition atom) := by
  cases atom with
  | terminal indexed endpoint => rfl
  | boundary boundary =>
      simp [drawingPeriodicPlanarSATVariablePosition,
        periodicPlanarSATVariableDrawingPoint,
        periodicPlanarSATVariableLocalPosition,
        CrossingBoundary.position, crossingMacroOrigin]
  | atom atom =>
      simp [drawingPeriodicPlanarSATVariablePosition,
        periodicPlanarSATVariableDrawingPoint,
        periodicPlanarSATVariableLocalPosition,
        liftedIncidenceVertexMacroOrigin]
  | crossoverInternal internal =>
      rcases internal with ⟨crossing, internal⟩
      simp [drawingPeriodicPlanarSATVariablePosition,
        periodicPlanarSATVariableDrawingPoint,
        periodicPlanarSATVariableLocalPosition,
        crossingMacroOrigin]

/-- Neither coordinate of a routed-SAT variable is zero modulo the refined
drawing period. -/
theorem drawingPeriodicPlanarSATVariablePosition_coordinate_emod_ne_zero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    ((drawingPeriodicPlanarSATPlacement formula).position atom).1 %
          (drawingPeriodicPlanarSATPlacement formula).period ≠ 0 ∧
      ((drawingPeriodicPlanarSATPlacement formula).position atom).2 %
          (drawingPeriodicPlanarSATPlacement formula).period ≠ 0 := by
  have localBounds :=
    periodicPlanarSATVariableLocalPosition_in_macrocell atom
  rw [show
      (drawingPeriodicPlanarSATPlacement formula).position atom =
        drawingPeriodicPlanarSATVariablePosition formula atom by rfl,
    drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
  constructor
  · simpa [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] using
      (macrocellCoordinate_emod_period_ne_zero
        (macroPeriod :=
          drawingGridSize (PeriodicCNF.incidenceGraph formula))
        localBounds.1 localBounds.2.1)
  · simpa [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] using
      (macrocellCoordinate_emod_period_ne_zero
        (macroPeriod :=
          drawingGridSize (PeriodicCNF.incidenceGraph formula))
        localBounds.2.2.1 localBounds.2.2.2)

/-- A routed variable site always names a declared variable vertex of the
source incidence graph. -/
theorem drawingVariableRouteSite_variable_vertex_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    {atom : Variable} {translate : Cell}
    (siteMem :
      (atom, translate) ∈ drawingVariableRouteSites formula) :
    CNFVertex.variable atom ∈
      (PeriodicCNF.incidenceGraph formula).vertices := by
  rw [drawingVariableRouteSites, List.mem_dedup] at siteMem
  rcases List.mem_map.mp siteMem with
    ⟨occurrence, occurrenceMem, siteEq⟩
  rw [drawingCNFRouteOccurrences, List.mem_flatMap]
    at occurrenceMem
  rcases occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, occurrenceMem⟩
  rcases List.mem_map.mp occurrenceMem with
    ⟨occurrenceTranslate, _occurrenceTranslateMem, occurrenceEq⟩
  subst occurrence
  have atomEq :
      taggedIncidence.1.literal.atom = atom :=
    congrArg Prod.fst siteEq
  have edgeMem :=
    PeriodicCNF.tagged_incidence_edge_mem
      formula taggedIncidenceMem
  have endpoints :=
    wellFormed.2 taggedIncidence.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMem)
  rw [CNFIncidence.edge_target, atomEq] at endpoints
  exact endpoints.2

/-- Every valid nonterminal periodic variable is already in the canonical
physical period cell. -/
theorem retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (atom : PeriodicPlanarSATVariable Variable)
    (valid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula atom)
    (nonterminal :
      ∀ indexed endpoint, atom ≠ .terminal indexed endpoint) :
    (drawingPeriodicPlanarSATPlacement formula).canonicalPositionGauge
        atom =
      (0, 0) := by
  have periodPositive :=
    drawingGridSize_pos (PeriodicCNF.incidenceGraph formula)
  have localBounds :=
    periodicPlanarSATVariableLocalPosition_in_macrocell atom
  have drawingPointBounds :
      InFundamentalDrawingSquare
        (PeriodicCNF.incidenceGraph formula)
        (periodicPlanarSATVariableDrawingPoint formula atom) := by
    cases atom with
    | terminal indexed endpoint =>
        exact False.elim (nonterminal indexed endpoint rfl)
    | boundary boundary =>
        change
          boundary ∈
            drawingCrossingBoundaries
              (PeriodicCNF.incidenceGraph formula)
          at valid
        rw [drawingCrossingBoundaries, List.mem_flatMap] at valid
        rcases valid with
          ⟨crossing, crossingMem, boundaryMem⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false]
          at boundaryMem
        rcases boundaryMem with
          boundaryEq | boundaryEq | boundaryEq | boundaryEq <;>
            subst boundary <;>
            exact
              (orientedCrossings_sound
                (PeriodicCNF.incidenceGraph formula)
                crossingMem).2.2.2.2.1.1
    | atom atom =>
        have vertexMem :=
          drawingVariableRouteSite_variable_vertex_mem
            formula wellFormed valid
        have bounded :=
          drawing_vertexPosition_in_fundamental_square
            (PeriodicCNF.incidenceGraph formula) vertexMem
        simpa [periodicPlanarSATVariableDrawingPoint,
          liftedIncidenceVertexPosition,
          PeriodicGridDrawing.periodTranslation,
          Cell.add, Cell.scale,
          InFundamentalDrawingSquare,
          PeriodicGridDrawing.PositionInFundamentalSquare] using
          And.intro (le_of_lt bounded.1)
            (And.intro bounded.2.1
              (And.intro (le_of_lt bounded.2.2.1)
                bounded.2.2.2))
    | crossoverInternal internal =>
        exact
          (orientedCrossings_sound
            (PeriodicCNF.incidenceGraph formula) valid).2.2.2.2.1.1
  apply Prod.ext
  · change
      (drawingPeriodicPlanarSATVariablePosition formula atom).1 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        0
    rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
    simpa [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] using
      (macrocellCoordinate_ediv_period_eq_zero
        periodPositive
        drawingPointBounds.1 drawingPointBounds.2.1
        (le_of_lt localBounds.1) localBounds.2.1)
  · change
      (drawingPeriodicPlanarSATVariablePosition formula atom).2 /
          (drawingPeriodicPlanarSATPlacement formula).period =
        0
    rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
    simpa [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] using
      (macrocellCoordinate_ediv_period_eq_zero
        periodPositive
        drawingPointBounds.2.2.1 drawingPointBounds.2.2.2
        (le_of_lt localBounds.2.2.1) localBounds.2.2.2)

/-- Canonical gauging puts every wrapped routed-SAT variable strictly inside
the refined fundamental square. -/
theorem retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    0 <
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).position atom).1 ∧
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).position atom).1 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period ∧
      0 <
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).position atom).2 ∧
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).position atom).2 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
  have nonzero :=
    drawingPeriodicPlanarSATVariablePosition_coordinate_emod_ne_zero
      formula atom.original
  exact
    PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position_inSquare
      (wrappedDrawingPeriodicPlanarSATPlacement formula)
      (drawingPeriodicPlanarSATPlacement_period_pos formula)
      atom nonzero.1 nonzero.2

/-- A coordinate in the open three-period window has neighboring quotient. -/
theorem coordinatePeriodQuotient_isNeighbor
    {period point : Int}
    (periodPositive : 0 < period)
    (pointLower : -period < point)
    (pointUpper : point < 2 * period) :
    point / period = -1 ∨
      point / period = 0 ∨
      point / period = 1 := by
  have periodNe : period ≠ 0 := ne_of_gt periodPositive
  have remainderNonnegative :=
    Int.emod_nonneg point periodNe
  have remainderLt :=
    Int.emod_lt_of_pos point periodPositive
  have division := Int.emod_add_mul_ediv point period
  have quotientLower : -1 ≤ point / period := by
    by_contra lower
    have quotientLe : point / period ≤ -2 := by omega
    have productLe :
        period * (point / period) ≤ period * (-2) :=
      mul_le_mul_of_nonneg_left quotientLe (le_of_lt periodPositive)
    nlinarith
  have quotientUpper : point / period ≤ 1 := by
    by_contra upper
    have quotientGe : 2 ≤ point / period := by omega
    have productGe :
        period * 2 ≤ period * (point / period) :=
      mul_le_mul_of_nonneg_left quotientGe (le_of_lt periodPositive)
    nlinarith
  omega

/-- The canonical gauge of a valid terminal selects one of the nine finite
neighboring route cells. -/
theorem
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge_terminal_isNeighbor
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (indexed : IndexedGridSegment)
    (endpoint : SegmentEnd)
    (valid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula
        (.terminal indexed endpoint)) :
    IsNeighborTranslation
      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
        formula ⟨.terminal indexed endpoint⟩) := by
  have endpointBounds :=
    drawing_indexedSegment_endpoints_inExpandedDrawingSquare
      wellFormed degree isLocal valid
  have drawingPointBounds :
      InExpandedDrawingSquare
        (PeriodicCNF.incidenceGraph formula)
        (SegmentTerminal.drawingPoint
          (PeriodicCNF.incidenceGraph formula)
          ⟨indexed, (0, 0), endpoint⟩) := by
    cases endpoint with
    | start =>
        simpa [SegmentTerminal.drawingPoint,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          Cell.add, Cell.scale] using endpointBounds.1
    | finish =>
        simpa [SegmentTerminal.drawingPoint,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          Cell.add, Cell.scale] using endpointBounds.2
  have localBounds :=
    segmentTerminalLocalPosition_in_macrocell
      indexed.segment endpoint
  let period : Int :=
    planarMacroScale *
      drawingGridSize (PeriodicCNF.incidenceGraph formula)
  have periodPositive : 0 < period := by
    dsimp [period]
    have sizePositive :
        (0 : Int) <
          drawingGridSize (PeriodicCNF.incidenceGraph formula) := by
      exact_mod_cast
        drawingGridSize_pos (PeriodicCNF.incidenceGraph formula)
    exact mul_pos (by norm_num [planarMacroScale]) sizePositive
  have positionBounds :
      -period <
          (drawingPeriodicPlanarSATVariablePosition formula
            (.terminal indexed endpoint)).1 ∧
        (drawingPeriodicPlanarSATVariablePosition formula
            (.terminal indexed endpoint)).1 <
          2 * period ∧
        -period <
          (drawingPeriodicPlanarSATVariablePosition formula
            (.terminal indexed endpoint)).2 ∧
        (drawingPeriodicPlanarSATVariablePosition formula
            (.terminal indexed endpoint)).2 <
          2 * period := by
    rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
    simp only [periodicPlanarSATVariableDrawingPoint,
      periodicPlanarSATVariableLocalPosition,
      Cell.add, Cell.scale]
    dsimp [InExpandedDrawingSquare] at drawingPointBounds
    dsimp [period, planarMacroScale] at periodPositive ⊢
    norm_num [planarMacroScale] at localBounds
    rcases drawingPointBounds with
      ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
    omega
  have horizontal :=
    coordinatePeriodQuotient_isNeighbor
      periodPositive positionBounds.1 positionBounds.2.1
  have vertical :=
    coordinatePeriodQuotient_isNeighbor
      periodPositive positionBounds.2.2.1 positionBounds.2.2.2
  simpa [retainedDrawingWrappedPeriodicPlanarSATVariableGauge,
    PeriodicVariablePlacement.canonicalPositionGauge,
    wrappedDrawingPeriodicPlanarSATPlacement,
    drawingPeriodicPlanarSATPlacement,
    period, IsNeighborTranslation, planarMacroScale] using
      And.intro horizontal vertical

/-- The inverse of a neighboring cell translation is neighboring. -/
theorem IsNeighborTranslation.neg
    {translate : Cell}
    (neighbor : IsNeighborTranslation translate) :
    IsNeighborTranslation (Cell.neg translate) := by
  rcases translate with ⟨horizontal, vertical⟩
  rcases neighbor with
    ⟨horizontalNeighbor, verticalNeighbor⟩
  rcases horizontalNeighbor with rfl | rfl | rfl <;>
    rcases verticalNeighbor with rfl | rfl | rfl <;>
    simp [Cell.neg, Cell.sub, IsNeighborTranslation]

/-- A finite retained representative placed at the canonically gauged
physical position of a periodic variable. -/
def periodicPlanarSATVariableGaugeLift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    PlanarSATVariable Variable :=
  match atom with
  | .terminal indexed endpoint =>
      .inl (.carrier (.terminal
        ⟨indexed,
          Cell.neg
            ((drawingPeriodicPlanarSATPlacement
              formula).canonicalPositionGauge atom),
          endpoint⟩))
  | .boundary boundary =>
      periodicPlanarSATVariableZeroLift (.boundary boundary)
  | .atom sourceAtom =>
      periodicPlanarSATVariableZeroLift (.atom sourceAtom)
  | .crossoverInternal internal =>
      periodicPlanarSATVariableZeroLift
        (.crossoverInternal internal)

/-- Every valid periodic variable's gauge lift belongs to the retained
finite variable set. -/
theorem periodicPlanarSATVariableGaugeLift_valid
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
    RetainedDrawingPlanarSATVariableValid formula
      (periodicPlanarSATVariableGaugeLift formula atom) := by
  cases atom with
  | terminal indexed endpoint =>
      change
        CarrierNode.terminal
            ⟨indexed,
              Cell.neg
                ((drawingPeriodicPlanarSATPlacement
                  formula).canonicalPositionGauge
                    (.terminal indexed endpoint)),
              endpoint⟩ ∈
          retainedDrawingCarrierNodes
            (PeriodicCNF.incidenceGraph formula)
      unfold retainedDrawingCarrierNodes
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨_, ?_, rfl⟩
      apply
        mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
      · exact valid
      · exact
          (retainedDrawingWrappedPeriodicPlanarSATVariableGauge_terminal_isNeighbor
            formula wellFormed degree isLocal indexed endpoint valid).neg
  | boundary boundary =>
      exact
        retainedDrawingPeriodicPlanarSATVariableValid_zeroLift
          formula (.boundary boundary) valid
  | atom sourceAtom =>
      exact
        retainedDrawingPeriodicPlanarSATVariableValid_zeroLift
          formula (.atom sourceAtom) valid
  | crossoverInternal internal =>
      exact
        retainedDrawingPeriodicPlanarSATVariableValid_zeroLift
          formula (.crossoverInternal internal) valid

/-- Wrapping a variable does not change its canonical position gauge. -/
@[simp]
theorem wrappedDrawingPeriodicPlanarSATPlacement_canonicalPositionGauge_mk
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    (wrappedDrawingPeriodicPlanarSATPlacement
      formula).canonicalPositionGauge ⟨atom⟩ =
      (drawingPeriodicPlanarSATPlacement
        formula).canonicalPositionGauge atom := rfl

/-- The gauged wrapped position is definitionally the corresponding
unwrapped gauged position. -/
@[simp]
theorem retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_mk
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (atom : PeriodicPlanarSATVariable Variable) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).position ⟨atom⟩ =
      ((drawingPeriodicPlanarSATPlacement formula).variableGauge
        (drawingPeriodicPlanarSATPlacement
          formula).canonicalPositionGauge).position atom := rfl

/-- The finite gauge lift is drawn exactly at the gauged periodic
prototype position. -/
theorem drawingPlanarSATVariablePosition_gaugeLift
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (atom : PeriodicPlanarSATVariable Variable)
    (valid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula atom) :
    drawingPlanarSATVariablePosition formula
        (periodicPlanarSATVariableGaugeLift formula atom) =
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).position ⟨atom⟩ := by
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_mk]
  cases atom with
  | terminal indexed endpoint =>
      rw [show
        drawingPlanarSATVariablePosition formula
            (periodicPlanarSATVariableGaugeLift formula
              (.terminal indexed endpoint)) =
          SegmentTerminal.position
            (PeriodicCNF.incidenceGraph formula)
              ⟨indexed,
                Cell.neg
                  ((drawingPeriodicPlanarSATPlacement
                    formula).canonicalPositionGauge
                      (.terminal indexed endpoint)),
                endpoint⟩ by rfl]
      rw [SegmentTerminal.position_translate]
      apply Prod.ext <;>
        simp [PeriodicVariablePlacement.variableGauge,
          drawingPeriodicPlanarSATPlacement,
          drawingPeriodicPlanarSATVariablePosition,
          PeriodicVariablePlacement.translation,
          Cell.neg, Cell.add, Cell.sub, Cell.scale,
          planarMacroScale] <;>
        ring
  | boundary boundary =>
      have gaugeZero :=
        retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
          formula wellFormed (.boundary boundary) valid
            (by intro indexed endpoint unequal; cases unequal)
      simp [periodicPlanarSATVariableGaugeLift,
        drawingPlanarSATVariablePosition_zeroLift,
        PeriodicVariablePlacement.variableGauge,
        gaugeZero, PeriodicVariablePlacement.translation,
        Cell.sub, Cell.scale]
      rfl
  | atom sourceAtom =>
      have gaugeZero :=
        retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
          formula wellFormed (.atom sourceAtom) valid
            (by intro indexed endpoint unequal; cases unequal)
      simp [periodicPlanarSATVariableGaugeLift,
        drawingPlanarSATVariablePosition_zeroLift,
        PeriodicVariablePlacement.variableGauge,
        gaugeZero, PeriodicVariablePlacement.translation,
        Cell.sub, Cell.scale]
      rfl
  | crossoverInternal internal =>
      have gaugeZero :=
        retainedDrawingPeriodicPlanarSATVariableGauge_eq_zero_of_nonterminal
          formula wellFormed (.crossoverInternal internal) valid
            (by intro indexed endpoint unequal; cases unequal)
      simp [periodicPlanarSATVariableGaugeLift,
        drawingPlanarSATVariablePosition_zeroLift,
        PeriodicVariablePlacement.variableGauge,
        gaugeZero, PeriodicVariablePlacement.translation,
        Cell.sub, Cell.scale]
      rfl

/-- Distinct periodic prototypes have distinct finite gauge lifts. -/
theorem periodicPlanarSATVariableGaugeLift_injective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    Function.Injective
      (periodicPlanarSATVariableGaugeLift formula) := by
  intro first second equal
  cases first <;> cases second <;>
    simp_all [periodicPlanarSATVariableGaugeLift,
      periodicPlanarSATVariableZeroLift]

/-- Gauged positions identify valid wrapped periodic prototypes. -/
theorem
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_injective_of_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {first second : WrappedPeriodicPlanarSATVariable Variable}
    (firstValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula first.original)
    (secondValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula second.original)
    (positionEq :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).position first =
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).position second) :
    first = second := by
  have liftEq :
      periodicPlanarSATVariableGaugeLift formula first.original =
        periodicPlanarSATVariableGaugeLift formula second.original := by
    apply drawingPlanarSATVariable_eq_of_valid_of_position_eq
      formula wellFormed degree isLocal
    · exact periodicPlanarSATVariableGaugeLift_valid
        formula wellFormed degree isLocal first.original firstValid
    · exact periodicPlanarSATVariableGaugeLift_valid
        formula wellFormed degree isLocal second.original secondValid
    · rw [drawingPlanarSATVariablePosition_gaugeLift
          formula wellFormed first.original firstValid,
        drawingPlanarSATVariablePosition_gaugeLift
          formula wellFormed second.original secondValid]
      exact positionEq
  have originalEq :=
    periodicPlanarSATVariableGaugeLift_injective formula liftEq
  cases first
  cases second
  simpa using originalEq

/-- Every variable surviving gauge, anchor normalization, and clause
deduplication remains geometrically valid. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {atom : WrappedPeriodicPlanarSATVariable Variable}
    (atomMem :
      atom ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.variableOccurrences) :
    RetainedDrawingPeriodicPlanarSATVariableValid
      formula atom.original := by
  let normalizedSource :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  have normalizedMem :
      atom ∈ normalizedSource.erase.variableOccurrences := by
    have deduplicatedMem :
        atom ∈ normalizedSource.erase.deduplicate.variableOccurrences := by
      simpa [normalizedSource,
        retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
        PositionedPeriodicCNF.erase_deduplicateByLiterals] using atomMem
    exact
      (PeriodicCNF.deduplicate_variableOccurrences_sublist
        normalizedSource.erase).subset deduplicatedMem
  have gaugedMem :
      atom ∈
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.variableOccurrences := by
    simpa [normalizedSource,
      retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using normalizedMem
  have wrappedMem :
      atom ∈
        (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.variableOccurrences := by
    rw [retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
      PositionedPeriodicCNF.erase_variableGauge,
      PeriodicCNF.variableOccurrences_variableGauge] at gaugedMem
    exact gaugedMem
  have unwrappedMem :
      atom.original ∈
        (retainedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.variableOccurrences := by
    rw [retainedWrappedDrawingPositionedPeriodicPlanarSATFormula,
      PositionedPeriodicCNF.variableOccurrences_erase_rename] at wrappedMem
    rcases List.mem_map.mp wrappedMem with
      ⟨original, originalMem, atomEq⟩
    exact
      (congrArg WrappedPeriodicVariable.original atomEq).symm ▸
        originalMem
  rw [retainedDrawingPositionedPeriodicPlanarSATFormula_erase]
    at unwrappedMem
  exact
    retainedDrawingPeriodicPlanarSATFormula_variableOccurrences_valid
      formula wellFormed degree isLocal unwrappedMem

/-- The variable-position prefix of the final gauged incidence drawing has
no repeated points. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variablePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase.incidenceVariableVertices.map fun vertex =>
      match vertex with
      | .variable atom =>
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).position atom
      | .clause _ => (0, 0)).Nodup := by
  rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
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

/-- Every position in the final gauged variable prefix lies strictly inside
the refined fundamental square. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variablePositions_inSquare
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (position : Cell)
    (positionMem :
      position ∈
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase.incidenceVariableVertices.map fun vertex =>
          match vertex with
          | .variable atom =>
              (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
                formula).position atom
          | .clause _ => (0, 0))) :
    0 < position.1 ∧
      position.1 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period ∧
      0 < position.2 ∧
      position.2 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
  rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
    at positionMem
  rcases List.mem_map.mp positionMem with
    ⟨atom, _atomMem, positionEq⟩
  rw [← positionEq]
  exact
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula atom

end LeanTrominoes.PeriodicOrthocrossing
