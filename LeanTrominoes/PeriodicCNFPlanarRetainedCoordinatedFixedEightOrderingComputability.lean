import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedComputability
import LeanTrominoes.PositionedPeriodicCNFClauseOrderingComputability
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutesComputability

/-!
# Computability of retained fixed-eight clause ordering

The final retained router supplies an exact primitive-recursive lookup for its
normalized routes.  This module uses their first directions to compute the
first clockwise clause ordering, the extra Figure 9 clearance scale, and the
twice-replaced raw unit-free exact-one formula.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

private abbrev RetainedOrderingVariable (Variable : Type*) :=
  WrappedPeriodicPlanarSATVariable Variable

private def retainedOrderingScaledSource
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF (RetainedOrderingVariable Variable) :=
  (finalCoordinatedSource source).scale
    retainedAngularFanSourceClearanceFactor

private def retainedOrderingScaledPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement (RetainedOrderingVariable Variable) :=
  (finalCoordinatedPlacement source).scale
    retainedAngularFanSourceClearanceFactor

private theorem retainedOrderingScaledSource_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedOrderingScaledSource :
      PeriodicCNF Variable → _) := by
  unfold retainedOrderingScaledSource finalCoordinatedSource
  exact (PositionedPeriodicCNF.scale_primrec
    retainedAngularFanSourceClearanceFactor).comp
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec

private theorem retainedOrderingScaledPlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        RetainedOrderingVariable Variable =>
      (retainedOrderingScaledPlacement input.1).position input.2 := by
  unfold retainedOrderingScaledPlacement finalCoordinatedPlacement
  exact Computability.cell_scale_primrec.comp
    (Primrec.const (retainedAngularFanSourceClearanceFactor : Int))
    retainedGaugedWrappedDrawingPeriodicPlanarSATPosition_primrec

/-- Proof-free construction of the source-scaled fixed-eight positioned
formula, using the equivalent unscaled angular port assignment. -/
private def retainedSourceScaledSplitComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable (RetainedOrderingVariable Variable)) :=
  (PeriodicEightOccurrenceSplitPositioned.formula
    (retainedOrderingScaledSource source)
    (retainedOrderingScaledPlacement source)
    (retainedDrawingAngularOccurrencePorts source)).scale
      retainedTerminalFanRoutingRefinement

private theorem retainedSourceScaledSplitComputed_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedSourceScaledSplitComputed :
      PeriodicCNF Variable → _) := by
  have split : Primrec fun source : PeriodicCNF Variable =>
      PeriodicEightOccurrenceSplitPositioned.formula
        (retainedOrderingScaledSource source)
        (retainedOrderingScaledPlacement source)
        (retainedDrawingAngularOccurrencePorts source) :=
    PeriodicEightOccurrenceSplitPositioned.formula_primrec
      retainedOrderingScaledSource retainedOrderingScaledPlacement
      retainedDrawingAngularOccurrencePorts
      retainedOrderingScaledSource_primrec
      retainedOrderingScaledPlacement_position_primrec
      retainedDrawingAngularOccurrencePorts_port_primrec
  exact (PositionedPeriodicCNF.scale_primrec
    retainedTerminalFanRoutingRefinement).comp split

private theorem retainedSourceScaledSplitComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    retainedSourceScaledSplitComputed source =
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source := by
  unfold retainedSourceScaledSplitComputed
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
    retainedAngularFanSourceScaledRefinedFormula
    retainedAngularFanRefinedFormula
    retainedOrderingScaledSource retainedOrderingScaledPlacement
    finalCoordinatedSource finalCoordinatedPlacement
    retainedDrawingAngularOccurrencePorts
    retainedDrawingAngularOccurrenceOrder retainedPlanarSATFormula
  rw [PositionedPeriodicCNF.erase_scale,
    angularOccurrenceOrder_scaleIncidenceRoutes
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source).erase
    retainedAngularFanSourceClearanceFactor_pos
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source)]

/-- The exact source-scaled positioned fixed-eight formula is primitive
recursive. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula :
        PeriodicCNF Variable → _) :=
  retainedSourceScaledSplitComputed_primrec.of_eq fun source =>
    retainedSourceScaledSplitComputed_eq source

/-- The physical period paired with the source-scaled fixed-eight formula is
primitive recursive. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        source).period := by
  let scaledPlacement := fun source : PeriodicCNF Variable =>
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).scale
      retainedAngularFanSourceClearanceFactor
  have scaledPeriod : Primrec fun source : PeriodicCNF Variable =>
      (scaledPlacement source).period :=
    Primrec.nat_mul.comp
      (Primrec.const retainedAngularFanSourceClearanceFactor)
      retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec
  have splitPeriod : Primrec fun source : PeriodicCNF Variable =>
      (PeriodicEightOccurrenceSplitPositioned.placement
        (scaledPlacement source)).period :=
    PeriodicEightOccurrenceSplitPositioned.placement_period_primrec
      scaledPlacement scaledPeriod
  have computed : Primrec fun source : PeriodicCNF Variable =>
      retainedTerminalFanRoutingRefinement *
        (PeriodicEightOccurrenceSplitPositioned.placement
          (scaledPlacement source)).period :=
    Primrec.nat_mul.comp
      (Primrec.const retainedTerminalFanRoutingRefinement)
      splitPeriod
  exact computed.of_eq fun source => by
    rfl

/-- The reindexed canonical routes paired with the first clockwise clause
ordering have a primitive-recursive presentation-index lookup. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  unfold retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
  exact PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_primrec
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_primrec
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_primrec
    retainedFinalNormalizedRouteQuery_primrec

/-- The first stable clockwise ordering of the normalized retained source is
primitive recursive. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula :
        PeriodicCNF Variable → _) := by
  exact PositionedPeriodicCNF.orderClausesByRouteDirection_primrec
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_primrec
    retainedFinalNormalizedRouteQuery_primrec

/-- The extra whole-source Figure 9 clearance scale is primitive recursive. -/
theorem retainedFigureNineClearancePositionedFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedFigureNineClearancePositionedFormula :
      PeriodicCNF Variable → _) := by
  exact (PositionedPeriodicCNF.scale_primrec
    retainedFigureNineSourceClearanceFactor).comp
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_primrec

/-- The extra Figure 9 source-clearance scale has a primitive-recursive
physical period. -/
theorem retainedFigureNineClearancePlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedFigureNineClearancePlacement source).period := by
  unfold retainedFigureNineClearancePlacement
  exact Primrec.nat_mul.comp
    (Primrec.const retainedFigureNineSourceClearanceFactor)
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_primrec

/-- Scaling and re-normalizing the first clockwise route family preserves a
primitive-recursive presentation-index lookup. -/
theorem retainedFigureNineClearanceIncidenceRoutes_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedFigureNineClearanceIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  have scaled : Primrec fun input :
      (PeriodicCNF Variable × Nat) × Nat =>
      scalePolyline retainedFigureNineSourceClearanceFactor
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
          input.1.1 input.1.2 input.2) :=
    LeanTrominoes.scalePolyline_primrec.comp
      (Primrec.const (retainedFigureNineSourceClearanceFactor : Int))
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_primrec
  exact (AxisDirection.normalizeOrthogonalPolyline_primrec.comp scaled).of_eq
    fun _ => rfl

/-- The twice-replaced raw unit-free exact-one formula after the first
clockwise ordering is primitive recursive. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula :
        PeriodicCNF Variable → _) := by
  exact PeriodicOneInThreeNoUnitsPositioned.formula_primrec.comp
    (PeriodicOneInThreePositioned.formula_primrec.comp
      retainedFigureNineClearancePositionedFormula_primrec)

end PeriodicOrthocrossing
end LeanTrominoes
