import LeanTrominoes.PeriodicCNFPlanarRetainedEightOccurrenceSplitComputability
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedComputability
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicizationComputability

/-!
# Computability of the positioned retained fixed-eight split

The retained, gauged planar-SAT presentation supplies computable clause
positions, variable positions, and angular ports.  Applying the generic
positioned fixed-eight compiler therefore computes both the exact positioned
split formula and the finite queries of its companion placement.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1200000

private theorem retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun formula : PeriodicCNF Variable =>
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).period := by
  change Primrec fun formula : PeriodicCNF Variable =>
    planarMacroScale.toNat *
      drawingGridSize (PeriodicCNF.incidenceGraph formula)
  exact Primrec.nat_mul.comp
    (Primrec.const planarMacroScale.toNat)
    (drawingGridSize_primrec.comp PeriodicCNF.incidenceGraph_primrec)

private theorem
    retainedGaugedWrappedDrawingPeriodicPlanarSATPosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        WrappedPeriodicPlanarSATVariable Variable =>
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        input.1).position input.2 := by
  have original : Primrec fun input : PeriodicCNF Variable ×
      WrappedPeriodicPlanarSATVariable Variable =>
      (wrappedDrawingPeriodicPlanarSATPlacement input.1).position input.2 :=
    wrappedDrawingPeriodicPlanarSATVariablePosition_primrec
  have gauge : Primrec fun input : PeriodicCNF Variable ×
      WrappedPeriodicPlanarSATVariable Variable =>
      retainedDrawingWrappedPeriodicPlanarSATVariableGauge
        input.1 input.2 :=
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge_primrec
  have translation : Primrec fun input : PeriodicCNF Variable ×
      WrappedPeriodicPlanarSATVariable Variable =>
      Cell.scale
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          input.1).period : Int)
        (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
          input.1 input.2) :=
    Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec.comp
          Primrec.fst))
      gauge
  exact (Computability.cell_sub_primrec.comp original translation).of_eq
    fun _ => rfl

theorem retainedDrawingEightOccurrenceSplitPositionedFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDrawingEightOccurrenceSplitPositionedFormula :
      PeriodicCNF Variable → _) := by
  unfold retainedDrawingEightOccurrenceSplitPositionedFormula
  exact PeriodicEightOccurrenceSplitPositioned.formula_primrec
    (Input := PeriodicCNF Variable)
    (Variable := WrappedPeriodicPlanarSATVariable Variable)
    (source :=
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula)
    (sourcePlacement :=
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement)
    (occurrencePorts := retainedDrawingAngularOccurrencePorts)
    (sourcePrimrec :=
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec)
    (positionPrimrec :=
      retainedGaugedWrappedDrawingPeriodicPlanarSATPosition_primrec)
    (portsPrimrec := retainedDrawingAngularOccurrencePorts_port_primrec)

theorem retainedDrawingEightOccurrenceSplitPositionedFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedDrawingEightOccurrenceSplitPositionedFormula :
      PeriodicCNF Variable → _) :=
  retainedDrawingEightOccurrenceSplitPositionedFormula_primrec.to_comp

theorem retainedDrawingEightOccurrenceSplitPlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun formula : PeriodicCNF Variable =>
      (retainedDrawingEightOccurrenceSplitPlacement formula).period := by
  unfold retainedDrawingEightOccurrenceSplitPlacement
  exact PeriodicEightOccurrenceSplitPositioned.placement_period_primrec
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
    retainedGaugedWrappedDrawingPeriodicPlanarSATPeriod_primrec

theorem retainedDrawingEightOccurrenceSplitPlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable) =>
      (retainedDrawingEightOccurrenceSplitPlacement
        input.1).position input.2 := by
  unfold retainedDrawingEightOccurrenceSplitPlacement
  exact PeriodicEightOccurrenceSplitPositioned.placement_position_primrec
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
    retainedGaugedWrappedDrawingPeriodicPlanarSATPosition_primrec

end PeriodicOrthocrossing
end LeanTrominoes
