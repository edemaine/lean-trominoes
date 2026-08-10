import LeanTrominoes.PeriodicCNFPlanarPeriodicizationComputability
import LeanTrominoes.PositionedPeriodicCNFComputability

/-!
# Computability of the retained positioned planar-SAT periodicization

The retained embedded planar-SAT block is converted to positioned periodic
clauses, renamed through the opaque pipeline wrapper, normalized to the
canonical clause-anchor gauge, and reduced to one representative of every
periodic clause orbit by primitive-recursive transformations.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1000000

theorem retainedDrawingPositionedPeriodicPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDrawingPositionedPeriodicPlanarSATFormula :
      PeriodicCNF Variable →
        PositionedPeriodicCNF
          (PeriodicPlanarSATVariable Variable)) := by
  have one : Primrec₂ fun (formula : PeriodicCNF Variable)
      (clause : EmbeddedClause (PlanarSATVariable Variable)) =>
      PositionedPeriodicClause.mk clause.position
        (periodicizePlanarSATClause formula clause) := by
    change Primrec fun input : PeriodicCNF Variable ×
        EmbeddedClause (PlanarSATVariable Variable) =>
      PositionedPeriodicClause.mk input.2.position
        (periodicizePlanarSATClause input.1 input.2)
    exact PositionedPeriodicClause.mk_primrec.comp
      (Primrec.pair
        (EmbeddedClause.position_primrec.comp Primrec.snd)
        (periodicizePlanarSATClause_primrec.comp
          Primrec.fst Primrec.snd))
  have clauses : Primrec fun formula : PeriodicCNF Variable =>
      (retainedDrawingPlanarSATFormula formula).map fun clause =>
        PositionedPeriodicClause.mk clause.position
          (periodicizePlanarSATClause formula clause) :=
    Primrec.list_map retainedDrawingPlanarSATFormula_primrec one
  exact (PositionedPeriodicCNF.mk_primrec.comp clauses).of_eq
    fun _ => rfl

theorem retainedDrawingPositionedPeriodicPlanarSATFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedDrawingPositionedPeriodicPlanarSATFormula :
      PeriodicCNF Variable →
        PositionedPeriodicCNF
          (PeriodicPlanarSATVariable Variable)) :=
  retainedDrawingPositionedPeriodicPlanarSATFormula_primrec.to_comp

theorem retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula :
      PeriodicCNF Variable →
        PositionedPeriodicCNF
          (WrappedPeriodicPlanarSATVariable Variable)) := by
  have variableMap : Primrec fun input : PeriodicCNF Variable ×
      PeriodicPlanarSATVariable Variable =>
      (WrappedPeriodicVariable.mk input.2 :
        WrappedPeriodicPlanarSATVariable Variable) :=
    WrappedPeriodicVariable.mk_primrec.comp Primrec.snd
  exact PositionedPeriodicCNF.rename_primrec
    retainedDrawingPositionedPeriodicPlanarSATFormula
    (fun _ => WrappedPeriodicVariable.mk)
    retainedDrawingPositionedPeriodicPlanarSATFormula_primrec
    variableMap

theorem retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula :
      PeriodicCNF Variable →
        PositionedPeriodicCNF
          (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec.to_comp

private def drawingPeriodicPlanarSATPeriod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Nat :=
  (drawingPeriodicPlanarSATPlacement formula).period

private theorem drawingPeriodicPlanarSATPeriod_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingPeriodicPlanarSATPeriod (Variable := Variable)) := by
  have graph : Primrec fun formula : PeriodicCNF Variable =>
      PeriodicCNF.incidenceGraph formula :=
    PeriodicCNF.incidenceGraph_primrec
  exact (Primrec.nat_mul.comp
    (Primrec.const planarMacroScale.toNat)
    (drawingGridSize_primrec.comp graph)).of_eq fun _ => rfl

theorem
    retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula :
        PeriodicCNF Variable →
          PositionedPeriodicCNF
            (WrappedPeriodicPlanarSATVariable Variable)) := by
  have normalized := PositionedPeriodicCNF.anchorNormalize_primrec
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    (drawingPeriodicPlanarSATPeriod (Variable := Variable))
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    drawingPeriodicPlanarSATPeriod_primrec
  exact normalized.of_eq fun _ => rfl

theorem
    retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable
      (retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula :
        PeriodicCNF Variable →
          PositionedPeriodicCNF
            (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec.to_comp

theorem
    retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula :
        PeriodicCNF Variable →
          PositionedPeriodicCNF
            (WrappedPeriodicPlanarSATVariable Variable)) :=
  PositionedPeriodicCNF.deduplicateByLiterals_primrec
    retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedAnchorNormalizedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec

theorem
    retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable
      (retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula :
        PeriodicCNF Variable →
          PositionedPeriodicCNF
            (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedDeduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes
