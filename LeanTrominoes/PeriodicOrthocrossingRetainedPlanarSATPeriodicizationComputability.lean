/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarPeriodicizationComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedCertificate
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariableGauge
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

private def periodicTerminalPosition
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable ×
      (IndexedGridSegment × SegmentEnd)) : Cell :=
  SegmentTerminal.position (PeriodicCNF.incidenceGraph input.1)
    ⟨input.2.1, (0, 0), input.2.2⟩

private theorem periodicTerminalPosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (periodicTerminalPosition (Variable := Variable)) := by
  have graph : Primrec fun input : PeriodicCNF Variable ×
      (IndexedGridSegment × SegmentEnd) =>
      PeriodicCNF.incidenceGraph input.1 :=
    PeriodicCNF.incidenceGraph_primrec.comp Primrec.fst
  have terminal : Primrec fun input : PeriodicCNF Variable ×
      (IndexedGridSegment × SegmentEnd) =>
      SegmentTerminal.mk input.2.1 (0, 0) input.2.2 :=
    SegmentTerminal.mk_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.const ((0, 0) : Cell)))
        (Primrec.snd.comp Primrec.snd))
  exact (SegmentTerminal.position_primrec.comp graph terminal).of_eq
    fun _ => rfl

private def periodicBoundaryPosition
    {Variable : Type*}
    (input : PeriodicCNF Variable × CrossingBoundary) : Cell :=
  input.2.position

private theorem periodicBoundaryPosition_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (periodicBoundaryPosition (Variable := Variable)) :=
  CrossingBoundary.position_primrec.comp Primrec.snd

private def periodicAtomPosition
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × Variable) : Cell :=
  Cell.add
    (liftedIncidenceVertexMacroOrigin input.1
      (.variable input.2) (0, 0))
    duplicatorArmCenterPosition

private theorem periodicAtomPosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (periodicAtomPosition (Variable := Variable)) := by
  have vertex : Primrec fun input : PeriodicCNF Variable × Variable =>
      (CNFVertex.variable input.2 : CNFVertex Variable) :=
    CNFVertex.variable_primrec.comp Primrec.snd
  have macroInput : Primrec fun input :
      PeriodicCNF Variable × Variable =>
      (((input.1, CNFVertex.variable input.2), (0, 0)) :
        (PeriodicCNF Variable × CNFVertex Variable) × Cell) :=
    Primrec.pair
      (Primrec.pair Primrec.fst vertex)
      (Primrec.const ((0, 0) : Cell))
  exact (Computability.cell_add_primrec.comp
    (liftedIncidenceVertexMacroOrigin_primrec.comp macroInput)
    (Primrec.const duplicatorArmCenterPosition)).of_eq fun _ => rfl

private def periodicInternalPosition
    {Variable : Type*}
    (input : PeriodicCNF Variable ×
      (CrossingRecord × CrossoverInternal)) : Cell :=
  Cell.add (crossingMacroOrigin input.2.1)
    (CrossoverVariable.position
      (crossoverInternalVariable input.2.2))

private theorem periodicInternalPosition_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (periodicInternalPosition (Variable := Variable)) := by
  have localPosition : Primrec fun internal : CrossoverInternal =>
      CrossoverVariable.position
        (crossoverInternalVariable internal) :=
    Primrec.dom_finite _
  exact (Computability.cell_add_primrec.comp
    (crossingMacroOrigin_primrec.comp
      (Primrec.fst.comp Primrec.snd))
    (localPosition.comp
      (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

private def periodicAtomOrInternalPosition
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable ×
      (Variable ⊕ (CrossingRecord × CrossoverInternal))) : Cell :=
  match input.2 with
  | .inl atom => periodicAtomPosition (input.1, atom)
  | .inr internal => periodicInternalPosition (input.1, internal)

private theorem periodicAtomOrInternalPosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (periodicAtomOrInternalPosition (Variable := Variable)) := by
  have atom : Primrec₂ fun
      (input : PeriodicCNF Variable ×
        (Variable ⊕ (CrossingRecord × CrossoverInternal)))
      (value : Variable) =>
      periodicAtomPosition (input.1, value) :=
    periodicAtomPosition_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  have internal : Primrec₂ fun
      (input : PeriodicCNF Variable ×
        (Variable ⊕ (CrossingRecord × CrossoverInternal)))
      (value : CrossingRecord × CrossoverInternal) =>
      periodicInternalPosition (input.1, value) :=
    periodicInternalPosition_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  exact (Primrec.sumCasesOn Primrec.snd atom internal).of_eq fun input => by
    rcases input with ⟨formula, value⟩
    cases value <;> rfl

private def periodicBoundaryOrRestPosition
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable ×
      (CrossingBoundary ⊕
        (Variable ⊕ (CrossingRecord × CrossoverInternal)))) : Cell :=
  match input.2 with
  | .inl boundary => periodicBoundaryPosition (input.1, boundary)
  | .inr rest => periodicAtomOrInternalPosition (input.1, rest)

private theorem periodicBoundaryOrRestPosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (periodicBoundaryOrRestPosition (Variable := Variable)) := by
  have boundary : Primrec₂ fun
      (input : PeriodicCNF Variable ×
        (CrossingBoundary ⊕
          (Variable ⊕ (CrossingRecord × CrossoverInternal))))
      (value : CrossingBoundary) =>
      periodicBoundaryPosition (input.1, value) :=
    periodicBoundaryPosition_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  have rest : Primrec₂ fun
      (input : PeriodicCNF Variable ×
        (CrossingBoundary ⊕
          (Variable ⊕ (CrossingRecord × CrossoverInternal))))
      (value : Variable ⊕
        (CrossingRecord × CrossoverInternal)) =>
      periodicAtomOrInternalPosition (input.1, value) :=
    periodicAtomOrInternalPosition_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  exact (Primrec.sumCasesOn Primrec.snd boundary rest).of_eq fun input => by
    rcases input with ⟨formula, value⟩
    cases value <;> rfl

private def periodicVariableDataPosition
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable ×
      ((IndexedGridSegment × SegmentEnd) ⊕
        (CrossingBoundary ⊕
          (Variable ⊕ (CrossingRecord × CrossoverInternal))))) : Cell :=
  match input.2 with
  | .inl terminal => periodicTerminalPosition (input.1, terminal)
  | .inr rest => periodicBoundaryOrRestPosition (input.1, rest)

private theorem periodicVariableDataPosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (periodicVariableDataPosition (Variable := Variable)) := by
  have terminal : Primrec₂ fun
      (input : PeriodicCNF Variable ×
        ((IndexedGridSegment × SegmentEnd) ⊕
          (CrossingBoundary ⊕
            (Variable ⊕ (CrossingRecord × CrossoverInternal)))))
      (value : IndexedGridSegment × SegmentEnd) =>
      periodicTerminalPosition (input.1, value) :=
    periodicTerminalPosition_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  have rest : Primrec₂ fun
      (input : PeriodicCNF Variable ×
        ((IndexedGridSegment × SegmentEnd) ⊕
          (CrossingBoundary ⊕
            (Variable ⊕ (CrossingRecord × CrossoverInternal)))))
      (value : CrossingBoundary ⊕
        (Variable ⊕ (CrossingRecord × CrossoverInternal))) =>
      periodicBoundaryOrRestPosition (input.1, value) :=
    periodicBoundaryOrRestPosition_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  exact (Primrec.sumCasesOn Primrec.snd terminal rest).of_eq fun input => by
    rcases input with ⟨formula, value⟩
    cases value <;> rfl

theorem drawingPeriodicPlanarSATVariablePosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        PeriodicPlanarSATVariable Variable =>
      drawingPeriodicPlanarSATVariablePosition input.1 input.2 := by
  exact (periodicVariableDataPosition_primrec.comp
    (Primrec.pair Primrec.fst
      (PeriodicPlanarSATVariable.equivData_primrec.comp Primrec.snd))).of_eq
        fun input => by
          rcases input with ⟨formula, value⟩
          cases value <;> rfl

theorem wrappedDrawingPeriodicPlanarSATVariablePosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        WrappedPeriodicPlanarSATVariable Variable =>
      (wrappedDrawingPeriodicPlanarSATPlacement input.1).position input.2 :=
  drawingPeriodicPlanarSATVariablePosition_primrec.comp
    (Primrec.pair Primrec.fst
      (WrappedPeriodicVariable.original_primrec.comp Primrec.snd))

theorem retainedDrawingWrappedPeriodicPlanarSATVariableGauge_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        WrappedPeriodicPlanarSATVariable Variable =>
      retainedDrawingWrappedPeriodicPlanarSATVariableGauge
        input.1 input.2 := by
  exact PeriodicVariablePlacement.canonicalPositionGauge_primrec
    (drawingPeriodicPlanarSATPeriod (Variable := Variable))
    (fun formula =>
      (wrappedDrawingPeriodicPlanarSATPlacement formula).position)
    drawingPeriodicPlanarSATPeriod_primrec
    wrappedDrawingPeriodicPlanarSATVariablePosition_primrec

/-- The unwrapped periodic planar-SAT variable gauge underlying the retained
opaque wrapper is primitive recursive. -/
theorem drawingPeriodicPlanarSATVariableGauge_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        PeriodicPlanarSATVariable Variable =>
      (drawingPeriodicPlanarSATPlacement input.1).canonicalPositionGauge
        input.2 := by
  exact PeriodicVariablePlacement.canonicalPositionGauge_primrec
    (drawingPeriodicPlanarSATPeriod (Variable := Variable))
    (fun formula =>
      (drawingPeriodicPlanarSATPlacement formula).position)
    drawingPeriodicPlanarSATPeriod_primrec
    drawingPeriodicPlanarSATVariablePosition_primrec

/-- The unwrapped canonical gauge at the normalized atom of one finite
planar-SAT literal. -/
def drawingPeriodicizedPlanarSATLiteralGauge
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable ×
      (PlanarSATVariable Variable × Bool)) : Cell :=
  (drawingPeriodicPlanarSATPlacement input.1).canonicalPositionGauge
    (periodicizePlanarSATLiteral input.1 input.2).atom

/-- Evaluating that normalized literal gauge is primitive recursive. -/
theorem drawingPeriodicizedPlanarSATLiteralGauge_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingPeriodicizedPlanarSATLiteralGauge
      (Variable := Variable)) := by
  have periodicized : Primrec fun input : PeriodicCNF Variable ×
      (PlanarSATVariable Variable × Bool) =>
      periodicizePlanarSATLiteral input.1 input.2 :=
    periodicizePlanarSATLiteral_primrec
  have gaugeInput : Primrec fun input : PeriodicCNF Variable ×
      (PlanarSATVariable Variable × Bool) =>
      ((input.1, (periodicizePlanarSATLiteral input.1 input.2).atom) :
        PeriodicCNF Variable × PeriodicPlanarSATVariable Variable) :=
    Primrec.pair Primrec.fst
      (PeriodicThreeCNF.literal_atom_primrec.comp periodicized)
  exact (drawingPeriodicPlanarSATVariableGauge_primrec.comp
    gaugeInput).of_eq fun _ => rfl

theorem retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula :
      PeriodicCNF Variable →
        PositionedPeriodicCNF
          (WrappedPeriodicPlanarSATVariable Variable)) :=
  PositionedPeriodicCNF.variableGauge_primrec
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge_primrec

theorem
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula :
        PeriodicCNF Variable →
          PositionedPeriodicCNF
            (WrappedPeriodicPlanarSATVariable Variable)) := by
  have normalized := PositionedPeriodicCNF.anchorNormalize_primrec
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    (drawingPeriodicPlanarSATPeriod (Variable := Variable))
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    drawingPeriodicPlanarSATPeriod_primrec
  exact normalized.of_eq fun _ => rfl

theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula :
        PeriodicCNF Variable →
          PositionedPeriodicCNF
            (WrappedPeriodicPlanarSATVariable Variable)) :=
  PositionedPeriodicCNF.deduplicateByLiterals_primrec
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec

theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula :
        PeriodicCNF Variable →
          PositionedPeriodicCNF
            (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec.to_comp

theorem retainedPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedPlanarSATFormula :
      PeriodicCNF Variable →
        PeriodicCNF (WrappedPeriodicPlanarSATVariable Variable)) :=
  PositionedPeriodicCNF.erase_primrec.comp
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_primrec

theorem retainedPlanarSATFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedPlanarSATFormula :
      PeriodicCNF Variable →
        PeriodicCNF (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedPlanarSATFormula_primrec.to_comp

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
