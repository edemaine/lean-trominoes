/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteProgramTrominoRegion
import LeanTrominoes.FiniteThreeDMSparseRegion
import LeanTrominoes.FiniteNormalizationInputPadding
import LeanTrominoes.GadgetSparseStripCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseVertexRecordDirectBounds

/-! # The finite program-source endpoint in sparse assignment order -/
noncomputable section
namespace LeanTrominoes.FiniteProgramSparseTrominoRegion
open Gadget PeriodicCNF PeriodicCNFStripReduction PeriodicOrthocrossing
open PeriodicThreeDM.NormalizationCompiler
attribute [local instance] variableDecidableEq variableBEq
variable {Source : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Source} {language : Source → Prop}
variable (source : ProgramSource encoding language)
variable (zero : ∀ symbols,FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))

def problemZero (symbols : List encoding.Γ) : (problem (source.formulaOfSymbols symbols)).ZeroOffsets :=
  retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_zeroOffsets
    (sourceFormula (source.formulaOfSymbols symbols)) (sourceFormula_isLocal _)
    (sourceFormula_widthAtMostThree _) (sourceFormula_occurrencesAtMostThree_canonicalBEq _)
    (sourceFormula_clausesNonempty _) (FiniteProgramTrominoRegion.guardedZero source zero symbols)

def endpointBounds (symbols : List encoding.Γ) :
    (presentation (source.formulaOfSymbols symbols)).drawing.SegmentEndpointsInExpandedSquare :=
  retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_endpointBounds
    (sourceFormula (source.formulaOfSymbols symbols)) (sourceFormula_isLocal _)
    (sourceFormula_widthAtMostThree _) (sourceFormula_occurrencesAtMostThree_canonicalBEq _)
    (sourceFormula_clausesNonempty _)

def inputs (symbols : List encoding.Γ) : Input :=
  directSparseComputedNormalizationInputOfSymbols source symbols

def paddedInputs (symbols : List encoding.Γ) : Input :=
  (inputs source symbols).finitePad

def assignments (symbols : List encoding.Γ) : List (Cell × OrthogonalCellType) :=
  (finalStripCellAssignments (paddedInputs source symbols)).map FiniteSparseAssignmentSeamCompiler.shift

def regionOfSymbols (t : Tromino) (symbols : List encoding.Γ) : List Cell :=
  sparseExpandedMotif t (assignments source symbols)

def region (t : Tromino) (input : Source) : List Cell :=
  regionOfSymbols source t (encoding.encode input)

/-- The proof-free padded input is exactly the certified finite presentation's
normalization data. -/
theorem paddedInputs_eq_presentation (symbols : List encoding.Γ) :
    paddedInputs source symbols=inputOfPresentation
      ((presentation (source.formulaOfSymbols symbols)).finitePad
        (problemZero source zero symbols) (endpointBounds source symbols)).toPlanarPresentation := by
  unfold paddedInputs inputs
  rw [directSparseComputedNormalizationInputOfSymbols_eq]
  rfl

/-- The sparse target uses the same finite region carrier as the verified
retained reduction. -/
theorem region_carrier_eq (t : Tromino) (symbols : List encoding.Γ) :
    ((regionOfSymbols source t symbols).toFinset:Set Cell)=
      ((FiniteProgramTrominoRegion.regionOfSymbols source zero t symbols).toFinset:Set Cell) := by
  unfold regionOfSymbols assignments
  rw [paddedInputs_eq_presentation source zero,finalStripCellAssignments_inputOfPresentation]
  change (((presentation (source.formulaOfSymbols symbols)).finiteSparseRegion
    (problemZero source zero symbols) (endpointBounds source symbols) t).toFinset:Set Cell)=_
  exact (presentation (source.formulaOfSymbols symbols)).finiteSparseRegion_carrier_eq
    (problemZero source zero symbols) (endpointBounds source symbols)
    (presentation (source.formulaOfSymbols symbols)).problemWellFormed
    (problem_degreeTwoOrThree _) (presentation_separated _) (presentation_routesSimple _) t

include zero in
theorem correct (t : Tromino) (input : Source) :
    language input ↔ t.Tileable ((region source t input).toFinset:Set Cell) := by
  unfold region
  rw [region_carrier_eq source zero]
  exact FiniteProgramTrominoRegion.correct source zero t input
end LeanTrominoes.FiniteProgramSparseTrominoRegion
