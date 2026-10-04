/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteProgramNormalizationFacts
import LeanTrominoes.FiniteTrominoCompletionInNP
import LeanTrominoes.FiniteDrawingCompletion
import LeanTrominoes.FiniteShiftedSparseModel

/-! # The finite completion instance of a zero-offset program source -/
noncomputable section
namespace LeanTrominoes.FiniteProgramCompletion
open Gadget PeriodicCNF PeriodicCNFStripReduction CompletionPattern CompletionPattern.Runtime
open FiniteProgramSparseTrominoRegion
attribute [local instance] variableDecidableEq variableBEq
variable {Source : Type} {encoding : _root_.Computability.FinEncoding Source} {language : Source → Prop}
variable (source : ProgramSource encoding language)
variable (zero : ∀ symbols,FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))

def drawing (symbols : List encoding.Γ) : PeriodicOrthogonalDrawing :=
  (presentation (source.formulaOfSymbols symbols)).finiteNormalizedDrawing
    (problemZero source zero symbols) (endpointBounds source symbols)

theorem drawing_facts (symbols : List encoding.Γ) :
    (drawing source zero symbols).IsWellFormed ∧ (drawing source zero symbols).VerticesSeparated ∧
    (drawing source zero symbols).BlankBoundary ∧
    ((drawing source zero symbols).HasOrientation ↔ (problem (source.formulaOfSymbols symbols)).FiniteSatisfiable) :=
  (presentation (source.formulaOfSymbols symbols)).finiteNormalizedDrawing_correct
    (presentation (source.formulaOfSymbols symbols)).problemWellFormed (problem_degreeTwoOrThree _)
    (problemZero source zero symbols) (endpointBounds source symbols)
    (presentation_separated _) (presentation_routesSimple _)

def prefillOfSymbols (t : Tromino) (symbols : List encoding.Γ) : List (Placement Unit) :=
  finiteDrawingPrefill (drawing source zero symbols) t

def prefill (t : Tromino) (input : Source) : List (Placement Unit) :=
  prefillOfSymbols source zero t (encoding.encode input)

theorem correct (t : Tromino) (input : Source) :
    language input ↔ t.Completable Set.univ
      ((Tromino.FiniteCoordinateColumns.completionFootprints t (prefill source zero t input)).toFinset : Set (Finset Cell)) := by
  let symbols := encoding.encode input
  let raw := source.formulaOfSymbols symbols
  have facts := drawing_facts source zero symbols
  have semantic := (source.correct input).trans (sourceFormula_correct raw)
  have finiteCore := (PeriodicOrthocrossing.retainedPlanarThreeDM_finite_satisfiable_iff
    (sourceFormula raw) (sourceFormula_isLocal raw) (sourceFormula_widthAtMostThree raw)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq raw) (sourceFormula_clausesNonempty raw)
    (FiniteProgramTrominoRegion.guardedZero source zero symbols)).symm
  have erase := (FiniteCNF.satisfiable_erase (sourceFormula raw)
    (FiniteProgramTrominoRegion.guardedZero source zero symbols)).symm
  exact ((semantic.trans erase).trans finiteCore).trans (facts.2.2.2.symm.trans
    (finiteDrawingPrefill_correct (drawing source zero symbols) facts.1 facts.2.2.1 t))

theorem sparseModel (symbols : List encoding.Γ) :
    SparseModel (drawing source zero symbols) (assignments source symbols) := by
  unfold assignments
  rw [paddedInputs_eq_presentation source zero,PeriodicThreeDM.NormalizationCompiler.finalStripCellAssignments_inputOfPresentation]
  obtain ⟨nodup,bounds,readback,firstColumn,firstRow⟩ :=
    (presentation (source.formulaOfSymbols symbols)).finitePaddedSparseFacts
      (problemZero source zero symbols) (endpointBounds source symbols)
      (presentation (source.formulaOfSymbols symbols)).problemWellFormed (problem_degreeTwoOrThree _)
      (presentation_separated _) (presentation_routesSimple _)
  exact shiftedSparseModel _ _ nodup bounds readback firstColumn firstRow
end LeanTrominoes.FiniteProgramCompletion
