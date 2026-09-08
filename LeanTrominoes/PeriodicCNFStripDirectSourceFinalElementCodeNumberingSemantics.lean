/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripTypedElementCodeEncoding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIncidenceElementCodeHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementCodeNodup
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceHorizontalEdgeBlockSemantics

/-! # Actual compiled codes identify the numbered horizontal elements -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Structural code at an actual numbered horizontal element. -/
def directSourceFinalHorizontalElementCode (symbols : List encoding.Γ)
    (element : WireColor × Nat) : Nat :=
  TypedElementCode.encodedElement
    (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase
    (directSourceFinalHorizontalOccurrenceKey decider symbols) element

/-- The complete compiled element column names the numbered elements in their
canonical color-major order. -/
theorem directSourceFinalCanonicalElementCodes_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementCodes decider symbols =
      (CountedContractedIncidence.horizontalElementPairs
        (horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))).map
        (directSourceFinalHorizontalElementCode decider symbols) := by
  rw [directSourceFinalCanonicalElementCodes_eq_horizontalTyped,
    horizontalThreeDMProblemComputed_eq_semantic]
  unfold CountedContractedIncidence.horizontalElementPairs directSourceFinalHorizontalElementCode
  exact (TypedElementCode.encodedElement_map_colorMajor _ _).symm

/-- The compiled incidence column names the element reached by each actual
canonical incidence tag. -/
theorem directSourceFinalCanonicalIncidenceElementCodes_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalIncidenceElementCodes decider symbols =
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.map
        (fun tag => directSourceFinalHorizontalElementCode decider symbols
          ((horizontalThreeDMProblemComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceElement tag)) := by
  rw [directSourceFinalCanonicalIncidenceElementCodes_eq_horizontalTyped,
    horizontalThreeDMProblemComputed_eq_semantic]
  unfold directSourceFinalHorizontalElementCode
  exact (TypedElementCode.incidenceTags_map_encodedElement _ _).symm

/-- Numeric equality in the actual incidence column is equality of its
colored horizontal element, including across distinct colors. -/
theorem directSourceFinalHorizontalIncidenceCode_eq_iff
    (symbols : List encoding.Γ) (element : WireColor × Nat)
    (elementLt : element.2 < (horizontalThreeDMProblemComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).elementCount element.1)
    (tag : IncidenceTag)
    (tagMember : tag ∈ (horizontalThreeDMProblemComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags) :
    directSourceFinalHorizontalElementCode decider symbols
        ((horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceElement tag) =
      directSourceFinalHorizontalElementCode decider symbols element ↔
        (horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceElement tag = element := by
  have unique := directSourceFinalCanonicalElementCodes_nodup decider symbols
  rw [directSourceFinalCanonicalElementCodes_eq_horizontalTyped] at unique
  rw [horizontalThreeDMProblemComputed_eq_semantic] at elementLt tagMember ⊢
  unfold directSourceFinalHorizontalElementCode
  apply TypedElementCode.encodedElement_eq_iff _ _ unique _ _ _ elementLt
  have indexLt := incidenceTag_tripleIndex_lt _ tagMember
  unfold incidenceElement
  dsimp only
  rw [List.getD_eq_getElem _ _ indexLt]
  exact encodedProblem_isWellFormed _ _ (List.getElem_mem indexLt) tag.color

end LeanTrominoes.PeriodicCNFStripReduction

end
