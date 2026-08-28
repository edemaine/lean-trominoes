/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomCodeData
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFOccurrencePositiveOffsets
import LeanTrominoes.PeriodicThreeSATThreeFiveFamilyNormalizedClauses

/-! # Five-family presentation of final direct-source atom codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalAtomFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalAtomFamilyVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Width-three source immediately before the direct occurrence split. -/
def directThreeCNFSourceFormula
    (symbols : List encoding.Γ) :
    PeriodicCNF (ThreeCNFVariable Nat) :=
  PeriodicThreeCNF.formula
    (PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- Exact five-family clause presentation used by the existing quotient
descriptor compiler. -/
def directSourceFinalFiveFamilyClauses
    (symbols : List encoding.Γ) :=
  let source := directThreeCNFSourceFormula decider symbols
  (crossoverMetadataNormalizedClausesDedup
      (PeriodicThreeSATThree.formula source) ++
    PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses source) ++
  ((PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source ++
    PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses source) ++
    PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
      source)

/-- The direct final duplicate-free clause presentation is exactly the same
five-family quotient already used for public descriptors. -/
theorem directSource_deduplicatedClauses_eq_fiveFamilies
    (symbols : List encoding.Γ) :
    deduplicatedClauses (directSourceFormula decider symbols) =
      directSourceFinalFiveFamilyClauses decider symbols := by
  let original := PolySpaceCompiler.formulaOfSymbols decider symbols
  let source := PeriodicThreeCNF.formula original
  have sourceLocal : source.IsLocal := by
    apply PeriodicThreeCNF.formula_isLocal
    exact (formulaOfSymbols_sourceAdmissible decider symbols).2.1
  have sourceWidth : source.WidthAtMost 3 :=
    PeriodicThreeCNF.formula_widthAtMostThree original
  have sourceClausesNonempty : ∀ clause ∈ source.clauses,
      clause ≠ [] :=
    PeriodicThreeCNF.formula_clausesNonempty original
      (formulaOfSymbols_clauses_nonempty decider symbols)
  have positiveOffsets :
      ∀ incidence ∈ PeriodicThreeSATThree.occurrenceIncidences source,
        incidence.edge.offset = (0, 0) ∨
          incidence.edge.offset = (1, 0) := by
    simpa only [source, original] using
      directThreeCNFSource_occurrenceIncidences_positiveOffsets
        decider symbols
  rw [directSourceFormula_eq_threeSATThree]
  change deduplicatedClauses (PeriodicThreeSATThree.formula source) = _
  rw [PeriodicThreeSATThree.deduplicatedClauses_formula_eq_fiveFamilies
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets]
  rfl

/-- Consequently, final atom codes are the literal-wise flattening of the
same five-family quotient, with no extra permutation or selection. -/
theorem directSourceFinalOccurrenceAtomCodes_eq_fiveFamilies
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceAtomCodes decider symbols =
      (directSourceFinalFiveFamilyClauses decider symbols).flatMap
        fun clause => clause.map fun literal =>
          directSourceFinalAtomCode literal.atom := by
  rw [directSourceFinalOccurrenceAtomCodes_eq_deduplicatedClauses]
  rw [directSource_deduplicatedClauses_eq_fiveFamilies]

end PeriodicCNFStripReduction
end LeanTrominoes

end
