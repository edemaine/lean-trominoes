/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientClauseDescriptorAssemblySemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDirectionDescriptorBlockData
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFOccurrencePositiveOffsets

/-! # Correctness of direct quotiented clause descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directQuotientCorrectnessStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The polynomial-time direct quotient assembly is the exact public
clause-descriptor stream of the generated retained source formula. -/
theorem directRetainedPlanarMetadataQuotientClauseDescriptorAssembly_eq_clauseDescriptors
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataQuotientClauseDescriptorAssembly
        decider symbols =
      directRetainedPlanarMetadataClauseDescriptors decider symbols := by
  let original := PolySpaceCompiler.formulaOfSymbols decider symbols
  let source := PeriodicThreeCNF.formula original
  have sourceLocal : source.IsLocal := by
    apply PeriodicThreeCNF.formula_isLocal
    exact (formulaOfSymbols_sourceAdmissible decider symbols).2.1
  have sourceWidth : source.WidthAtMost 3 := by
    exact PeriodicThreeCNF.formula_widthAtMostThree original
  have sourceClausesNonempty : ∀ clause ∈ source.clauses,
      clause ≠ [] := by
    exact PeriodicThreeCNF.formula_clausesNonempty original
      (formulaOfSymbols_clauses_nonempty decider symbols)
  have positiveOffsets :
      ∀ incidence ∈ PeriodicThreeSATThree.occurrenceIncidences source,
        incidence.edge.offset = (0, 0) ∨
          incidence.edge.offset = (1, 0) := by
    simpa only [source, original] using
      directThreeCNFSource_occurrenceIncidences_positiveOffsets
        decider symbols
  have sourceEq : directSourceFormula decider symbols =
      PeriodicThreeSATThree.formula source := by
    simpa only [source, original] using
      directSourceFormula_eq_threeSATThree decider symbols
  calc
    directRetainedPlanarMetadataQuotientClauseDescriptorAssembly
          decider symbols =
        PeriodicThreeSATThree.clauseDescriptorQuotient source := by
      simpa only [source, original] using
        directRetainedPlanarMetadataQuotientClauseDescriptorAssembly_eq_quotient
          decider symbols
    _ = clauseDescriptors (PeriodicThreeSATThree.formula source) :=
      (PeriodicThreeSATThree.clauseDescriptors_formula_eq_quotient
        source sourceLocal sourceWidth sourceClausesNonempty
          positiveOffsets).symm
    _ = clauseDescriptors (directSourceFormula decider symbols) :=
      congrArg clauseDescriptors sourceEq.symm
    _ = directRetainedPlanarMetadataClauseDescriptors decider symbols :=
      eq_directRetainedPlanarMetadataClauseDescriptors_of_eq
        decider symbols rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
