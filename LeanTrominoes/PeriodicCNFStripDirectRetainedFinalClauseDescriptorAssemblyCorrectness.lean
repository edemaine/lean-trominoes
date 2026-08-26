/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseDescriptorAssemblySemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedClauseQuerySemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFOccurrencePositiveOffsets
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseDescriptorFiveFamilySemantics

/-! # Correctness of the direct final clause-descriptor assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalAssemblyCorrectnessStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalAssemblyCorrectnessVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The evaluated polynomial-time query assembly is the exact descriptor
stream of the direct source's final copied clauses. -/
theorem directRetainedFinalClauseDescriptorAssembly_eq_finalCopied
    (symbols : List encoding.Γ) :
    directRetainedFinalClauseDescriptorAssembly decider symbols =
      retainedFinalCopiedClauseDescriptors
        (retainedFinalIndexedClauseQueries
          (directSourceFormula decider symbols)) := by
  let original := PolySpaceCompiler.formulaOfSymbols decider symbols
  let source := PeriodicThreeCNF.formula original
  let formula := PeriodicThreeSATThree.formula source
  have sourceLocal : source.IsLocal :=
    PeriodicThreeCNF.formula_isLocal
      (formulaOfSymbols_sourceAdmissible decider symbols).2.1
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
  have sourceEq : directSourceFormula decider symbols = formula := by
    simpa only [formula, source, original] using
      directSourceFormula_eq_threeSATThree decider symbols
  have occurrenceDecidableEqEq :
      directFinalAssemblyCorrectnessVariableDecidableEq =
        (PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq :
          DecidableEq Variable) :=
    Subsingleton.elim _ _
  have crossoverEq :
      directRetainedFinalCrossoverClauseQueries decider symbols =
        (List.replicate
          (orientedCrossings formula.incidenceGraph).length
          retainedFinalDirectCrossoverClauseQueries).flatten := by
    unfold directRetainedFinalCrossoverClauseQueries
    let count := fun retained : PeriodicCNF Variable =>
      (orientedCrossings retained.incidenceGraph).length
    exact congrArg
      (fun crossingCount =>
        (List.replicate crossingCount
          retainedFinalDirectCrossoverClauseQueries).flatten)
      (congrArg count sourceEq)
  have carrierEq :
      directRetainedPlanarMetadataCarrierClauseDescriptors decider symbols =
        carrierMetadataClauseDescriptors formula := by
    unfold directRetainedPlanarMetadataCarrierClauseDescriptors
    let descriptors := fun retained : PeriodicCNF Variable =>
      carrierMetadataClauseDescriptors retained
    exact congrArg descriptors sourceEq
  have bendEq :
      directRetainedPlanarMetadataBaseBendClauseDescriptors decider symbols =
        baseBendClauseDescriptors formula := by
    rw [directRetainedPlanarMetadataBaseBendClauseDescriptors_eq_base]
    let descriptors := fun retained : PeriodicCNF Variable =>
      baseBendClauseDescriptors retained
    exact congrArg descriptors sourceEq
  let emit := fun clause : PeriodicClause Variable =>
    retainedFinalDirectRoutedClauseQuery
      (clause.map fun literal =>
        (⟨false, literal.value⟩ :
          UnaryProgramClauseProfile.LiteralProfile))
  have routedClauseEq :
      directRetainedFinalRoutedClauseQueries decider symbols =
        formula.clauses.map emit := by
    calc
      directRetainedFinalRoutedClauseQueries decider symbols =
          (directSourceFormula decider symbols).clauses.map emit :=
        directRetainedFinalRoutedClauseQueries_eq_sourceClauses
          decider symbols
      _ = formula.clauses.map emit :=
        congrArg (fun retained : PeriodicCNF Variable =>
          retained.clauses.map emit) sourceEq
  have routedVariableEq :
      directRetainedFinalRoutedVariableClauseQueries decider symbols =
        (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
          (fun _targetIndex =>
            retainedFinalDirectRoutedVariableFullSiteQueries) := by
    rfl
  have semanticEq :=
    retainedFinalCopiedClauseDescriptors_formula_eq_fiveFamilies
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
  calc
    directRetainedFinalClauseDescriptorAssembly decider symbols =
        retainedFinalCopiedClauseDescriptors
            (directRetainedFinalCrossoverClauseQueries decider symbols) ++
          directRetainedPlanarMetadataCarrierClauseDescriptors
              decider symbols ++
            directRetainedPlanarMetadataBaseBendClauseDescriptors
                decider symbols ++
              retainedFinalCopiedClauseDescriptors
                  (directRetainedFinalRoutedClauseQueries decider symbols) ++
                retainedFinalCopiedClauseDescriptors
                  (directRetainedFinalRoutedVariableClauseQueries
                    decider symbols) :=
      directRetainedFinalClauseDescriptorAssembly_eq_families
        decider symbols
    _ = retainedFinalCopiedClauseDescriptors
          (retainedFinalIndexedClauseQueries formula) := by
      rw [crossoverEq, carrierEq, bendEq, routedClauseEq,
        routedVariableEq]
      rw [occurrenceDecidableEqEq]
      exact semanticEq.symm
    _ = retainedFinalCopiedClauseDescriptors
          (retainedFinalIndexedClauseQueries
            (directSourceFormula decider symbols)) := by
      rw [sourceEq]

end LeanTrominoes.PeriodicCNFStripReduction

end
