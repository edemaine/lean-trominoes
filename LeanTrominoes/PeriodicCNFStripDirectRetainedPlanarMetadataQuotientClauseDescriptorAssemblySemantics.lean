/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorQuotient
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientClauseDescriptorAssemblyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataQuotientFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceNormalizedFormula
import LeanTrominoes.PeriodicThreeSATThreeClauseDescriptorQuotient

/-! # Semantics of the direct quotiented descriptor assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directQuotientAssemblySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directQuotientAssemblySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct polynomial-time quotient assembly is exactly the complete
public clause-descriptor quotient of the generated occurrence-split source. -/
theorem directRetainedPlanarMetadataQuotientClauseDescriptorAssembly_eq_quotient
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataQuotientClauseDescriptorAssembly
        decider symbols =
      PeriodicThreeSATThree.clauseDescriptorQuotient
        (PeriodicThreeCNF.formula
          (PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  let source := PeriodicThreeCNF.formula
    (PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceEq : directSourceFormula decider symbols =
      PeriodicThreeSATThree.formula source := by
    simpa only [source] using
      directSourceFormula_eq_threeSATThree decider symbols
  have crossoverEq :
      directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
          decider symbols =
        (List.replicate
          (orientedCrossings
            (PeriodicThreeSATThree.formula source).incidenceGraph).length
          FormulaShapeCrossoverDirection.descriptors).flatten := by
    unfold directRetainedPlanarMetadataFixedCrossoverClauseDescriptors
    rw [sourceEq]
  have carrierEq :
      directRetainedPlanarMetadataCarrierClauseDescriptors decider symbols =
        carrierMetadataClauseDescriptors
          (PeriodicThreeSATThree.formula source) := by
    unfold directRetainedPlanarMetadataCarrierClauseDescriptors
    exact congrArg
      (fun formula : PeriodicCNF Variable =>
        carrierMetadataClauseDescriptors formula) sourceEq
  have bendEq :
      directRetainedPlanarMetadataBaseBendClauseDescriptors decider symbols =
        baseBendClauseDescriptors
          (PeriodicThreeSATThree.formula source) :=
    (directRetainedPlanarMetadataBaseBendClauseDescriptors_eq_base
      decider symbols).trans (congrArg baseBendClauseDescriptors sourceEq)
  have routedEq :
      directRetainedPlanarMetadataBaseRoutedClauseDescriptors decider symbols =
        baseRoutedClauseDescriptors
          (PeriodicThreeSATThree.formula source) :=
    (directRetainedPlanarMetadataBaseRoutedClauseDescriptors_eq_base
      decider symbols).trans (congrArg baseRoutedClauseDescriptors sourceEq)
  have routedVariableEq :
      directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
          decider symbols =
        (List.range (PeriodicCNF.presentationLiteralCount source)).flatMap
          (fun _targetIndex => routedVariableFullSiteBlock) := by
    simpa only [source] using
      directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors_eq_fullSites
        decider symbols
  change directRetainedPlanarMetadataQuotientClauseDescriptorAssembly
      decider symbols =
    PeriodicThreeSATThree.clauseDescriptorQuotient source
  calc
    directRetainedPlanarMetadataQuotientClauseDescriptorAssembly
          decider symbols =
        PeriodicThreeSATThree.clauseDescriptorQuotientWith source
          directQuotientAssemblySemanticsVariableDecidableEq := by
      unfold directRetainedPlanarMetadataQuotientClauseDescriptorAssembly
        directRetainedPlanarMetadataQuotientCarrierClauseDescriptorSuffix
        directRetainedPlanarMetadataQuotientBendClauseDescriptorSuffix
        directRetainedPlanarMetadataQuotientRoutedClauseDescriptorSuffix
        PeriodicThreeSATThree.clauseDescriptorQuotientWith
        PeriodicThreeSATThree.nonCrossoverDescriptorQuotientWith
      let append := fun first second :
          List FormulaShapeDirectionOrdering.Token => first ++ second
      have routedTailEq := congrArg₂ append routedEq routedVariableEq
      have bendTailEq := congrArg₂ append bendEq routedTailEq
      have carrierTailEq := congrArg₂ append carrierEq bendTailEq
      exact congrArg₂ append crossoverEq carrierTailEq
    _ = PeriodicThreeSATThree.clauseDescriptorQuotient source := by
      unfold PeriodicThreeSATThree.clauseDescriptorQuotient
      exact PeriodicThreeSATThree.clauseDescriptorQuotientWith_eq
        source _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
