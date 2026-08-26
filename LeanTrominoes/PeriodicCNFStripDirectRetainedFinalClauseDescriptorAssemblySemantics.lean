/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseDescriptorAssemblyData
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalFallbackClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryListSemantics

/-! # Family decomposition of the evaluated final descriptor assembly -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDescriptorAssemblySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- After evaluating the five query families, only crossover,
routed-clause, and routed-variable directions remain to be identified; the
carrier and bend families are already their final metadata descriptors. -/
theorem directRetainedFinalClauseDescriptorAssembly_eq_families
    (symbols : List encoding.Γ) :
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
                  decider symbols) := by
  unfold directRetainedFinalClauseDescriptorAssembly
    directRetainedFinalClauseQueryAssembly
    directRetainedFinalCarrierClauseQuerySuffix
    directRetainedFinalBendClauseQuerySuffix
    directRetainedFinalRoutedClauseQuerySuffix
  simp only [retainedFinalCopiedClauseDescriptors_append,
    directRetainedFinalCarrierClauseQueryDescriptors_eq,
    directRetainedFinalBendClauseQueryDescriptors_eq,
    List.append_assoc]

end LeanTrominoes.PeriodicCNFStripReduction

end
