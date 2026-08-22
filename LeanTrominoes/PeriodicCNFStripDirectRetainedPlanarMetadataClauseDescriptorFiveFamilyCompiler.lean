/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataClauseDescriptorFamilyCompiler

/-! # Complete five-family retained clause-candidate compiler boundary -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedFiveFamilyCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Five independent family machines, composed only through small binary
append leaves, emit the exact undeduplicated metadata candidates. -/
noncomputable def
    directRetainedPlanarMetadataClauseDescriptorCandidatesComputableInPolyTimeOfFamilies
    (crossover :
      DirectRetainedPlanarMetadataCrossoverClauseDescriptorCompiler decider)
    (carrier :
      DirectRetainedPlanarMetadataCarrierClauseDescriptorCompiler decider)
    (bend :
      DirectRetainedPlanarMetadataBendClauseDescriptorCompiler decider)
    (routedClause :
      DirectRetainedPlanarMetadataRoutedClauseDescriptorCompiler decider)
    (routedVariable :
      DirectRetainedPlanarMetadataRoutedVariableClauseDescriptorCompiler
        decider) :
    DirectRetainedPlanarMetadataClauseDescriptorCandidateCompiler decider :=
  let routed :=
    directRetainedPlanarMetadataRoutedClauseDescriptorSuffixComputableInPolyTime
      decider routedClause routedVariable
  let bent :=
    directRetainedPlanarMetadataBendClauseDescriptorSuffixComputableInPolyTime
      decider bend routed
  let carried :=
    directRetainedPlanarMetadataCarrierClauseDescriptorSuffixComputableInPolyTime
      decider carrier bent
  let assembled :=
    directRetainedPlanarMetadataFamilyClauseDescriptorsComputableInPolyTime
      decider crossover carried
  let family :=
    directRetainedPlanarMetadataFamilyClauseDescriptorCompilerOfAssembled
      decider assembled
  directRetainedPlanarMetadataClauseDescriptorCandidateCompilerOfFamily
    decider family

end LeanTrominoes.PeriodicCNFStripReduction

end
