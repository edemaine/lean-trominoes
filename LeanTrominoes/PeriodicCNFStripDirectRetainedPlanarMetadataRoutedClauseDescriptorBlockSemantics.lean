/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataRoutedClauseDescriptorData

/-! # Literal semantics of direct routed-clause descriptor blocks -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

/-- Currentizing the semantic profile of a clause keeps exactly its literal
polarities and clears every slice bit. -/
theorem routedClauseDescriptorBlockOfProfiles_literalProfiles
    {Variable : Type}
    (clause : PeriodicClause Variable) :
    directRetainedPlanarMetadataRoutedClauseDescriptorBlockOfProfiles
        (ClauseProfileOccurrenceSplit.literalProfiles clause) =
      PeriodicOrthocrossing.neighborTranslations.map fun _ =>
        FormulaShapeRetainedPlanarMetadataDirection.routedClauseDescriptor
          (clause.map fun literal =>
            (⟨false, literal.value⟩ : LiteralProfile)) := by
  unfold directRetainedPlanarMetadataRoutedClauseDescriptorBlockOfProfiles
    currentizeRoutedLiteralProfiles
    ClauseProfileOccurrenceSplit.literalProfiles
  rw [List.map_map]
  apply List.map_congr_left
  intro _ _
  congr 2

end LeanTrominoes.PeriodicCNFStripReduction
