/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseFamilySemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseSourceProfiles

/-! # Routed clause descriptors in source presentation order -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open UnaryProgramClauseProfile

/-- The complete routed-clause family is nine copies of each source
clause's current-slice polarity profile, in source presentation order. -/
theorem routedClauseMetadataClauseDescriptors_eq_sourceClauses
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed) :
    routedClauseMetadataClauseDescriptors source =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        neighborTranslations.map fun _ =>
          routedClauseDescriptor
            (taggedClause.1.map fun literal =>
              (⟨false, literal.value⟩ : LiteralProfile)) := by
  rw [routedClauseMetadataClauseDescriptors_eq_canonicalDescriptors]
  unfold drawingClauseRouteSites
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedMember
  rw [List.map_map]
  apply List.map_congr_left
  intro translate _
  simp only [Function.comp_apply]
  unfold canonicalRoutedClauseDescriptor
  rw [normalizedRoutedClauseAt_literalProfiles_eq_current
    source wellFormed]
  rw [routedClauseCurrentProfiles_eq_taggedClause
    source taggedClause taggedMember translate]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
