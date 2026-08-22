/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendDescriptorData

/-! # Literal profiles of normalized retained bend clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- The two literal profiles of a normalized bend implication are fixed by
its implication polarity and normalized relative-slice bit. -/
theorem normalizedBendClause_literalProfiles_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (forward : Bool) :
    (normalizedClause source
        (bendClauseMetadataAt source.incidenceGraph routeBend forward)).map
        FormulaShapeDirectionOrdering.literalProfile =
      if forward then
        [(⟨false, true⟩ : LiteralProfile),
          ⟨bendLinkNextSlice source routeBend, false⟩]
      else
        [(⟨false, false⟩ : LiteralProfile),
          ⟨bendLinkNextSlice source routeBend, true⟩] := by
  rw [normalizedClause_bendClauseMetadataAt_eq]
  cases forward <;>
    simp [PeriodicEquality.normalizedClause,
      bendLinkNextSlice, carrierLinkNextSlice,
      FormulaShapeDirectionOrdering.literalProfile]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
