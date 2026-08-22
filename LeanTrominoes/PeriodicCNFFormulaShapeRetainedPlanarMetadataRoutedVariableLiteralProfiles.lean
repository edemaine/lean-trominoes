/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableDescriptorData

/-! # Literal profiles of normalized routed-variable clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open UnaryProgramClauseProfile

/-- The literal profiles of a normalized active-arm implication are fixed by
its implication polarity and normalized relative-slice bit. -/
theorem normalizedRoutedVariableClause_literalProfiles_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (forward : Bool) :
    (normalizedClause source
        (routedVariableClauseMetadataAt
          site armIndex arm link forward)).map
        FormulaShapeDirectionOrdering.literalProfile =
      if forward then
        [(⟨false, true⟩ : LiteralProfile),
          ⟨routedVariableLinkNextSlice source link, false⟩]
      else
        [(⟨false, false⟩ : LiteralProfile),
          ⟨routedVariableLinkNextSlice source link, true⟩] := by
  rw [normalizedClause_routedVariableClauseMetadataAt_eq]
  cases forward <;>
    simp [PeriodicEquality.normalizedClause,
      routedVariableLinkNextSlice,
      FormulaShapeDirectionOrdering.literalProfile]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
