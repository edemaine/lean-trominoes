/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableLiteralProfiles

/-! # Pointwise semantics of finite routed-variable descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Every active routed-variable implication has exactly its finite
duplicator-arm descriptor. -/
theorem metadataClauseDescriptor_routedVariableClauseMetadataAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (forward : Bool) :
    metadataClauseDescriptor source
        (routedVariableClauseMetadataAt
          site armIndex arm link forward) =
      routedVariableClauseDescriptor arm
        (routedVariableLinkNextSlice source link) forward := by
  cases forward
  all_goals
    unfold metadataClauseDescriptor
    rw [normalizedClause_routedVariableClauseMetadataAt_eq]
    simp [routedVariableClauseMetadataAt,
      DrawingPlanarSATClauseSource.localClauseIndex,
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause,
      FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList,
      FormulaShapeDirectionOrdering.annotatedLiterals,
      routedVariableClauseDescriptor,
      PeriodicEquality.normalizedClause,
      routedVariableLinkNextSlice,
      FormulaShapeDirectionOrdering.literalProfile,
      routedVariable_routeFirstDirection_eq
        source site armIndex arm link]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
