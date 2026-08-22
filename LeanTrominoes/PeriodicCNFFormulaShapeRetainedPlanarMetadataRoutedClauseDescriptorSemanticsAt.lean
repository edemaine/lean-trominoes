/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseDescriptorData

/-! # Pointwise semantics of finite routed source-clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

private theorem map_zipIdx_fst
    {Value Output : Type}
    (values : List Value) (transform : Value → Output) :
    values.zipIdx.map (fun tagged => transform tagged.1) =
      values.map transform := by
  have functionEq :
      (fun tagged : Value × Nat => transform tagged.1) =
        transform ∘ Prod.fst := by
    funext tagged
    rfl
  rw [functionEq]
  simpa only [List.map_map] using
    congrArg (List.map transform) (List.zipIdx_map_fst 0 values)

/-- Every retained routed source clause has exactly the finite token obtained
from its normalized literal profiles; every local route annotation is the
invalid axis fallback. -/
theorem metadataClauseDescriptor_routedClauseMetadataAt_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    metadataClauseDescriptor source
        (routedClauseMetadataAt source site) =
      canonicalRoutedClauseDescriptor source site := by
  unfold metadataClauseDescriptor canonicalRoutedClauseDescriptor
    routedClauseDescriptor
  rw [normalizedClause_routedClauseMetadataAt_eq]
  simp [routedClauseMetadataAt,
    DrawingPlanarSATClauseSource.localClauseIndex,
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause,
    FormulaShapeDirectionOrdering.annotatedLiterals,
    routedClause_routeFirstDirection_eq_invalid source site]
  apply congrArg
    FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  calc
    _ = (normalizedRoutedClauseAt source site).map
          (fun literal =>
            (FormulaShapeDirectionOrdering.literalProfile literal,
              AxisDirection.invalid)) :=
      map_zipIdx_fst _ _
    _ = _ := by
      unfold ClauseProfileOccurrenceSplit.literalProfiles
      rw [List.map_map]
      rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
