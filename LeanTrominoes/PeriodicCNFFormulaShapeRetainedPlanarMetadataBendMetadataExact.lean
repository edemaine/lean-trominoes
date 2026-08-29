/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendClauseData

/-! # Exact finite classification of retained bend metadata -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- A metadata record whose source and indexed clause belong to one bend is
exactly one of that bend's two canonical implication records. -/
theorem bendMetadata_eq_forward_or_backward
    {Variable Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (sourceEq : metadata.source = .bend routeBend localClauseIndex)
    (localMember : (metadata.clause, localClauseIndex) ∈
      (drawingPlanarSATBendFormulaAt
        (Variable := Variable) graph routeBend).zipIdx) :
    metadata = bendClauseMetadataAt graph routeBend true ∨
      metadata = bendClauseMetadataAt graph routeBend false := by
  rw [drawingPlanarSATBendFormulaAt_eq_pair] at localMember
  simp only [List.zipIdx_cons, List.mem_cons, Prod.mk.injEq,
    List.zipIdx_nil, List.not_mem_nil, or_false] at localMember
  rcases localMember with localForward | localBackward
  · left
    rcases localForward with ⟨clauseEq, indexEq⟩
    rcases metadata with ⟨metadataClause, metadataSource⟩
    change metadataClause = _ at clauseEq
    change metadataSource = _ at sourceEq
    subst metadataClause
    subst localClauseIndex
    subst metadataSource
    rfl
  · right
    rcases localBackward with ⟨clauseEq, indexEq⟩
    rcases metadata with ⟨metadataClause, metadataSource⟩
    change metadataClause = _ at clauseEq
    change metadataSource = _ at sourceEq
    subst metadataClause
    subst localClauseIndex
    subst metadataSource
    rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
