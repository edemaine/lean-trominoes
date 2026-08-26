/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorData

/-! # Data blocks of retained metadata descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- One direction-aware finite token for every deduplicated normalized
metadata clause, in retained presentation order. -/
def clauseDescriptors {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  (positionedSource source).clauses.zipIdx.map fun taggedClause =>
    .clause
      (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        (rawRepresentativeRoute source) taggedClause.2
        taggedClause.1)

/-- Clause descriptors do not depend on the implementation of decidable
equality used while deduplicating the finite metadata presentation. -/
theorem clauseDescriptors_decidableEq_irrel {Variable : Type}
    (source : PeriodicCNF Variable)
    (first second : DecidableEq Variable) :
    @clauseDescriptors Variable first source =
      @clauseDescriptors Variable second source := by
  have implementationEq : first = second := Subsingleton.elim _ _
  subst second
  rfl

/-- Retarget an existing descriptor equality without reconstructing or
normalizing its decidable-equality implementation. -/
theorem eq_clauseDescriptors_of_decidableEq_irrel {Variable : Type}
    {tokens : List FormulaShapeDirectionOrdering.Token}
    (source : PeriodicCNF Variable)
    {first : DecidableEq Variable} (second : DecidableEq Variable)
    (equal : tokens = @clauseDescriptors Variable first source) :
    tokens = @clauseDescriptors Variable second source :=
  equal.trans (clauseDescriptors_decidableEq_irrel source first second)

/-- One finite marker for every distinct variable in the deduplicated
normalized metadata clause list. -/
def variableMarkers {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  List.replicate
    (positionedSource source).erase.variableOccurrences.dedup.length
    .variable

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
