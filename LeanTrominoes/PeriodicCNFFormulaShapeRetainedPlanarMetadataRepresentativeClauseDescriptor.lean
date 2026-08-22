/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRouteLookup

/-! # Individual representative metadata clause descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

theorem clauseToken_eq_representativeClauseDescriptor_of_lookup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause : PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex : Nat)
    (clauseLookup :
      (deduplicatedClauses source)[clauseIndex]? = some clause) :
    FormulaShapeDirectionOrdering.Token.clause
        (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
          (rawRepresentativeRoute source) clauseIndex ⟨(0, 0), clause⟩) =
      representativeClauseDescriptor source clause := by
  apply congrArg FormulaShapeDirectionOrdering.Token.clause
  unfold FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
    FormulaShapeDirectionOrdering.annotatedLiterals
  apply congrArg FormulaShapeDirectionOrdering.DirectedClauseProfile.ofList
  apply List.map_congr_left
  intro taggedLiteral _taggedLiteralMember
  apply Prod.ext
  · rfl
  · rw [rawRepresentativeRoute_eq_of_clauseLookup
      source clause clauseIndex taggedLiteral.2 clauseLookup]

theorem rawIndexedClauseDescriptor_eq_representative_of_lookup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedClause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (clauseLookup :
      (deduplicatedClauses source)[taggedClause.2]? =
        some taggedClause.1) :
    rawIndexedClauseDescriptor source taggedClause =
      representativeClauseDescriptor source taggedClause.1 := by
  rcases taggedClause with ⟨clause, clauseIndex⟩
  exact clauseToken_eq_representativeClauseDescriptor_of_lookup
    source clause clauseIndex clauseLookup

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
