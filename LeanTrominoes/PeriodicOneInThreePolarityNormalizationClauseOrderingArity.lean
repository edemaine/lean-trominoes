/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalization
import LeanTrominoes.ListZipIdxMappedZipIdx
import LeanTrominoes.PositionedPeriodicCNFUnitEliminationFinalOrdering

/-! # Clause arities through the final unit-elimination ordering -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalization

/-- The two positions of a binary clause request the same polarity, so
permuting its literals does not change the arity block emitted by polarity
normalization. -/
theorem clauseClauses_lengths_perm_of_length_two
    {Variable : Type} (clauseIndex : Nat)
    (first second : PeriodicLiteral Variable)
    (ordered : PeriodicClause Variable)
    (permutation : ordered.Perm [first, second]) :
    (clauseClauses clauseIndex ordered).map List.length =
      (clauseClauses clauseIndex [first, second]).map List.length := by
  rw [List.perm_pair] at permutation
  rcases permutation with rfl | rfl
  · rfl
  · rcases first with ⟨firstAtom, firstOffset, firstValue⟩
    rcases second with ⟨secondAtom, secondOffset, secondValue⟩
    cases firstValue <;> cases secondValue <;> rfl

/-- Rotating a ternary clause from `0,1,2` to `2,0,1` preserves the
polarity-normalization arity block when its last two polarities agree. -/
theorem clauseClauses_lengths_rotate_three
    {Variable : Type} (clauseIndex : Nat)
    (first second third : PeriodicLiteral Variable)
    (tailValues : second.value = third.value) :
    (clauseClauses clauseIndex [third, first, second]).map List.length =
      (clauseClauses clauseIndex [first, second, third]).map List.length := by
  rcases first with ⟨firstAtom, firstOffset, firstValue⟩
  rcases second with ⟨secondAtom, secondOffset, secondValue⟩
  rcases third with ⟨thirdAtom, thirdOffset, thirdValue⟩
  cases firstValue <;> cases secondValue <;> cases thirdValue <;>
    simp_all [clauseClauses, normalizeClause, normalizeClauseFrom,
      complementClauses, complementClausesFrom, normalizeLiteral,
      normalizedPolarity, liftLiteral, complementLiteral,
      complementClause, complementFalseLiteral, originalFalseLiteral]

/-- Every ternary clause has equal polarities in its final two source
positions.  This is the logical invariant needed by the final geometric
rotation. -/
def TernaryTailValuesEqual {Variable : Type}
    (source : PositionedPeriodicCNF Variable) : Prop :=
  ∀ clause ∈ source.clauses, ∀ first second third,
    clause.literals = [first, second, third] →
      second.value = third.value

/-- A tail-polarity statement about erased clauses lifts directly to the
positioned presentation that carries them. -/
theorem ternaryTailValuesEqual_of_erase
    {Variable : Type} (source : PositionedPeriodicCNF Variable)
    (tailValues :
      ∀ clause ∈ source.erase.clauses, ∀ first second third,
        clause = [first, second, third] →
          second.value = third.value) :
    TernaryTailValuesEqual source := by
  intro clause clauseMember first second third literalsEq
  apply tailValues clause.literals
  · exact List.mem_map.mpr ⟨clause, clauseMember, rfl⟩
  · exact literalsEq

/-- Clause by clause, the final route-direction ordering preserves the
arity block subsequently emitted by polarity normalization. -/
theorem clauseClauses_lengths_orderClauseByRouteDirection
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (routeOrder :
      source.TernaryClauseRoutesInUnitEliminationOrder routes)
    (tailValues : TernaryTailValuesEqual source)
    (clause : PositionedPeriodicClause Variable) (clauseIndex : Nat)
    (clauseMember : (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    (clauseClauses clauseIndex
        (PositionedPeriodicCNF.orderClauseByRouteDirection
          routes clauseIndex clause).literals).map List.length =
      (clauseClauses clauseIndex clause.literals).map List.length := by
  have clauseArity :
      clause.literals.length = 2 ∨ clause.literals.length = 3 := by
    apply arity clause.literals
    exact List.mem_map.mpr
      ⟨clause, List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩
  rcases clauseArity with lengthTwo | lengthThree
  · rcases List.length_eq_two.mp lengthTwo with
      ⟨first, second, literalsEq⟩
    rw [literalsEq]
    apply clauseClauses_lengths_perm_of_length_two
      clauseIndex first second
    simpa only [literalsEq] using
      PositionedPeriodicCNF.orderClauseByRouteDirection_literals_perm
        routes clauseIndex clause
  · rcases List.length_eq_three.mp lengthThree with
      ⟨first, second, third, literalsEq⟩
    rw [PositionedPeriodicCNF.orderClauseByRouteDirection_literals_eq_two_zero_one_of_unitEliminationOrder
      (placement := placement) routeOrder clauseMember literalsEq,
      literalsEq]
    exact clauseClauses_lengths_rotate_three clauseIndex
      first second third
      (tailValues clause
        (List.fst_mem_of_mem_zipIdx clauseMember)
        first second third literalsEq)

/-- Applying polarity normalization after the final route-direction sort has
the same clause-arity sequence as applying it before the sort. -/
theorem formula_clauseLengths_orderClausesByRouteDirection
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (routeOrder :
      source.TernaryClauseRoutesInUnitEliminationOrder routes)
    (tailValues : TernaryTailValuesEqual source) :
    (formula
      (PositionedPeriodicCNF.orderClausesByRouteDirection
        source routes).erase).clauses.map List.length =
      (formula source.erase).clauses.map List.length := by
  unfold formula PositionedPeriodicCNF.orderClausesByRouteDirection
    PositionedPeriodicCNF.erase
  rw [List.map_flatMap, List.map_flatMap]
  simp only [List.map_map, Function.comp_def]
  rw [List.zipIdx_map_zipIdx, List.zipIdx_map]
  rw [List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  exact clauseClauses_lengths_orderClauseByRouteDirection
    source placement routes arity routeOrder tailValues
    clause clauseIndex taggedClauseMember

end PeriodicOneInThreePolarityNormalization
end LeanTrominoes
