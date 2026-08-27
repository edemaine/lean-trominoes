/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordCompiler

/-! # Canonical batches of routed Figure 9 source-tail records -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteTailRecord

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

/-- One canonical source clause without its final delimiter. -/
def clauseBody (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) : List Token :=
  .profile profile :: taggedTailTokens orderedTails

@[simp] theorem clauseRecord_eq_body (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) :
    clauseRecord profile orderedTails =
      clauseBody profile orderedTails ++ [.clauseEnd] := by
  rfl

private theorem tailBlock_continues (sourceSlot : SourceLiteralSlot)
    (directions : List AxisDirection) :
    ∀ token ∈ tailBlock sourceSlot directions,
      isClauseEnd token = false := by
  intro token member
  obtain ⟨direction, _, rfl⟩ := List.mem_map.mp member
  rfl

private theorem taggedTailTokens_continues
    (orderedTails : List (List AxisDirection)) :
    ∀ token ∈ taggedTailTokens orderedTails,
      isClauseEnd token = false := by
  intro token member
  cases orderedTails with
  | nil => simp [taggedTailTokens] at member
  | cons first tails =>
      cases tails with
      | nil =>
          exact tailBlock_continues .first first token
            (by simpa only [taggedTailTokens, List.append_nil] using member)
      | cons second tails =>
          cases tails with
          | nil =>
              simp only [taggedTailTokens, List.append_nil,
                List.mem_append] at member
              rcases member with member | member
              · exact tailBlock_continues .first first token member
              · exact tailBlock_continues .second second token member
          | cons third tails =>
              simp only [taggedTailTokens, List.mem_append] at member
              rcases member with member | member
              · exact tailBlock_continues .first first token member
              · rcases member with member | member
                · exact tailBlock_continues .second second token member
                · exact tailBlock_continues .third third token member

theorem clauseBody_continues (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) :
    ∀ token ∈ clauseBody profile orderedTails,
      isClauseEnd token = false := by
  intro token member
  simp only [clauseBody, List.mem_cons] at member
  rcases member with rfl | member
  · rfl
  · exact taggedTailTokens_continues orderedTails token member

theorem blocksAux_append_clauseEnd
    (reverseBlock body rest : List Token)
    (continues : ∀ token ∈ body, isClauseEnd token = false) :
    TM2EndDelimitedBlockMap.blocksAux isClauseEnd reverseBlock
        (body ++ .clauseEnd :: rest) =
      (reverseBlock.reverse ++ body ++ [.clauseEnd]) ::
        TM2EndDelimitedBlockMap.blocksAux isClauseEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil => simp [TM2EndDelimitedBlockMap.blocksAux, isClauseEnd]
  | cons token body induction =>
      have tokenContinues := continues token (by simp)
      have bodyContinues : ∀ other ∈ body,
          isClauseEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, TM2EndDelimitedBlockMap.blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

theorem blocksAux_clauseRecord_append (reverseBlock : List Token)
    (profile : DirectedClauseProfile)
    (orderedTails : List (List AxisDirection)) (rest : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isClauseEnd reverseBlock
        (clauseRecord profile orderedTails ++ rest) =
      (reverseBlock.reverse ++ clauseRecord profile orderedTails) ::
        TM2EndDelimitedBlockMap.blocksAux isClauseEnd [] rest := by
  rw [clauseRecord_eq_body, List.append_assoc]
  simpa [clauseRecord_eq_body, List.append_assoc] using
    blocksAux_append_clauseEnd reverseBlock
      (clauseBody profile orderedTails) rest
      (clauseBody_continues profile orderedTails)

/-- Canonical concatenation of flat source-clause records. -/
def clauseRecords
    (clauses : List (DirectedClauseProfile × List (List AxisDirection))) :
    List Token :=
  clauses.flatMap fun clause => clauseRecord clause.1 clause.2

@[simp] theorem blocks_clauseRecords
    (clauses : List (DirectedClauseProfile × List (List AxisDirection))) :
    TM2EndDelimitedBlockMap.blocks isClauseEnd (clauseRecords clauses) =
      clauses.map fun clause => clauseRecord clause.1 clause.2 := by
  unfold TM2EndDelimitedBlockMap.blocks clauseRecords
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      rw [List.flatMap_cons,
        blocksAux_clauseRecord_append [] clause.1 clause.2]
      simp only [List.reverse_nil, List.nil_append, List.map_cons]
      rw [induction]

/-- The physical batched compiler has the established routed-record semantics
on every canonical sequence of clockwise source clauses. -/
@[simp] theorem batchedRecords_clauseRecords
    (clauses : List (DirectedClauseProfile × List (List AxisDirection))) :
    batchedRecords (clauseRecords clauses) =
      clauses.flatMap fun clause =>
        sourceClauseRecords clause.1 clause.2 := by
  unfold batchedRecords TM2EndDelimitedBlockMap.mappedOutput
  rw [blocks_clauseRecords, List.flatMap_map]
  apply List.flatMap_congr
  intro clause _
  exact expandedRecords_clauseRecord clause.1 clause.2

end HorizontalRoutedRouteTailRecord
end PeriodicCNFStripReduction
end LeanTrominoes
