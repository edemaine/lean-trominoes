/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeSATThreeNumeric
import LeanTrominoes.PeriodicCNFSplitLiteralSemantics
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Finite literal profiles of the compact occurrence split -/
namespace LeanTrominoes.PeriodicThreeSATThree.Numeric
open PeriodicCNF PeriodicCNF.UnaryProgramClauseProfile

def cycleProfile : ClauseProfile := .binary (current false) (current true)

theorem occurrence_profiles (source : PeriodicCNF Nat) (ci : Nat) (c : PeriodicClause Nat) :
    (renameClause (atomMap source) (occurrenceClause ci c)).map LiteralProfile.ofLiteral =
      c.map LiteralProfile.ofLiteral := by
  simp only [renameClause,occurrenceClause,List.map_map,Function.comp_def]
  conv_rhs => rw [← List.zipIdx_map_fst (l := c) 0]
  rw [List.map_map]
  rfl

private theorem cycleFrom_profiles (source : PeriodicCNF Nat)
    (first currentCopy : ThreeOccurrenceVariable Nat) (rest : List (ThreeOccurrenceVariable Nat)) :
    ((cycleFrom first currentCopy rest).map (renameClause (atomMap source))).map
      (List.map LiteralProfile.ofLiteral) =
        List.replicate (rest.length+1) cycleProfile.literals := by
  induction rest generalizing currentCopy with
  | nil => rfl
  | cons next rest ih =>
    simp only [cycleFrom,List.map_cons,ih,List.length_cons]
    rw [show rest.length+1+1=Nat.succ (rest.length+1) from rfl,List.replicate_succ]
    rfl

private theorem cycleClauses_profiles (source : PeriodicCNF Nat)
    (copies : List (ThreeOccurrenceVariable Nat)) :
    ((cycleClauses copies).map (renameClause (atomMap source))).map
      (List.map LiteralProfile.ofLiteral) =
        List.replicate copies.length cycleProfile.literals := by
  cases copies with
  | nil => rfl
  | cons first rest => exact cycleFrom_profiles source first first rest

private theorem cycles_profiles (source : PeriodicCNF Nat) :
    ((allCycleClauses source).map (renameClause (atomMap source))).map
      (List.map LiteralProfile.ofLiteral) =
        List.replicate (allCycleClauses source).length cycleProfile.literals := by
  unfold allCycleClauses
  induction sourceVariables source with
  | nil => rfl
  | cons atom atoms ih =>
    simp only [List.flatMap_cons,List.map_append,List.length_append,List.replicate_add]
    rw [cycleClauses_profiles,cycleClauses_length,ih]

theorem profiles (source : PeriodicCNF Nat) :
    (formula source).clauses.map (List.map LiteralProfile.ofLiteral) =
      source.clauses.map (List.map LiteralProfile.ofLiteral) ++
        List.replicate (presentationLiteralCount source) cycleProfile.literals := by
  simp only [formula,rename,PeriodicThreeSATThree.formula,List.map_append]
  rw [cycles_profiles,allCycleClauses_length]
  congr 1
  simp only [occurrenceClauses,List.map_map,Function.comp_def]
  simp_rw [occurrence_profiles]
  conv_rhs => rw [← List.zipIdx_map_fst (l := source.clauses) 0]
  rw [List.map_map]
  rfl

end LeanTrominoes.PeriodicThreeSATThree.Numeric
