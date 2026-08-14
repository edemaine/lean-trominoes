/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphSize
import LeanTrominoes.PeriodicThreeSATThree

/-!
# Presentation-size bounds for periodic 3SAT-3 conversion
-/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

private theorem filterMap_length_le
    {α β : Type*} (values : List α) (function : α → Option β) :
    (values.filterMap function).length ≤ values.length := by
  induction values with
  | nil => simp
  | cons value values induction =>
      cases equation : function value <;>
        simp [equation] <;> omega

private theorem flatMap_length_le
    {α β : Type*} (values : List α) (function : α → List β)
    (bound : Nat)
    (bounded : ∀ value ∈ values, (function value).length ≤ bound) :
    (values.flatMap function).length ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values induction =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have head := bounded value (by simp)
      have tail := induction fun member memberMem =>
        bounded member (by simp [memberMem])
      rw [Nat.add_mul, one_mul]
      omega

@[simp] theorem taggedLiterals_length
    {Variable : Type*} (source : PeriodicCNF Variable) :
    (taggedLiterals source).length =
      PeriodicCNF.presentationLiteralCount source := by
  simp [taggedLiterals, PeriodicCNF.presentationLiteralCount]
  calc
    (List.map (fun item => item.1.length) source.clauses.zipIdx).sum =
        (List.map List.length
          (source.clauses.zipIdx.map Prod.fst)).sum := by
      apply congrArg List.sum
      rw [List.map_map]
      apply List.map_congr_left
      intro item itemMember
      rfl
    _ = (List.map List.length source.clauses).sum := by
      rw [List.zipIdx_map_fst]

theorem sourceVariables_length_le_taggedLiterals
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (sourceVariables source).length ≤ (taggedLiterals source).length := by
  unfold sourceVariables
  simpa only [List.length_map] using
    List.Sublist.length_le
      (List.dedup_sublist
        ((taggedLiterals source).map (fun tagged => tagged.1.atom)))

theorem occurrenceVariables_length_le_taggedLiterals
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    (occurrenceVariables source atom).length ≤
      (taggedLiterals source).length := by
  exact filterMap_length_le _ _

@[simp] theorem cycleFrom_length {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (rest : List (ThreeOccurrenceVariable Variable)) :
    (cycleFrom first current rest).length = rest.length + 1 := by
  induction rest generalizing current with
  | nil => simp [cycleFrom]
  | cons next rest induction =>
      simp [cycleFrom, induction]

theorem cycleClauses_length_le {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    (cycleClauses copies).length ≤ copies.length := by
  cases copies with
  | nil => simp [cycleClauses]
  | cons first rest =>
      simp [cycleClauses]

theorem allCycleClauses_length_le_literalCount_sq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (allCycleClauses source).length ≤
      PeriodicCNF.presentationLiteralCount source ^ 2 := by
  have bounded : ∀ atom ∈ sourceVariables source,
      (cycleClauses (occurrenceVariables source atom)).length ≤
        (taggedLiterals source).length := by
    intro atom atomMember
    exact (cycleClauses_length_le _).trans
      (occurrenceVariables_length_le_taggedLiterals source atom)
  have flat := flatMap_length_le (sourceVariables source)
    (fun atom => cycleClauses (occurrenceVariables source atom))
    (taggedLiterals source).length bounded
  have copyKinds := sourceVariables_length_le_taggedLiterals source
  unfold allCycleClauses
  rw [taggedLiterals_length] at flat copyKinds
  exact flat.trans (by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ copyKinds)

theorem formula_clauses_length_le
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (formula source).clauses.length ≤
      source.clauses.length +
        PeriodicCNF.presentationLiteralCount source ^ 2 := by
  simp only [formula, List.length_append, occurrenceClauses,
    List.length_map, List.length_zipIdx]
  exact Nat.add_le_add_left
    (allCycleClauses_length_le_literalCount_sq source) _

/-- Occurrence splitting has a uniform quadratic presentation-size bound. -/
theorem formula_presentationSize_le
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (width : source.WidthAtMost 3) :
    PeriodicCNF.presentationSize (formula source) ≤
      4 * (PeriodicCNF.presentationSize source +
        PeriodicCNF.presentationSize source ^ 2) := by
  have clauses := formula_clauses_length_le source
  have literals := PeriodicCNF.presentationLiteralCount_le_mul_of_width
    (formula source) 3 (formula_widthAtMostThree width)
  have clauseLe : source.clauses.length ≤
      PeriodicCNF.presentationSize source := by
    unfold PeriodicCNF.presentationSize
    omega
  have literalLe : PeriodicCNF.presentationLiteralCount source ≤
      PeriodicCNF.presentationSize source := by
    unfold PeriodicCNF.presentationSize
    omega
  have squareLe : PeriodicCNF.presentationLiteralCount source ^ 2 ≤
      PeriodicCNF.presentationSize source ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul literalLe literalLe
  have outputClausesLe : (formula source).clauses.length ≤
      PeriodicCNF.presentationSize source +
        PeriodicCNF.presentationSize source ^ 2 :=
    clauses.trans (Nat.add_le_add clauseLe squareLe)
  have outputSizeLe : PeriodicCNF.presentationSize (formula source) ≤
      4 * (formula source).clauses.length := by
    unfold PeriodicCNF.presentationSize at literals ⊢
    omega
  exact outputSizeLe.trans (Nat.mul_le_mul_left 4 outputClausesLe)

end PeriodicThreeSATThree
end LeanTrominoes
