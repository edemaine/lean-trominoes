/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreePolyTimeProfiles
import LeanTrominoes.AlignedUnaryBooleanChoiceOccurrenceSemantics
import LeanTrominoes.UnaryPrefixSumsInterface

/-! # Finite atom descriptors for the exact-one clause gadget -/
namespace LeanTrominoes.PeriodicOneInThree.AtomDescriptors
open PeriodicCNF.UnaryProgramClauseProfile

/-- An original occurrence or an auxiliary, with the end-of-source-clause flag. -/
abbrev Descriptor := Option OneInThreeAux × Bool

def block : ClauseProfile → List Descriptor
  | .unary _ => [(none,false),(some .firstChoice,false),(some .secondChoice,false),
      (some .secondPadding,false),(some .firstChoice,false),(some .firstSlack,false),
      (some .thirdPadding,false),(some .secondChoice,false),(some .secondSlack,false),
      (some .secondPadding,false),(some .thirdPadding,true)]
  | .binary _ _ => [(none,false),(some .firstChoice,false),(some .secondChoice,false),
      (none,false),(some .firstChoice,false),(some .firstSlack,false),
      (some .thirdPadding,false),(some .secondChoice,false),(some .secondSlack,false),
      (some .thirdPadding,true)]
  | .ternary _ _ _ => [(none,false),(some .firstChoice,false),(some .secondChoice,false),
      (none,false),(some .firstChoice,false),(some .firstSlack,false),
      (none,false),(some .secondChoice,false),(some .secondSlack,true)]

def originalStep (d : Descriptor) : Nat := if d.1.isNone then 1 else 0

def clauseStep (d : Descriptor) : Nat := if d.2 then 1 else 0

def auxiliaryOffset (d : Descriptor) : Nat :=
  4 * Numeric.kindCode (d.1.getD .firstChoice) + 1

@[simp] theorem block_original_sum (p : ClauseProfile) :
    ((block p).map originalStep).sum = p.literals.length := by cases p <;> rfl

@[simp] theorem block_clause_sum (p : ClauseProfile) :
    ((block p).map clauseStep).sum = 1 := by cases p <;> rfl

@[simp] theorem block_length (p : ClauseProfile) :
    (block p).length =
      ((PeriodicCNF.ClauseProfileFigureNine.oneInThreeProfiles p).flatMap ClauseProfile.literals).length := by
  cases p <;> rfl

/-- Direct interpretation, keeping the two counters separate. -/
def evaluate (original : List Nat) : Nat → Nat → List Descriptor → List Nat
  | _, _, [] => []
  | clause, occurrence, d :: ds =>
      (match d.1 with
        | none => 2 * original.getD occurrence 0
        | some k => 28 * clause + 4 * Numeric.kindCode k + 1) ::
      evaluate original (clause + clauseStep d) (occurrence + originalStep d) ds

@[simp] theorem evaluate_length (original : List Nat) (clause occurrence : Nat)
    (ds : List Descriptor) : (evaluate original clause occurrence ds).length = ds.length := by
  induction ds generalizing clause occurrence with
  | nil => rfl
  | cons d ds ih => simp [evaluate,ih]

theorem evaluate_append (original : List Nat) (clause occurrence : Nat)
    (ds es : List Descriptor) :
    evaluate original clause occurrence (ds ++ es) =
      evaluate original clause occurrence ds ++
        evaluate original (clause + (ds.map clauseStep).sum)
          (occurrence + (ds.map originalStep).sum) es := by
  induction ds generalizing clause occurrence with
  | nil => simp [evaluate]
  | cons d ds ih => simp [evaluate,ih,Nat.add_assoc]

/-- Every prefix query is within the original stream or its appended sentinel. -/
theorem prefix_le_sum (start : Nat) (values : List Nat) :
    ∀ n ∈ PrefixSums.startsAux start values, n ≤ start + values.sum := by
  induction values generalizing start with
  | nil => simp
  | cons v vs ih =>
    intro n hn
    simp only [PrefixSums.startsAux_cons,List.mem_cons] at hn
    rcases hn with rfl | hn
    · simp only [List.sum_cons]; omega
    · have h := ih (start+v) n hn
      simpa only [List.sum_cons,Nat.add_assoc] using h

end LeanTrominoes.PeriodicOneInThree.AtomDescriptors
