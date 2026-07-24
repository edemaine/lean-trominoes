import LeanTrominoes.PartrecFlatIteration

/-!
# Direct list combinators for partial-recursive programs

These combinators operate on `ToPartrec.Code`'s native `List Nat` values.
They deliberately avoid routing a variable-length list through a single
paired natural-number code.
-/

namespace Turing.ToPartrec.Code

/-- Drop a fixed number of leading fields. -/
def drop : Nat → Code
  | 0 => id
  | count + 1 => (drop count).comp tail

@[simp]
theorem drop_eval (count : Nat) (values : List Nat) :
    (drop count).eval values = pure (values.drop count) := by
  induction count generalizing values with
  | zero => simp [drop]
  | succ count induction =>
      simp [drop, induction]

/-- Read a fixed-offset field as a singleton list, using zero when absent. -/
def get (index : Nat) : Code :=
  head.comp (drop index)

@[simp]
theorem get_eval (index : Nat) (values : List Nat) :
    (get index).eval values = pure [values[index]?.getD 0] := by
  have headAfterDrop :
      (values.drop index).headI = values[index]?.getD 0 := by
    induction index generalizing values with
    | zero =>
        cases values <;> rfl
    | succ index induction =>
        cases values with
        | nil => simp
        | cons value values =>
            simpa using induction values
  simp [get, Part.bind_eq_bind, headAfterDrop]

/-- Prepend the singleton result of `field` to the list result of `rest`. -/
def prepend (field rest : Code) : Code :=
  cons field rest

theorem prepend_eval (field rest : Code)
    (fieldValue : List Nat → Nat) (restValue : List Nat → List Nat)
    (fieldCorrect : ∀ values, field.eval values = pure [fieldValue values])
    (restCorrect : ∀ values, rest.eval values = pure (restValue values))
    (values : List Nat) :
    (prepend field rest).eval values =
      pure (fieldValue values :: restValue values) := by
  simp [prepend, fieldCorrect, restCorrect]

/-- Branch on whether a computed singleton natural is zero, while presenting
the untouched original input to either branch. -/
def branchZero (test whenZero whenSucc : Code) : Code :=
  (case whenZero (whenSucc.comp tail)).comp (cons test id)

theorem branchZero_eval_zero
    (test whenZero whenSucc : Code)
    (testValue : List Nat → Nat)
    (testCorrect : ∀ values, test.eval values = pure [testValue values])
    (whenZeroValue : List Nat → List Nat)
    (whenZeroCorrect :
      ∀ values, whenZero.eval values = pure (whenZeroValue values))
    (values : List Nat) (zero : testValue values = 0) :
    (branchZero test whenZero whenSucc).eval values =
      pure (whenZeroValue values) := by
  simp [branchZero, testCorrect, whenZeroCorrect, zero]

theorem branchZero_eval_succ
    (test whenZero whenSucc : Code)
    (testValue : List Nat → Nat)
    (testCorrect : ∀ values, test.eval values = pure [testValue values])
    (whenSuccValue : List Nat → List Nat)
    (whenSuccCorrect :
      ∀ values, whenSucc.eval values = pure (whenSuccValue values))
    (values : List Nat) (positive : 0 < testValue values) :
    (branchZero test whenZero whenSucc).eval values =
      pure (whenSuccValue values) := by
  obtain ⟨predecessor, predecessorEq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simp [branchZero, testCorrect, whenSuccCorrect, predecessorEq]

/-- Normalize a natural truth tag to Boolean `0` or `1`. -/
def normalizeBool (value : Code) : Code :=
  branchZero value zero one

theorem normalizeBool_eval
    (value : Code) (result : List Nat → Nat)
    (correct : ∀ values, value.eval values = pure [result values])
    (values : List Nat) :
    (normalizeBool value).eval values =
      pure [if result values = 0 then 0 else 1] := by
  by_cases zeroResult : result values = 0
  · rw [if_pos zeroResult]
    exact branchZero_eval_zero value zero one result correct
      (fun _ => [0]) (fun input => by simp) values zeroResult
  · rw [if_neg zeroResult]
    exact branchZero_eval_succ value zero one result correct
      (fun _ => [1]) (fun input => by simp) values
      (Nat.pos_of_ne_zero zeroResult)

/-- Boolean conjunction of two computed natural truth tags. -/
def boolAnd (left right : Code) : Code :=
  branchZero left zero (normalizeBool right)

theorem boolAnd_eval
    (left right : Code) (leftValue rightValue : List Nat → Nat)
    (leftCorrect : ∀ values, left.eval values = pure [leftValue values])
    (rightCorrect : ∀ values, right.eval values = pure [rightValue values])
    (values : List Nat) :
    (boolAnd left right).eval values =
      pure [if leftValue values = 0 ∨ rightValue values = 0
        then 0 else 1] := by
  unfold boolAnd
  by_cases leftZero : leftValue values = 0
  · rw [if_pos (Or.inl leftZero)]
    exact branchZero_eval_zero left zero (normalizeBool right)
      leftValue leftCorrect (fun _ => [0]) (fun input => by simp)
      values leftZero
  · have leftPositive := Nat.pos_of_ne_zero leftZero
    rw [branchZero_eval_succ left zero (normalizeBool right)
      leftValue leftCorrect
      (fun input => [if rightValue input = 0 then 0 else 1])
      (normalizeBool_eval right rightValue rightCorrect)
      values leftPositive]
    by_cases rightZero : rightValue values = 0
    · simp [rightZero]
    · simp [leftZero, rightZero]

/-- Boolean disjunction of two computed natural truth tags. -/
def boolOr (left right : Code) : Code :=
  branchZero left (normalizeBool right) one

theorem boolOr_eval
    (left right : Code) (leftValue rightValue : List Nat → Nat)
    (leftCorrect : ∀ values, left.eval values = pure [leftValue values])
    (rightCorrect : ∀ values, right.eval values = pure [rightValue values])
    (values : List Nat) :
    (boolOr left right).eval values =
      pure [if leftValue values = 0 ∧ rightValue values = 0
        then 0 else 1] := by
  unfold boolOr
  by_cases leftZero : leftValue values = 0
  · rw [branchZero_eval_zero left (normalizeBool right) one
      leftValue leftCorrect
      (fun input => [if rightValue input = 0 then 0 else 1])
      (normalizeBool_eval right rightValue rightCorrect)
      values leftZero]
    by_cases rightZero : rightValue values = 0
    · simp [leftZero, rightZero]
    · simp [leftZero, rightZero]
  · have leftPositive := Nat.pos_of_ne_zero leftZero
    rw [if_neg (fun both => leftZero both.1)]
    exact branchZero_eval_succ left (normalizeBool right) one
      leftValue leftCorrect (fun _ => [1]) (fun input => by simp)
      values leftPositive

/-- Convert a normalized Boolean tag to the optional-Boolean answer tags:
`0 ↦ 1` and nonzero `↦ 2`. -/
def someBoolTag (value : Code) : Code :=
  succ.comp (normalizeBool value)

theorem someBoolTag_eval
    (value : Code) (result : List Nat → Nat)
    (correct : ∀ values, value.eval values = pure [result values])
    (values : List Nat) :
    (someBoolTag value).eval values =
      pure [if result values = 0 then 1 else 2] := by
  simp [someBoolTag, normalizeBool_eval value result correct]
  split <;> simp_all

end Turing.ToPartrec.Code
