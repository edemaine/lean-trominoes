import LeanTrominoes.PartrecListCode
import Mathlib.Data.Nat.Sqrt

/-!
# Explicit partial-recursive natural square root

Mathlib's standard pairing decoder uses `Nat.sqrt`.  This module exposes a
flat evaluator program for that operation.  The loop processes the integers
from zero through the input while retaining the distance to the next square,
the gap between consecutive squares, and the current square root.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- State update when the next processed integer is a square.  Its input is
`[gap, root]`, after the two surrounding `case` nodes remove the distance
field and its predecessor. -/
def sqrtHitCode : Code :=
  prepend ((addConst 2).comp (get 0)) <|
    prepend ((addConst 2).comp (get 0)) <|
      succ.comp (get 1)

/-- State update when the next processed integer is below the next square.
Its input is `[distance - 2, gap, root]`. -/
def sqrtMissCode : Code :=
  prepend succ <|
    prepend (get 1) (get 2)

/-- Total fallback for the unreachable state whose distance is zero. -/
def sqrtZeroCode : Code :=
  prepend zero <|
    prepend (get 0) (get 1)

/-- One square-root scan step on `[distance, gap, root]`. -/
def sqrtStepCode : Code :=
  case sqrtZeroCode <|
    case sqrtHitCode sqrtMissCode

def sqrtStepList (values : List Nat) : List Nat :=
  let distance := values[0]?.getD 0
  let gap := values[1]?.getD 0
  let root := values[2]?.getD 0
  if distance = 0 then [0, gap, root]
  else if distance = 1 then [gap + 2, gap + 2, root + 1]
  else [distance - 1, gap, root]

@[simp]
theorem sqrtStepCode_eval (values : List Nat) :
    sqrtStepCode.eval values = pure (sqrtStepList values) := by
  cases values with
  | nil =>
      simp [sqrtStepCode, sqrtZeroCode, sqrtStepList]
  | cons distance rest =>
      cases distance with
      | zero =>
          simp [sqrtStepCode, sqrtZeroCode, sqrtStepList]
      | succ predecessor =>
          cases predecessor with
          | zero =>
              cases rest with
              | nil =>
                  simp [sqrtStepCode, sqrtHitCode, sqrtStepList]
              | cons gap rest =>
                  cases rest with
                  | nil =>
                      simp [sqrtStepCode, sqrtHitCode, sqrtStepList]
                  | cons root rest =>
                      simp [sqrtStepCode, sqrtHitCode, sqrtStepList]
          | succ predecessor =>
              simp [sqrtStepCode, sqrtMissCode, sqrtStepList]

/-- Assemble the countdown and its initial state. -/
def sqrtInputCode : Code :=
  prepend head <|
    prepend one <|
      prepend one zero

@[simp]
theorem sqrtInputCode_eval (number : Nat) :
    sqrtInputCode.eval [number] =
      pure [number, 1, 1, 0] := by
  simp [sqrtInputCode]

/-- Unary explicit code computing `Nat.sqrt`. -/
def sqrtCode : Code :=
  (get 2).comp <|
    (flatIterate sqrtStepCode).comp sqrtInputCode

/-- Semantic invariant after `processed` scan steps. -/
def SqrtInvariant
    (steps remaining : Nat) (payload : List Nat) : Prop :=
  ∃ processed root,
    processed + remaining = steps ∧
      root * root ≤ processed ∧
      processed < (root + 1) * (root + 1) ∧
      payload =
        [(root + 1) * (root + 1) - processed,
          2 * root + 1, root]

theorem sqrtInvariant_initial (steps : Nat) :
    SqrtInvariant steps steps [1, 1, 0] := by
  exact ⟨0, 0, by simp, by simp, by norm_num, by norm_num⟩

theorem sqrtInvariant_preserved
    (steps remaining : Nat) (payload : List Nat)
    (invariant : SqrtInvariant steps (remaining + 1) payload) :
    SqrtInvariant steps remaining (sqrtStepList payload) := by
  obtain ⟨processed, root, sum, lower, upper, rfl⟩ := invariant
  have positive :
      0 < (root + 1) * (root + 1) - processed := by
    omega
  by_cases hit :
      processed + 1 = (root + 1) * (root + 1)
  · refine ⟨processed + 1, root + 1, by omega, ?_, ?_, ?_⟩
    · omega
    · rw [hit]
      exact Nat.mul_self_lt_mul_self (by omega)
    · have distanceOne :
          (root + 1) * (root + 1) - processed = 1 := by
        omega
      have nextSquare :
          (root + 1 + 1) * (root + 1 + 1) =
            (root + 1) * (root + 1) + (2 * root + 3) := by
        ring
      have nextDistance :
          (root + 1 + 1) * (root + 1 + 1) -
              (processed + 1) =
            2 * root + 3 := by
        omega
      simp [sqrtStepList, distanceOne, nextDistance]
      ring
  · have nextUpper :
        processed + 1 < (root + 1) * (root + 1) := by
      omega
    refine ⟨processed + 1, root, by omega, by omega,
      nextUpper, ?_⟩
    have distanceNotZero :
        (root + 1) * (root + 1) - processed ≠ 0 := by
      omega
    have distanceNotOne :
        (root + 1) * (root + 1) - processed ≠ 1 := by
      omega
    have distanceStep :
        (root + 1) * (root + 1) - processed - 1 =
          (root + 1) * (root + 1) - (processed + 1) := by
      omega
    simp [sqrtStepList, distanceNotZero, distanceNotOne,
      distanceStep]

theorem sqrtInvariant_iterate (steps : Nat) :
    SqrtInvariant steps 0
      (((sqrtStepList)^[steps]) [1, 1, 0]) := by
  induction steps with
  | zero =>
      simpa using sqrtInvariant_initial 0
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      have lifted :
          SqrtInvariant (steps + 1) 1
            (((sqrtStepList)^[steps]) [1, 1, 0]) := by
        obtain ⟨processed, root, sum, lower, upper, payload⟩ :=
          induction
        exact
          ⟨processed, root, by omega, lower, upper, payload⟩
      apply sqrtInvariant_preserved (steps + 1) 0
      exact lifted

theorem sqrtStepList_iterate (steps : Nat) :
    ((sqrtStepList)^[steps]) [1, 1, 0] =
      [((Nat.sqrt steps + 1) * (Nat.sqrt steps + 1) - steps),
        2 * Nat.sqrt steps + 1, Nat.sqrt steps] := by
  obtain ⟨processed, root, sum, lower, upper, payload⟩ :=
    sqrtInvariant_iterate steps
  have processedEq : processed = steps := by omega
  subst processed
  have rootEq : root = Nat.sqrt steps :=
    Nat.eq_sqrt.mpr ⟨lower, upper⟩
  subst root
  exact payload

@[simp]
theorem sqrtCode_eval (number : Nat) :
    sqrtCode.eval [number] =
      pure [Nat.sqrt number] := by
  simp [sqrtCode, flatIterate_eval,
    sqrtStepList_iterate]

end Turing.ToPartrec.Code
