import LeanTrominoes.PartrecSqrt
import LeanTrominoes.PartrecSubtract

/-!
# Explicit partial-recursive standard unpairing

Mathlib's `Nat.unpair` computes a square root, subtracts the preceding square,
and branches according to which side of the square shell contains the input.
The square-root scan already exposes enough information to recover the shell
offset without multiplication:

`n - s² = (2s + 1) - ((s + 1)² - n)`.
-/

namespace Turing.ToPartrec.Code

attribute [local simp] Part.bind_eq_bind

/-- Present `[gap, distance]` to truncated subtraction. -/
def unpairRemainderArgumentsCode : Code :=
  prepend (get 1) (get 0)

/-- Convert `[distance, gap, root]` into `[remainder, root]`. -/
def unpairRemainderStateCode : Code :=
  prepend (subtractCode.comp unpairRemainderArgumentsCode) <|
    get 2

theorem sqrtGap_sub_distance (number : Nat) :
    (2 * Nat.sqrt number + 1) -
        ((Nat.sqrt number + 1) *
          (Nat.sqrt number + 1) - number) =
      number - Nat.sqrt number * Nat.sqrt number := by
  let root := Nat.sqrt number
  have lower : root * root ≤ number :=
    Nat.sqrt_le number
  have upper :
      number < (root + 1) * (root + 1) :=
    Nat.lt_succ_sqrt number
  have squareIdentity :
      (root + 1) * (root + 1) =
        root * root + (2 * root + 1) := by
    ring
  change
    (2 * root + 1) -
        ((root + 1) * (root + 1) - number) =
      number - root * root
  omega

@[simp]
theorem unpairRemainderStateCode_eval (number : Nat) :
    unpairRemainderStateCode.eval
        [((Nat.sqrt number + 1) *
            (Nat.sqrt number + 1) - number),
          2 * Nat.sqrt number + 1, Nat.sqrt number] =
      pure
        [number - Nat.sqrt number * Nat.sqrt number,
          Nat.sqrt number] := by
  simp [unpairRemainderStateCode,
    unpairRemainderArgumentsCode,
    sqrtGap_sub_distance]

/-- Unary code producing the square-shell offset and square root. -/
def unpairStateCode : Code :=
  unpairRemainderStateCode.comp sqrtStateCode

@[simp]
theorem unpairStateCode_eval (number : Nat) :
    unpairStateCode.eval [number] =
      pure
        [number - Nat.sqrt number * Nat.sqrt number,
          Nat.sqrt number] := by
  simp [unpairStateCode]

/-- Compute `root - remainder`; positivity selects the upper shell edge. -/
def unpairTestArgumentsCode : Code :=
  prepend (get 1) (get 0)

def unpairTestCode : Code :=
  subtractCode.comp unpairTestArgumentsCode

@[simp]
theorem unpairTestCode_eval (remainder root : Nat) :
    unpairTestCode.eval [remainder, root] =
      pure [root - remainder] := by
  simp [unpairTestCode, unpairTestArgumentsCode]

/-- Present `[remainder, root]` to the subtraction `remainder - root`. -/
def unpairRightArgumentsCode : Code :=
  prepend (get 0) (get 1)

/-- Lower-shell output `[root, remainder - root]`. -/
def unpairLowerCode : Code :=
  prepend (get 1) <|
    subtractCode.comp unpairRightArgumentsCode

@[simp]
theorem unpairLowerCode_eval (remainder root : Nat) :
    unpairLowerCode.eval [remainder, root] =
      pure [root, remainder - root] := by
  simp [unpairLowerCode, unpairRightArgumentsCode]

/-- Convert `[remainder, root]` into the two coordinates of `Nat.unpair`. -/
def unpairFinalCode : Code :=
  branchZero unpairTestCode unpairLowerCode id

theorem unpairFinalCode_eval (remainder root : Nat) :
    unpairFinalCode.eval [remainder, root] =
      pure
        (if remainder < root then [remainder, root]
          else [root, remainder - root]) := by
  by_cases upperEdge : remainder < root
  · have positive : 0 < root - remainder := by omega
    rw [if_pos upperEdge]
    exact
      branchZero_eval_succ_at
        unpairTestCode unpairLowerCode id
        [remainder, root] (root - remainder)
        (unpairTestCode_eval remainder root)
        [remainder, root] (by simp)
        positive
  · have zero : root - remainder = 0 := by omega
    rw [if_neg upperEdge]
    exact
      branchZero_eval_zero_at
        unpairTestCode unpairLowerCode id
        [remainder, root] (root - remainder)
        (unpairTestCode_eval remainder root)
        [root, remainder - root]
        (unpairLowerCode_eval remainder root)
        zero

/-- Unary explicit code for Mathlib's standard `Nat.unpair`. -/
def unpairCode : Code :=
  unpairFinalCode.comp unpairStateCode

@[simp]
theorem unpairCode_eval (number : Nat) :
    unpairCode.eval [number] =
      pure [number.unpair.1, number.unpair.2] := by
  let root := Nat.sqrt number
  let remainder := number - root * root
  have stateRun :
      unpairStateCode.eval [number] =
        pure [remainder, root] := by
    change
      unpairStateCode.eval [number] =
        pure
          [number - Nat.sqrt number * Nat.sqrt number,
            Nat.sqrt number]
    exact unpairStateCode_eval number
  have finalRun :=
    unpairFinalCode_eval remainder root
  have semantic :
      number.unpair =
        if remainder < root then (remainder, root)
        else (root, remainder - root) := by
    simp [Nat.unpair, root, remainder]
  calc
    _ = unpairFinalCode.eval [remainder, root] := by
      simp [unpairCode, stateRun]
    _ = pure
        (if remainder < root then [remainder, root]
          else [root, remainder - root]) :=
      finalRun
    _ = pure [number.unpair.1, number.unpair.2] := by
      rw [semantic]
      split <;> rfl

end Turing.ToPartrec.Code
