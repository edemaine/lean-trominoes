/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Basic
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic of corner-key matching

The lower and upper envelopes describe every possible keyed complement:
the upper envelope fills every uncut cell; the lower envelope retains the
modulo-three background and the four reserved 18-by-18 corners.
-/

namespace LeanTrominoes.KeyCornerArithmetic

def inBox (n : Int) (c : Cell) : Prop :=
  0 ≤ c.1 ∧ c.1 < n ∧ 0 ≤ c.2 ∧ c.2 < n

def inVerticalLock (c : Cell) : Prop :=
  (c.1 = 2 ∧ 0 ≤ c.2 ∧ c.2 ≤ 3) ∨ (c.1 = 3 ∧ c.2 = 2)

def inHorizontalLock (n : Int) (c : Cell) : Prop :=
  (c.1 = n - 4 ∧ c.2 = 2) ∨ (n - 4 ≤ c.1 ∧ c.1 < n ∧ c.2 = 3)

def inKey (n : Int) (c : Cell) : Prop :=
  (c.1 = 2 ∧ n ≤ c.2 ∧ c.2 ≤ n + 3) ∨ (c.1 = 3 ∧ c.2 = n + 2) ∨
  (c.1 = -4 ∧ c.2 = 2) ∨ (-4 ≤ c.1 ∧ c.1 ≤ -1 ∧ c.2 = 3)

def upper (n : Int) (c : Cell) : Prop :=
  (inBox n c ∧ ¬ inVerticalLock c ∧ ¬ inHorizontalLock n c) ∨ inKey n c

def lower (n : Int) (c : Cell) : Prop :=
  (inBox n c ∧ ¬ inVerticalLock c ∧ ¬ inHorizontalLock n c ∧
    ((c.1 % 3 ≠ 0 ∧ c.2 % 3 ≠ 0) ∨
      ((c.1 < 18 ∨ n - 18 ≤ c.1) ∧ (c.2 < 18 ∨ n - 18 ≤ c.2)))) ∨ inKey n c

instance (n : Int) (c : Cell) : Decidable (upper n c) := by
  unfold upper inBox inVerticalLock inHorizontalLock inKey
  infer_instance

instance (n : Int) (c : Cell) : Decidable (lower n c) := by
  unfold lower inBox inVerticalLock inHorizontalLock inKey
  infer_instance

/-- Express a world cell in the coordinates of a placed envelope. -/
def source (s : SquareSymmetry) (offset c : Cell) : Cell :=
  s.inverse.act (Cell.sub c offset)

end LeanTrominoes.KeyCornerArithmetic
