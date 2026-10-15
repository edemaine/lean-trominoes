/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Encoding.Finite.FiniteBoolCheck
import LeanTrominoes.Computation.Encoding.Bounded.BoundedDelimitedDirectionCancellationNoReversal

/-! # Cancelling one bounded opposite-direction run -/

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

def directionBlock (direction : AxisDirection) (amount : Count) :
    List Token :=
  List.replicate amount.val (.direction direction)

def overflow (count amount : Count) : Nat :=
  count.val + amount.val - bufferCapacity

def residual (count amount : Count) : Nat :=
  Nat.min bufferCapacity (count.val + amount.val) - amount.val

def residualCount (count amount : Count) : Count :=
  ⟨residual count amount,
    Nat.lt_succ_of_le
      (le_trans (Nat.sub_le _ _)
        (Nat.min_le_left _ _))⟩

def overflowBlock (direction : AxisDirection)
    (count amount : Count) : List Token :=
  List.replicate (overflow count amount) (.direction direction)

def afterCancellation (direction : AxisDirection)
    (count amount : Count) : Control :=
  if residual count amount = 0 then
    .empty
  else
    .run direction (residualCount count amount)

def oppositeRunCheck (direction : AxisDirection) : Bool :=
  if direction.IsGenuine then
    finiteAll fun count : Count =>
      if 0 < count.val then
        finiteAll fun amount : Count =>
          decide (FiniteStateTransducer.scan transition (.run direction count)
            (directionBlock direction amount ++ directionBlock direction.opposite amount) =
            (afterCancellation direction count amount, overflowBlock direction count amount))
      else true
  else true

end BoundedDelimitedDirectionCancellation
end LeanTrominoes
