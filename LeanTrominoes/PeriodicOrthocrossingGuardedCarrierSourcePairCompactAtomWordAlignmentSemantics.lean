/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairCompactAtomWordData

/-! # Alignment of delayed and final compact carrier words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairCompactAtomWords

def nodeItemAtPeriod (period : Nat) : CarrierNode → List Bool × Bool
  | .terminal terminal =>
      (CarrierKeyWords.word
        (CarrierNodeNormalizedSourceKeys.pairAtPeriod
          period (.terminal terminal)).1, false)
  | .boundary boundary =>
      (CarrierNodeSourceKeys.word
        (CarrierNodeNormalizedSourceKeys.pairAtPeriod
          period (.boundary boundary)), true)

@[simp] theorem trailing_nodeItemAtPeriod
    (period : Nat) (node : CarrierNode) :
    (nodeItemAtPeriod period node).1 ++
        [(nodeItemAtPeriod period node).2] =
      GuardedCarrierSourcePairTrailingConstructor.nodeWordAtPeriod
        period node := by
  cases node <;> rfl

@[simp] theorem prefixed_nodeItemAtPeriod
    (period : Nat) (node : CarrierNode) :
    false :: (nodeItemAtPeriod period node).2 ::
        (nodeItemAtPeriod period node).1 =
      CarrierNodeNormalizedSourceKeys.compactWordAtPeriod period node := by
  cases node <;> rfl

theorem trailingWords_nodeItemsAtPeriod
    (period : Nat) (nodes : List CarrierNode) :
    DelimitedBinaryWordTrailingBitPrefix.trailingWords
        (nodes.map (nodeItemAtPeriod period)) =
      GuardedCarrierSourcePairTrailingConstructor.nodeWordsAtPeriod
        period nodes := by
  unfold DelimitedBinaryWordTrailingBitPrefix.trailingWords
    GuardedCarrierSourcePairTrailingConstructor.nodeWordsAtPeriod
  apply congrArg DelimitedBinaryWords.Input.mk
  induction nodes with
  | nil => rfl
  | cons node nodes induction =>
      cases node <;> simp only [List.map_cons, trailing_nodeItemAtPeriod,
        induction]

theorem prefixedWords_nodeItemsAtPeriod
    (period : Nat) (nodes : List CarrierNode) :
    DelimitedBinaryWordTrailingBitPrefix.prefixedWords
        (nodes.map (nodeItemAtPeriod period)) =
      wordsAtPeriod period nodes := by
  unfold DelimitedBinaryWordTrailingBitPrefix.prefixedWords wordsAtPeriod
  apply congrArg DelimitedBinaryWords.Input.mk
  induction nodes with
  | nil => rfl
  | cons node nodes induction =>
      cases node <;> simp only [List.map_cons, prefixed_nodeItemAtPeriod,
        induction]

end GuardedCarrierSourcePairCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing
