import LeanTrominoes.PartrecBooleanSpace
import LeanTrominoes.PartrecPackedAssignmentAtSpace
import LeanTrominoes.PartrecPackedAssignmentPredicates

/-!
# Evaluator-space certificates for packed assignment predicates

The packed `none` predicate first projects the digit returned by the complete
five-column lookup and then performs one fitted zero test.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def packedAssignmentLookupDigitCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  getCost 0 [outcome.2.1, outcome.2.2.toNat] +
    packedAssignmentLookupCodeCost motif queriedColumn target word

theorem packedAssignmentLookupDigit
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentLookupDigitCode
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      [(Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1]
      (packedAssignmentLookupDigitCost motif queriedColumn
        target word) := by
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  simpa [Code.packedAssignmentLookupDigitCode,
    packedAssignmentLookupDigitCost, outcome] using
    comp
      (get 0 [outcome.2.1, outcome.2.2.toNat])
      (packedAssignmentLookup motif queriedColumn target word)

def packedAssignmentIsNoneCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [Encodable.encode motif, queriedColumn,
      Encodable.encode target, word]
  let digit :=
    (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
  isZeroCost values digit
    (packedAssignmentLookupDigitCost motif queriedColumn target word)

theorem packedAssignmentIsNone
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentIsNoneCode
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      [if (Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1 = 0 then 1 else 0]
      (packedAssignmentIsNoneCost motif queriedColumn target word) := by
  simpa [Code.packedAssignmentIsNoneCode,
    packedAssignmentIsNoneCost] using
    isZero
      (packedAssignmentLookupDigit motif queriedColumn target word)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
