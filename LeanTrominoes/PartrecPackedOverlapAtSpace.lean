/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecPackedAssignmentPredicatesSpace
import LeanTrominoes.PartrecPackedOverlapAt

/-!
# Evaluator-space certificate for one packed overlap comparison

The fitted program projects two four-field lookup inputs from one fixed-width
six-field state, performs both packed assignment scans, and compares their
base-nine digits.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def packedOverlapCurrentArgumentsCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  let values :=
    Code.packedOverlapAtInput motif currentColumn nextColumn
      base currentWord nextWord
  let rest3 :=
    prependCost values [Encodable.encode base] [currentWord]
      (getCost 3 values) (getCost 4 values)
  let rest1 :=
    prependCost values [currentColumn]
      [Encodable.encode base, currentWord]
      (getCost 1 values) rest3
  prependCost values [Encodable.encode motif]
    [currentColumn, Encodable.encode base, currentWord]
    (getCost 0 values) rest1

theorem packedOverlapCurrentArguments
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    EvaluatorCodeFits Code.packedOverlapCurrentArgumentsCode
      (Code.packedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [Encodable.encode motif, currentColumn,
        Encodable.encode base, currentWord]
      (packedOverlapCurrentArgumentsCost motif
        currentColumn nextColumn base currentWord nextWord) := by
  let values :=
    Code.packedOverlapAtInput motif currentColumn nextColumn
      base currentWord nextWord
  have rest3 := prepend (get 3 values) (get 4 values)
  have rest1 := prepend (get 1 values) rest3
  have result := prepend (get 0 values) rest1
  simpa [Code.packedOverlapCurrentArgumentsCode,
    packedOverlapCurrentArgumentsCost,
    Code.packedOverlapAtInput,
    prependCost, values] using result

def packedOverlapNextArgumentsCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  let values :=
    Code.packedOverlapAtInput motif currentColumn nextColumn
      base currentWord nextWord
  let rest3 :=
    prependCost values [Encodable.encode base] [nextWord]
      (getCost 3 values) (getCost 5 values)
  let rest2 :=
    prependCost values [nextColumn]
      [Encodable.encode base, nextWord]
      (getCost 2 values) rest3
  prependCost values [Encodable.encode motif]
    [nextColumn, Encodable.encode base, nextWord]
    (getCost 0 values) rest2

theorem packedOverlapNextArguments
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    EvaluatorCodeFits Code.packedOverlapNextArgumentsCode
      (Code.packedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [Encodable.encode motif, nextColumn,
        Encodable.encode base, nextWord]
      (packedOverlapNextArgumentsCost motif
        currentColumn nextColumn base currentWord nextWord) := by
  let values :=
    Code.packedOverlapAtInput motif currentColumn nextColumn
      base currentWord nextWord
  have rest3 := prepend (get 3 values) (get 5 values)
  have rest2 := prepend (get 2 values) rest3
  have result := prepend (get 0 values) rest2
  simpa [Code.packedOverlapNextArgumentsCode,
    packedOverlapNextArgumentsCost,
    Code.packedOverlapAtInput,
    prependCost, values] using result

def packedOverlapCurrentDigitCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  packedAssignmentLookupDigitCost motif currentColumn base currentWord +
    packedOverlapCurrentArgumentsCost motif currentColumn nextColumn
      base currentWord nextWord

theorem packedOverlapCurrentDigit
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    EvaluatorCodeFits Code.packedOverlapCurrentDigitCode
      (Code.packedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [(Code.packedAssignmentLookupOutcome motif currentColumn
        base currentWord).2.1]
      (packedOverlapCurrentDigitCost motif
        currentColumn nextColumn base currentWord nextWord) := by
  simpa [Code.packedOverlapCurrentDigitCode,
    packedOverlapCurrentDigitCost] using
    comp
      (packedAssignmentLookupDigit
        motif currentColumn base currentWord)
      (packedOverlapCurrentArguments motif currentColumn nextColumn
        base currentWord nextWord)

def packedOverlapNextDigitCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  packedAssignmentLookupDigitCost motif nextColumn base nextWord +
    packedOverlapNextArgumentsCost motif currentColumn nextColumn
      base currentWord nextWord

theorem packedOverlapNextDigit
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    EvaluatorCodeFits Code.packedOverlapNextDigitCode
      (Code.packedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [(Code.packedAssignmentLookupOutcome motif nextColumn
        base nextWord).2.1]
      (packedOverlapNextDigitCost motif
        currentColumn nextColumn base currentWord nextWord) := by
  simpa [Code.packedOverlapNextDigitCode,
    packedOverlapNextDigitCost] using
    comp
      (packedAssignmentLookupDigit
        motif nextColumn base nextWord)
      (packedOverlapNextArguments motif currentColumn nextColumn
        base currentWord nextWord)

def packedOverlapEqualityArgumentsCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  let values :=
    Code.packedOverlapAtInput motif currentColumn nextColumn
      base currentWord nextWord
  let currentDigit :=
    (Code.packedAssignmentLookupOutcome motif currentColumn
      base currentWord).2.1
  let nextDigit :=
    (Code.packedAssignmentLookupOutcome motif nextColumn
      base nextWord).2.1
  prependCost values [currentDigit] [nextDigit]
    (packedOverlapCurrentDigitCost motif currentColumn nextColumn
      base currentWord nextWord)
    (packedOverlapNextDigitCost motif currentColumn nextColumn
      base currentWord nextWord)

theorem packedOverlapEqualityArguments
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    let currentDigit :=
      (Code.packedAssignmentLookupOutcome motif currentColumn
        base currentWord).2.1
    let nextDigit :=
      (Code.packedAssignmentLookupOutcome motif nextColumn
        base nextWord).2.1
    EvaluatorCodeFits Code.packedOverlapEqualityArgumentsCode
      (Code.packedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [currentDigit, nextDigit]
      (packedOverlapEqualityArgumentsCost motif
        currentColumn nextColumn base currentWord nextWord) := by
  simp only
  simpa [Code.packedOverlapEqualityArgumentsCode,
    packedOverlapEqualityArgumentsCost,
    prependCost] using
    prepend
      (packedOverlapCurrentDigit motif currentColumn nextColumn
        base currentWord nextWord)
      (packedOverlapNextDigit motif currentColumn nextColumn
        base currentWord nextWord)

def packedOverlapAtCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  let currentDigit :=
    (Code.packedAssignmentLookupOutcome motif currentColumn
      base currentWord).2.1
  let nextDigit :=
    (Code.packedAssignmentLookupOutcome motif nextColumn
      base nextWord).2.1
  natEqCost currentDigit nextDigit +
    packedOverlapEqualityArgumentsCost motif
      currentColumn nextColumn base currentWord nextWord

theorem packedOverlapAt
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    let currentDigit :=
      (Code.packedAssignmentLookupOutcome motif currentColumn
        base currentWord).2.1
    let nextDigit :=
      (Code.packedAssignmentLookupOutcome motif nextColumn
        base nextWord).2.1
    EvaluatorCodeFits Code.packedOverlapAtCode
      (Code.packedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [if currentDigit = nextDigit then 1 else 0]
      (packedOverlapAtCost motif currentColumn nextColumn
        base currentWord nextWord) := by
  simp only
  simpa [Code.packedOverlapAtCode,
    packedOverlapAtCost] using
    comp
      (natEq
        (Code.packedAssignmentLookupOutcome motif currentColumn
          base currentWord).2.1
        (Code.packedAssignmentLookupOutcome motif nextColumn
          base nextWord).2.1)
      (packedOverlapEqualityArguments motif
        currentColumn nextColumn base currentWord nextWord)

def packedOverlapAtSpaceBound
    (motifCode currentColumn nextColumn baseCode
      currentWord nextWord : Nat) : Nat :=
  100000000000000000000000 *
    (encodedListSpace
      [64 * (motifCode + motifCode + motifCode +
        baseCode + currentColumn + currentWord +
        motifCode + motifCode + motifCode +
        baseCode + nextColumn + nextWord + 100) + 1000] + 1)

private theorem packedOverlapAtBudgetGrowth
    (unit : Nat) (positive : 1 ≤ unit) :
    10000000000 * unit +
        (30000000000000000000000 * unit) ≤
      100000000000000000000000 * unit := by
  omega

private theorem packedOverlapEqualityArgumentsBudget
    (unit currentCost nextCost overhead : Nat)
    (currentBound :
      currentCost ≤ 1000000000000000000000 * unit)
    (nextBound :
      nextCost ≤ 1000000000000000000000 * unit)
    (overheadBound : overhead ≤ 100 * unit) :
    currentCost + nextCost + overhead ≤
      30000000000000000000000 * unit := by
  omega

private theorem packedOverlapEqualityArgumentsCost_le_of
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord unit : Nat)
    (currentBound :
      packedOverlapCurrentDigitCost motif
          currentColumn nextColumn base currentWord nextWord ≤
        1000000000000000000000 * unit)
    (nextBound :
      packedOverlapNextDigitCost motif
          currentColumn nextColumn base currentWord nextWord ≤
        1000000000000000000000 * unit)
    (overheadBound :
      encodedListSpace
          (Code.packedOverlapAtInput motif currentColumn nextColumn
            base currentWord nextWord) +
        encodedListSpace
          [(Code.packedAssignmentLookupOutcome motif currentColumn
            base currentWord).2.1] +
        encodedListSpace
          [(Code.packedAssignmentLookupOutcome motif currentColumn
              base currentWord).2.1,
            (Code.packedAssignmentLookupOutcome motif nextColumn
              base nextWord).2.1] + 2 ≤
        100 * unit) :
    packedOverlapEqualityArgumentsCost motif
        currentColumn nextColumn base currentWord nextWord ≤
      30000000000000000000000 * unit := by
  have combined :=
    packedOverlapEqualityArgumentsBudget unit
      (packedOverlapCurrentDigitCost motif
        currentColumn nextColumn base currentWord nextWord)
      (packedOverlapNextDigitCost motif
        currentColumn nextColumn base currentWord nextWord)
      (encodedListSpace
          (Code.packedOverlapAtInput motif currentColumn nextColumn
            base currentWord nextWord) +
        encodedListSpace
          [(Code.packedAssignmentLookupOutcome motif currentColumn
            base currentWord).2.1] +
        encodedListSpace
          [(Code.packedAssignmentLookupOutcome motif currentColumn
              base currentWord).2.1,
            (Code.packedAssignmentLookupOutcome motif nextColumn
              base nextWord).2.1] + 2)
      currentBound nextBound overheadBound
  simpa [packedOverlapEqualityArgumentsCost,
    prependCost, Nat.add_assoc] using combined

set_option maxHeartbeats 400000 in
theorem packedOverlapAtCost_le_linear
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    packedOverlapAtCost motif currentColumn nextColumn
        base currentWord nextWord ≤
      packedOverlapAtSpaceBound
        (Encodable.encode motif) currentColumn nextColumn
        (Encodable.encode base) currentWord nextWord := by
  let motifCode := Encodable.encode motif
  let baseCode := Encodable.encode base
  let currentDigit :=
    (Code.packedAssignmentLookupOutcome motif currentColumn
      base currentWord).2.1
  let nextDigit :=
    (Code.packedAssignmentLookupOutcome motif nextColumn
      base nextWord).2.1
  let limit :=
    64 * (motifCode + motifCode + motifCode +
      baseCode + currentColumn + currentWord +
      motifCode + motifCode + motifCode +
      baseCode + nextColumn + nextWord + 100) + 1000
  let unit := encodedListSpace [limit] + 1
  change
    packedOverlapAtCost motif currentColumn nextColumn
        base currentWord nextWord ≤
      100000000000000000000000 * unit
  have unitPositive : 1 ≤ unit := by
    simp [unit, encodedListSpace_cons,
      encodedListSpace_nil]
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, encodedListSpace_cons,
      encodedListSpace_nil]
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have baseBound : baseCode ≤ limit := by
    simp only [limit]
    omega
  have currentColumnBound : currentColumn ≤ limit := by
    simp only [limit]
    omega
  have nextColumnBound : nextColumn ≤ limit := by
    simp only [limit]
    omega
  have currentWordBound : currentWord ≤ limit := by
    simp only [limit]
    omega
  have nextWordBound : nextWord ≤ limit := by
    simp only [limit]
    omega
  have currentDigitSmall : currentDigit ≤ 40 := by
    simpa [currentDigit] using
      Code.packedAssignmentLookupOutcome_digit_le
        motif currentColumn base currentWord
  have nextDigitSmall : nextDigit ≤ 40 := by
    simpa [nextDigit] using
      Code.packedAssignmentLookupOutcome_digit_le
        motif nextColumn base nextWord
  have currentDigitBound : currentDigit ≤ limit := by
    simp only [currentDigit, limit]
    clear * - currentDigitSmall
    omega
  have nextDigitBound : nextDigit ≤ limit := by
    simp only [nextDigit, limit]
    clear * - nextDigitSmall
    omega
  have motifBits := encodeNat_length_mono motifBound
  have baseBits := encodeNat_length_mono baseBound
  have currentColumnBits :=
    encodeNat_length_mono currentColumnBound
  have nextColumnBits :=
    encodeNat_length_mono nextColumnBound
  have currentWordBits := encodeNat_length_mono currentWordBound
  have nextWordBits := encodeNat_length_mono nextWordBound
  have currentDigitBits :=
    encodeNat_length_mono currentDigitBound
  have nextDigitBits := encodeNat_length_mono nextDigitBound
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have baseSuccBits :=
    encodeNat_length_mono
      (show baseCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have currentColumnSuccBits :=
    encodeNat_length_mono
      (show currentColumn + 1 ≤ limit by
        simp only [limit]
        omega)
  have nextColumnSuccBits :=
    encodeNat_length_mono
      (show nextColumn + 1 ≤ limit by
        simp only [limit]
        omega)
  have currentWordSuccBits :=
    encodeNat_length_mono
      (show currentWord + 1 ≤ limit by
        simp only [limit]
        omega)
  have nextWordSuccBits :=
    encodeNat_length_mono
      (show nextWord + 1 ≤ limit by
        simp only [limit]
        omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have motifBitsRaw :
      (Computability.encodeNat
        (Encodable.encode motif)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifBits
  have baseBitsRaw :
      (Computability.encodeNat
        (Encodable.encode base)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [baseCode] using baseBits
  have motifSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode motif + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifSuccBits
  have baseSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode base + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [baseCode] using baseSuccBits
  have currentArguments :
      packedOverlapCurrentArgumentsCost motif
          currentColumn nextColumn base currentWord nextWord ≤
        1000000 * unit := by
    simp [packedOverlapCurrentArgumentsCost,
      Code.packedOverlapAtInput, prependCost,
      getCost, dropCost, headCost, idCost, nilCost,
      tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq, zeroBits]
    clear * - motifBitsRaw baseBitsRaw currentColumnBits
      nextColumnBits currentWordBits nextWordBits
      motifSuccBitsRaw baseSuccBitsRaw currentColumnSuccBits
      nextColumnSuccBits currentWordSuccBits nextWordSuccBits
      unitEq
    omega
  have nextArguments :
      packedOverlapNextArgumentsCost motif
          currentColumn nextColumn base currentWord nextWord ≤
        1000000 * unit := by
    simp [packedOverlapNextArgumentsCost,
      Code.packedOverlapAtInput, prependCost,
      getCost, dropCost, headCost, idCost, nilCost,
      tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq, zeroBits]
    clear * - motifBitsRaw baseBitsRaw currentColumnBits
      nextColumnBits currentWordBits nextWordBits
      motifSuccBitsRaw baseSuccBitsRaw currentColumnSuccBits
      nextColumnSuccBits currentWordSuccBits nextWordSuccBits
      unitEq
    omega
  have currentLookupLocal :=
    packedAssignmentLookupDigitCost_le_linear
      motif currentColumn base currentWord
  have currentLookupLimit :
      32 * (motifCode + motifCode + motifCode +
          baseCode + currentColumn + currentWord + 40 + 32) + 200 ≤
        limit := by
    simp only [limit]
    omega
  have currentLookupBits :=
    encodeNat_length_mono currentLookupLimit
  have currentLookup :
      packedAssignmentLookupDigitCost motif
          currentColumn base currentWord ≤
        800000000000000000000 * unit := by
    have aligned :
        packedAssignmentLookupDigitCost motif
            currentColumn base currentWord ≤
          800000000000000000000 *
            (encodedListSpace
              [32 * (motifCode + motifCode + motifCode +
                baseCode + currentColumn + currentWord +
                40 + 32) + 200] + 1) := by
      simpa [packedAssignmentLookupDigitSpaceBound,
        motifCode, baseCode] using currentLookupLocal
    simp only [unitEq, encodedListSpace_cons,
      encodedListSpace_nil] at aligned ⊢
    omega
  have nextLookupLocal :=
    packedAssignmentLookupDigitCost_le_linear
      motif nextColumn base nextWord
  have nextLookupLimit :
      32 * (motifCode + motifCode + motifCode +
          baseCode + nextColumn + nextWord + 40 + 32) + 200 ≤
        limit := by
    simp only [limit]
    omega
  have nextLookupBits :=
    encodeNat_length_mono nextLookupLimit
  have nextLookup :
      packedAssignmentLookupDigitCost motif
          nextColumn base nextWord ≤
        800000000000000000000 * unit := by
    have aligned :
        packedAssignmentLookupDigitCost motif
            nextColumn base nextWord ≤
          800000000000000000000 *
            (encodedListSpace
              [32 * (motifCode + motifCode + motifCode +
                baseCode + nextColumn + nextWord +
                40 + 32) + 200] + 1) := by
      simpa [packedAssignmentLookupDigitSpaceBound,
        motifCode, baseCode] using nextLookupLocal
    simp only [unitEq, encodedListSpace_cons,
      encodedListSpace_nil] at aligned ⊢
    omega
  have currentDigitCost :
      packedOverlapCurrentDigitCost motif
          currentColumn nextColumn base currentWord nextWord ≤
        1000000000000000000000 * unit := by
    simp only [packedOverlapCurrentDigitCost]
    clear * - currentLookup currentArguments
    omega
  have nextDigitCost :
      packedOverlapNextDigitCost motif
          currentColumn nextColumn base currentWord nextWord ≤
        1000000000000000000000 * unit := by
    simp only [packedOverlapNextDigitCost]
    clear * - nextLookup nextArguments
    omega
  have inputSpace :
      encodedListSpace
          (Code.packedOverlapAtInput motif currentColumn nextColumn
            base currentWord nextWord) ≤
        10 * unit := by
    simp [Code.packedOverlapAtInput,
      unitEq,
      encodedListSpace_cons, encodedListSpace_nil]
    clear * - motifBitsRaw baseBitsRaw currentColumnBits
      nextColumnBits currentWordBits nextWordBits unitEq
    omega
  have equalityArguments :
      packedOverlapEqualityArgumentsCost motif
          currentColumn nextColumn base currentWord nextWord ≤
        30000000000000000000000 * unit := by
    let overhead :=
      encodedListSpace
          (Code.packedOverlapAtInput motif currentColumn nextColumn
            base currentWord nextWord) +
        encodedListSpace [currentDigit] +
        encodedListSpace [currentDigit, nextDigit] + 2
    have overheadBound : overhead ≤ 100 * unit := by
      simp [overhead, encodedListSpace_cons,
        encodedListSpace_nil, unitEq]
      clear * - inputSpace currentDigitBits nextDigitBits unitEq
      omega
    apply packedOverlapEqualityArgumentsCost_le_of
      motif currentColumn nextColumn base currentWord nextWord unit
      currentDigitCost nextDigitCost
    simpa only [overhead, currentDigit, nextDigit] using overheadBound
  have equalityLocal := natEqCost_le_linear
    currentDigit nextDigit
  have equalityLimit :
      2 * (currentDigit + nextDigit) + 4 ≤ limit := by
    simp only [limit]
    clear * - currentDigitSmall nextDigitSmall
    omega
  have equalityBits := encodeNat_length_mono equalityLimit
  have equality :
      natEqCost currentDigit nextDigit ≤
        10000000000 * unit := by
    simp only [unitEq, encodedListSpace_cons,
      encodedListSpace_nil] at equalityLocal ⊢
    clear * - equalityLocal equalityBits unitEq
    omega
  simp only [packedOverlapAtCost]
  exact
    (Nat.add_le_add equality equalityArguments).trans
      (packedOverlapAtBudgetGrowth unit unitPositive)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
