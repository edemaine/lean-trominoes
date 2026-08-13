/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecFlatPackedAssignmentPredicatesSpace
import LeanTrominoes.PartrecFlatPackedOverlapAt

/-!
# Evaluator-space certificate for one flat packed overlap comparison

The fitted program reconstructs two native five-field assignment queries from
one seven-field overlap input, runs both verified flat assignment lookups, and
compares their selected base-nine digits.  All adapters and both lookup calls
are bounded in the actual flat overlap-input footprint.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatPackedOverlapCurrentArgumentsCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  let values := Code.flatPackedOverlapAtInput motif currentColumn nextColumn
    base currentWord nextWord
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let restWord := prependCost values [currentWord] coordinates
    (getCost 5 values) (dropCost 7 values)
  let restY := prependCost values [Encodable.encode base.2]
    (currentWord :: coordinates) (getCost 4 values) restWord
  let restX := prependCost values [Encodable.encode base.1]
    (Encodable.encode base.2 :: currentWord :: coordinates)
    (getCost 3 values) restY
  let restColumn := prependCost values [currentColumn]
    (Encodable.encode base.1 :: Encodable.encode base.2 ::
      currentWord :: coordinates) (getCost 1 values) restX
  prependCost values [motif.length]
    (currentColumn :: Encodable.encode base.1 :: Encodable.encode base.2 ::
      currentWord :: coordinates) (getCost 0 values) restColumn

theorem flatPackedOverlapCurrentArguments
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    EvaluatorCodeFits Code.flatPackedOverlapCurrentArgumentsCode
      (Code.flatPackedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      ([motif.length, currentColumn,
          Encodable.encode base.1, Encodable.encode base.2, currentWord] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatPackedOverlapCurrentArgumentsCost motif currentColumn nextColumn
        base currentWord nextWord) := by
  let values := Code.flatPackedOverlapAtInput motif currentColumn nextColumn
    base currentWord nextWord
  have restWord := prepend (get 5 values) (drop 7 values)
  have restY := prepend (get 4 values) restWord
  have restX := prepend (get 3 values) restY
  have restColumn := prepend (get 1 values) restX
  have result := prepend (get 0 values) restColumn
  simpa [Code.flatPackedOverlapCurrentArgumentsCode,
    flatPackedOverlapCurrentArgumentsCost,
    Code.flatPackedOverlapAtInput, prependCost, values] using result

def flatPackedOverlapNextArgumentsCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  let values := Code.flatPackedOverlapAtInput motif currentColumn nextColumn
    base currentWord nextWord
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let restWord := prependCost values [nextWord] coordinates
    (getCost 6 values) (dropCost 7 values)
  let restY := prependCost values [Encodable.encode base.2]
    (nextWord :: coordinates) (getCost 4 values) restWord
  let restX := prependCost values [Encodable.encode base.1]
    (Encodable.encode base.2 :: nextWord :: coordinates)
    (getCost 3 values) restY
  let restColumn := prependCost values [nextColumn]
    (Encodable.encode base.1 :: Encodable.encode base.2 ::
      nextWord :: coordinates) (getCost 2 values) restX
  prependCost values [motif.length]
    (nextColumn :: Encodable.encode base.1 :: Encodable.encode base.2 ::
      nextWord :: coordinates) (getCost 0 values) restColumn

theorem flatPackedOverlapNextArguments
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    EvaluatorCodeFits Code.flatPackedOverlapNextArgumentsCode
      (Code.flatPackedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      ([motif.length, nextColumn,
          Encodable.encode base.1, Encodable.encode base.2, nextWord] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatPackedOverlapNextArgumentsCost motif currentColumn nextColumn
        base currentWord nextWord) := by
  let values := Code.flatPackedOverlapAtInput motif currentColumn nextColumn
    base currentWord nextWord
  have restWord := prepend (get 6 values) (drop 7 values)
  have restY := prepend (get 4 values) restWord
  have restX := prepend (get 3 values) restY
  have restColumn := prepend (get 2 values) restX
  have result := prepend (get 0 values) restColumn
  simpa [Code.flatPackedOverlapNextArgumentsCode,
    flatPackedOverlapNextArgumentsCost,
    Code.flatPackedOverlapAtInput, prependCost, values] using result

def flatPackedOverlapCurrentDigitCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  flatPackedAssignmentLookupDigitCost motif currentColumn base currentWord +
    flatPackedOverlapCurrentArgumentsCost motif currentColumn nextColumn
      base currentWord nextWord

theorem flatPackedOverlapCurrentDigit
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    EvaluatorCodeFits Code.flatPackedOverlapCurrentDigitCode
      (Code.flatPackedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [(Code.packedAssignmentLookupOutcome motif currentColumn
        base currentWord).2.1]
      (flatPackedOverlapCurrentDigitCost motif currentColumn nextColumn
        base currentWord nextWord) := by
  simpa [Code.flatPackedOverlapCurrentDigitCode,
    flatPackedOverlapCurrentDigitCost] using
    comp
      (flatPackedAssignmentLookupDigit motif currentColumn base currentWord)
      (flatPackedOverlapCurrentArguments motif currentColumn nextColumn
        base currentWord nextWord)

def flatPackedOverlapNextDigitCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  flatPackedAssignmentLookupDigitCost motif nextColumn base nextWord +
    flatPackedOverlapNextArgumentsCost motif currentColumn nextColumn
      base currentWord nextWord

theorem flatPackedOverlapNextDigit
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    EvaluatorCodeFits Code.flatPackedOverlapNextDigitCode
      (Code.flatPackedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [(Code.packedAssignmentLookupOutcome motif nextColumn base nextWord).2.1]
      (flatPackedOverlapNextDigitCost motif currentColumn nextColumn
        base currentWord nextWord) := by
  simpa [Code.flatPackedOverlapNextDigitCode,
    flatPackedOverlapNextDigitCost] using
    comp
      (flatPackedAssignmentLookupDigit motif nextColumn base nextWord)
      (flatPackedOverlapNextArguments motif currentColumn nextColumn
        base currentWord nextWord)

def flatPackedOverlapEqualityArgumentsCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  let values := Code.flatPackedOverlapAtInput motif currentColumn nextColumn
    base currentWord nextWord
  let currentDigit := (Code.packedAssignmentLookupOutcome motif currentColumn
    base currentWord).2.1
  let nextDigit := (Code.packedAssignmentLookupOutcome motif nextColumn
    base nextWord).2.1
  prependCost values [currentDigit] [nextDigit]
    (flatPackedOverlapCurrentDigitCost motif currentColumn nextColumn
      base currentWord nextWord)
    (flatPackedOverlapNextDigitCost motif currentColumn nextColumn
      base currentWord nextWord)

theorem flatPackedOverlapEqualityArguments
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    let currentDigit := (Code.packedAssignmentLookupOutcome motif
      currentColumn base currentWord).2.1
    let nextDigit := (Code.packedAssignmentLookupOutcome motif
      nextColumn base nextWord).2.1
    EvaluatorCodeFits Code.flatPackedOverlapEqualityArgumentsCode
      (Code.flatPackedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [currentDigit, nextDigit]
      (flatPackedOverlapEqualityArgumentsCost motif currentColumn nextColumn
        base currentWord nextWord) := by
  simp only
  simpa [Code.flatPackedOverlapEqualityArgumentsCode,
    flatPackedOverlapEqualityArgumentsCost, prependCost] using
    prepend
      (flatPackedOverlapCurrentDigit motif currentColumn nextColumn
        base currentWord nextWord)
      (flatPackedOverlapNextDigit motif currentColumn nextColumn
        base currentWord nextWord)

def flatPackedOverlapAtCost
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  let currentDigit := (Code.packedAssignmentLookupOutcome motif currentColumn
    base currentWord).2.1
  let nextDigit := (Code.packedAssignmentLookupOutcome motif nextColumn
    base nextWord).2.1
  natEqCost currentDigit nextDigit +
    flatPackedOverlapEqualityArgumentsCost motif currentColumn nextColumn
      base currentWord nextWord

theorem flatPackedOverlapAt
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    let currentDigit := (Code.packedAssignmentLookupOutcome motif
      currentColumn base currentWord).2.1
    let nextDigit := (Code.packedAssignmentLookupOutcome motif
      nextColumn base nextWord).2.1
    EvaluatorCodeFits Code.flatPackedOverlapAtCode
      (Code.flatPackedOverlapAtInput motif currentColumn nextColumn
        base currentWord nextWord)
      [if currentDigit = nextDigit then 1 else 0]
      (flatPackedOverlapAtCost motif currentColumn nextColumn
        base currentWord nextWord) := by
  simp only
  simpa [Code.flatPackedOverlapAtCode, flatPackedOverlapAtCost] using
    comp
      (natEq
        (Code.packedAssignmentLookupOutcome motif currentColumn
          base currentWord).2.1
        (Code.packedAssignmentLookupOutcome motif nextColumn
          base nextWord).2.1)
      (flatPackedOverlapEqualityArguments motif currentColumn nextColumn
        base currentWord nextWord)

/-! ## Native polynomial bound -/

def flatPackedOverlapAtInputUnit
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  encodedListSpace (Code.flatPackedOverlapAtInput motif currentColumn
    nextColumn base currentWord nextWord) + 10

theorem flatPackedOverlapCurrentLookupUnit_le
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedAssignmentLookupNativeInputSpace motif currentColumn base
        currentWord ≤
      flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
        currentWord nextWord := by
  simp [flatPackedAssignmentLookupNativeInputSpace,
    flatPackedOverlapAtInputUnit, Code.flatPackedOverlapAtInput,
    List.cons_append, encodedListSpace_cons]
  omega

theorem flatPackedOverlapNextLookupUnit_le
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedAssignmentLookupNativeInputSpace motif nextColumn base nextWord ≤
      flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
        currentWord nextWord := by
  simp [flatPackedAssignmentLookupNativeInputSpace,
    flatPackedOverlapAtInputUnit, Code.flatPackedOverlapAtInput,
    List.cons_append, encodedListSpace_cons]
  omega

theorem flatPackedOverlapCurrentArgumentsCost_le_linear
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapCurrentArgumentsCost motif currentColumn nextColumn
        base currentWord nextWord ≤
      100000000 * flatPackedOverlapAtInputUnit motif currentColumn nextColumn
        base currentWord nextWord := by
  let values := Code.flatPackedOverlapAtInput motif currentColumn nextColumn
    base currentWord nextWord
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let unit := flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
    currentWord nextWord
  have scanSpace : encodedListSpace values + 1 ≤ unit := by
    simp [values, unit, flatPackedOverlapAtInputUnit]
  have getBound : ∀ index : Nat, index ≤ 7 →
      getCost index values ≤ 80000 * unit := by
    intro index fixed
    have raw := listCodeGetCost_le_linear index values
    calc
      _ ≤ (10000 * (index + 1)) * (encodedListSpace values + 1) := raw
      _ ≤ 80000 * unit := by gcongr; omega
  have get0 := getBound 0 (by omega)
  have get1 := getBound 1 (by omega)
  have get3 := getBound 3 (by omega)
  have get4 := getBound 4 (by omega)
  have get5 := getBound 5 (by omega)
  have get7 := getBound 7 (by omega)
  have drop7 : dropCost 7 values ≤ 80000 * unit := by
    have part : dropCost 7 values ≤ getCost 7 values := by
      simp only [getCost]
      omega
    exact part.trans get7
  change flatPackedOverlapCurrentArgumentsCost motif currentColumn nextColumn
      base currentWord nextWord ≤ 100000000 * unit
  simp [flatPackedOverlapCurrentArgumentsCost, prependCost,
    Code.flatPackedOverlapAtInput, List.cons_append,
    encodedListSpace_cons] at ⊢
  simp only [values, unit, flatPackedOverlapAtInputUnit,
    Code.flatPackedOverlapAtInput, List.cons_append, List.nil_append,
    encodedListSpace_cons] at *
  omega

theorem flatPackedOverlapNextArgumentsCost_le_linear
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapNextArgumentsCost motif currentColumn nextColumn
        base currentWord nextWord ≤
      100000000 * flatPackedOverlapAtInputUnit motif currentColumn nextColumn
        base currentWord nextWord := by
  let values := Code.flatPackedOverlapAtInput motif currentColumn nextColumn
    base currentWord nextWord
  let coordinates := motif.flatMap PeriodicStripFlatEncoding.cellFields
  let unit := flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
    currentWord nextWord
  have scanSpace : encodedListSpace values + 1 ≤ unit := by
    simp [values, unit, flatPackedOverlapAtInputUnit]
  have getBound : ∀ index : Nat, index ≤ 7 →
      getCost index values ≤ 80000 * unit := by
    intro index fixed
    have raw := listCodeGetCost_le_linear index values
    calc
      _ ≤ (10000 * (index + 1)) * (encodedListSpace values + 1) := raw
      _ ≤ 80000 * unit := by gcongr; omega
  have get0 := getBound 0 (by omega)
  have get2 := getBound 2 (by omega)
  have get3 := getBound 3 (by omega)
  have get4 := getBound 4 (by omega)
  have get6 := getBound 6 (by omega)
  have get7 := getBound 7 (by omega)
  have drop7 : dropCost 7 values ≤ 80000 * unit := by
    have part : dropCost 7 values ≤ getCost 7 values := by
      simp only [getCost]
      omega
    exact part.trans get7
  change flatPackedOverlapNextArgumentsCost motif currentColumn nextColumn
      base currentWord nextWord ≤ 100000000 * unit
  simp [flatPackedOverlapNextArgumentsCost, prependCost,
    Code.flatPackedOverlapAtInput, List.cons_append,
    encodedListSpace_cons] at ⊢
  simp only [values, unit, flatPackedOverlapAtInputUnit,
    Code.flatPackedOverlapAtInput, List.cons_append, List.nil_append,
    encodedListSpace_cons] at *
  omega

def flatPackedOverlapAssignmentCoefficient : Nat :=
  10000000000000000000000000000000000000000000000000000000000

theorem flatPackedOverlapCurrentDigitCost_le_quadratic
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapCurrentDigitCost motif currentColumn nextColumn
        base currentWord nextWord ≤
      (10 ^ 70) *
        (flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
          currentWord nextWord) ^ 2 := by
  let unit := flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
    currentWord nextWord
  let native := flatPackedAssignmentLookupNativeInputSpace motif
    currentColumn base currentWord
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedOverlapAtInputUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have nativeBound := flatPackedOverlapCurrentLookupUnit_le motif currentColumn
    nextColumn base currentWord nextWord
  have lookupBudget := flatPackedAssignmentLookupDigitCost_le_budget motif
    currentColumn base currentWord
  have lookupCost : flatPackedAssignmentLookupDigitCost motif currentColumn
      base currentWord ≤
    flatPackedAssignmentPredicateSpaceBound motif currentColumn base
      currentWord := lookupBudget.trans (by
        simp [flatPackedAssignmentPredicateSpaceBound]
        omega)
  have lookupQuadratic :=
    flatPackedAssignmentPredicateSpaceBound_le_native_quadratic motif
      currentColumn base currentWord
  have lookup : flatPackedAssignmentLookupDigitCost motif currentColumn base
      currentWord ≤ flatPackedOverlapAssignmentCoefficient * unit ^ 2 := by
    calc
      _ ≤ flatPackedAssignmentPredicateSpaceBound motif currentColumn base
          currentWord := lookupCost
      _ ≤ flatPackedOverlapAssignmentCoefficient * native ^ 2 := by
        simpa [flatPackedOverlapAssignmentCoefficient, native] using
          lookupQuadratic
      _ ≤ flatPackedOverlapAssignmentCoefficient * unit ^ 2 := by
        gcongr
  have arguments := flatPackedOverlapCurrentArgumentsCost_le_linear motif
    currentColumn nextColumn base currentWord nextWord
  have coefficient :
      flatPackedOverlapAssignmentCoefficient + 100000000 ≤ 10 ^ 70 := by
    native_decide
  change flatPackedAssignmentLookupDigitCost motif currentColumn base
      currentWord +
      flatPackedOverlapCurrentArgumentsCost motif currentColumn nextColumn
        base currentWord nextWord ≤ (10 ^ 70) * unit ^ 2
  calc
    _ ≤ flatPackedOverlapAssignmentCoefficient * unit ^ 2 +
        100000000 * unit ^ 2 := by
      exact Nat.add_le_add lookup
        (arguments.trans (Nat.mul_le_mul_left 100000000 unitQuadratic))
    _ = (flatPackedOverlapAssignmentCoefficient + 100000000) *
        unit ^ 2 := by ring
    _ ≤ (10 ^ 70) * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficient

theorem flatPackedOverlapNextDigitCost_le_quadratic
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapNextDigitCost motif currentColumn nextColumn
        base currentWord nextWord ≤
      (10 ^ 70) *
        (flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
          currentWord nextWord) ^ 2 := by
  let unit := flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
    currentWord nextWord
  let native := flatPackedAssignmentLookupNativeInputSpace motif nextColumn
    base nextWord
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedOverlapAtInputUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have nativeBound := flatPackedOverlapNextLookupUnit_le motif currentColumn
    nextColumn base currentWord nextWord
  have lookupBudget := flatPackedAssignmentLookupDigitCost_le_budget motif
    nextColumn base nextWord
  have lookupCost : flatPackedAssignmentLookupDigitCost motif nextColumn base
      nextWord ≤
    flatPackedAssignmentPredicateSpaceBound motif nextColumn base nextWord :=
    lookupBudget.trans (by
      simp [flatPackedAssignmentPredicateSpaceBound]
      omega)
  have lookupQuadratic :=
    flatPackedAssignmentPredicateSpaceBound_le_native_quadratic motif
      nextColumn base nextWord
  have lookup : flatPackedAssignmentLookupDigitCost motif nextColumn base
      nextWord ≤ flatPackedOverlapAssignmentCoefficient * unit ^ 2 := by
    calc
      _ ≤ flatPackedAssignmentPredicateSpaceBound motif nextColumn base
          nextWord := lookupCost
      _ ≤ flatPackedOverlapAssignmentCoefficient * native ^ 2 := by
        simpa [flatPackedOverlapAssignmentCoefficient, native] using
          lookupQuadratic
      _ ≤ flatPackedOverlapAssignmentCoefficient * unit ^ 2 := by
        gcongr
  have arguments := flatPackedOverlapNextArgumentsCost_le_linear motif
    currentColumn nextColumn base currentWord nextWord
  have coefficient :
      flatPackedOverlapAssignmentCoefficient + 100000000 ≤ 10 ^ 70 := by
    native_decide
  change flatPackedAssignmentLookupDigitCost motif nextColumn base nextWord +
      flatPackedOverlapNextArgumentsCost motif currentColumn nextColumn base
        currentWord nextWord ≤ (10 ^ 70) * unit ^ 2
  calc
    _ ≤ flatPackedOverlapAssignmentCoefficient * unit ^ 2 +
        100000000 * unit ^ 2 := by
      exact Nat.add_le_add lookup
        (arguments.trans (Nat.mul_le_mul_left 100000000 unitQuadratic))
    _ = (flatPackedOverlapAssignmentCoefficient + 100000000) *
        unit ^ 2 := by ring
    _ ≤ (10 ^ 70) * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficient

theorem flatPackedOverlapEqualityArgumentsCost_le_quadratic
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapEqualityArgumentsCost motif currentColumn nextColumn
        base currentWord nextWord ≤
      (10 ^ 80) *
        (flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
          currentWord nextWord) ^ 2 := by
  let values := Code.flatPackedOverlapAtInput motif currentColumn nextColumn
    base currentWord nextWord
  let unit := flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
    currentWord nextWord
  let currentDigit := (Code.packedAssignmentLookupOutcome motif currentColumn
    base currentWord).2.1
  let nextDigit := (Code.packedAssignmentLookupOutcome motif nextColumn base
    nextWord).2.1
  have unitPositive : 10 ≤ unit := by
    simp [unit, flatPackedOverlapAtInputUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have currentCost : flatPackedOverlapCurrentDigitCost motif currentColumn
      nextColumn base currentWord nextWord ≤ (10 ^ 70) * unit ^ 2 := by
    simpa [unit] using flatPackedOverlapCurrentDigitCost_le_quadratic motif
      currentColumn nextColumn base currentWord nextWord
  have nextCost : flatPackedOverlapNextDigitCost motif currentColumn nextColumn
      base currentWord nextWord ≤ (10 ^ 70) * unit ^ 2 := by
    simpa [unit] using flatPackedOverlapNextDigitCost_le_quadratic motif
      currentColumn nextColumn base currentWord nextWord
  have inputSpace : encodedListSpace values ≤ unit := by
    simp [values, unit, flatPackedOverlapAtInputUnit]
  have currentSmall : currentDigit ≤ 40 := by
    simpa [currentDigit] using Code.packedAssignmentLookupOutcome_digit_le
      motif currentColumn base currentWord
  have nextSmall : nextDigit ≤ 40 := by
    simpa [nextDigit] using Code.packedAssignmentLookupOutcome_digit_le
      motif nextColumn base nextWord
  have currentBits := encodeNat_length_mono currentSmall
  have nextBits := encodeNat_length_mono nextSmall
  have fortyBits : (Computability.encodeNat 40).length = 6 := by
    native_decide
  rw [fortyBits] at currentBits nextBits
  have currentSpace : encodedListSpace [currentDigit] ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have outputSpace : encodedListSpace [currentDigit, nextDigit] ≤
      2 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have overhead : encodedListSpace values +
      encodedListSpace [currentDigit] +
      encodedListSpace [currentDigit, nextDigit] + 2 ≤ 5 * unit := by
    omega
  have coefficient : 2 * (10 ^ 70) + 5 ≤ 10 ^ 80 := by
    native_decide
  change flatPackedOverlapCurrentDigitCost motif currentColumn nextColumn
        base currentWord nextWord +
      flatPackedOverlapNextDigitCost motif currentColumn nextColumn base
        currentWord nextWord +
      encodedListSpace values + encodedListSpace [currentDigit] +
      encodedListSpace [currentDigit, nextDigit] + 2 ≤
    (10 ^ 80) * unit ^ 2
  calc
    _ ≤ 2 * (10 ^ 70) * unit ^ 2 + 5 * unit := by omega
    _ ≤ (2 * (10 ^ 70) + 5) * unit ^ 2 := by
      nlinarith
    _ ≤ (10 ^ 80) * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficient

def flatPackedOverlapAtSpaceBound
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : Nat :=
  (10 ^ 90) *
    (flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
      currentWord nextWord) ^ 2

theorem flatPackedOverlapAtCost_le_quadratic
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapAtCost motif currentColumn nextColumn base currentWord
        nextWord ≤
      flatPackedOverlapAtSpaceBound motif currentColumn nextColumn base
        currentWord nextWord := by
  let unit := flatPackedOverlapAtInputUnit motif currentColumn nextColumn base
    currentWord nextWord
  let currentDigit := (Code.packedAssignmentLookupOutcome motif currentColumn
    base currentWord).2.1
  let nextDigit := (Code.packedAssignmentLookupOutcome motif nextColumn base
    nextWord).2.1
  have unitPositive : 1 ≤ unit := by
    simp [unit, flatPackedOverlapAtInputUnit]
  have unitQuadratic : unit ≤ unit ^ 2 := by nlinarith
  have arguments := flatPackedOverlapEqualityArgumentsCost_le_quadratic motif
    currentColumn nextColumn base currentWord nextWord
  have currentSmall : currentDigit ≤ 40 := by
    simpa [currentDigit] using Code.packedAssignmentLookupOutcome_digit_le
      motif currentColumn base currentWord
  have nextSmall : nextDigit ≤ 40 := by
    simpa [nextDigit] using Code.packedAssignmentLookupOutcome_digit_le
      motif nextColumn base nextWord
  have equalityRaw := natEqCost_le_linear currentDigit nextDigit
  have equalityArgument : 2 * (currentDigit + nextDigit) + 4 ≤ 164 := by
    omega
  have equalityBits := encodeNat_length_mono equalityArgument
  have oneSixtyFourBits : (Computability.encodeNat 164).length = 8 := by
    native_decide
  rw [oneSixtyFourBits] at equalityBits
  have equality : natEqCost currentDigit nextDigit ≤
      100000000000 * unit := equalityRaw.trans (by
        simp only [encodedListSpace_cons, encodedListSpace_nil]
        omega)
  have coefficient : 10 ^ 80 + 100000000000 ≤ 10 ^ 90 := by
    native_decide
  change natEqCost currentDigit nextDigit +
      flatPackedOverlapEqualityArgumentsCost motif currentColumn nextColumn
        base currentWord nextWord ≤ (10 ^ 90) * unit ^ 2
  calc
    _ ≤ 100000000000 * unit + (10 ^ 80) * unit ^ 2 :=
      Nat.add_le_add equality arguments
    _ ≤ (100000000000 + 10 ^ 80) * unit ^ 2 := by
      nlinarith
    _ = (10 ^ 80 + 100000000000) * unit ^ 2 := by
      rw [Nat.add_comm]
    _ ≤ (10 ^ 90) * unit ^ 2 :=
      Nat.mul_le_mul_right (unit ^ 2) coefficient

theorem flatPackedOverlapAtPolynomialBounded
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    let currentDigit := (Code.packedAssignmentLookupOutcome motif
      currentColumn base currentWord).2.1
    let nextDigit := (Code.packedAssignmentLookupOutcome motif
      nextColumn base nextWord).2.1
    EvaluatorCodeFits Code.flatPackedOverlapAtCode
      (Code.flatPackedOverlapAtInput motif currentColumn nextColumn base
        currentWord nextWord)
      [if currentDigit = nextDigit then 1 else 0]
      (flatPackedOverlapAtSpaceBound motif currentColumn nextColumn base
        currentWord nextWord) := by
  simp only
  exact (flatPackedOverlapAt motif currentColumn nextColumn base currentWord
    nextWord).mono (flatPackedOverlapAtCost_le_quadratic motif currentColumn
      nextColumn base currentWord nextWord)

theorem flatPackedOverlapAtSemanticPolynomialBounded
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (column : Fin 4) (base : Cell) :
    EvaluatorCodeFits Code.flatPackedOverlapAtCode
      (Code.flatPackedOverlapAtInput periodicStrip.motif column.succ.val
        column.castSucc.val base current.assignmentWord next.assignmentWord)
      [(current.overlapsAtBool periodicStrip next column base).toNat]
      (flatPackedOverlapAtSpaceBound periodicStrip.motif column.succ.val
        column.castSucc.val base current.assignmentWord next.assignmentWord) := by
  have bounded := flatPackedOverlapAtPolynomialBounded periodicStrip.motif
    column.succ.val column.castSucc.val base current.assignmentWord
      next.assignmentWord
  simp only at bounded
  rw [Code.packedOverlapAtResult_eq_semantic periodicStrip current next
    column base] at bounded
  exact bounded

end EvaluatorCodeFits
end PartrecToTM2
end Turing
