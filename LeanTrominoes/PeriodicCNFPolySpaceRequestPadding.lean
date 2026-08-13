/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Algebra.Polynomial.CoeffList
import LeanTrominoes.PeriodicCNFPolySpaceNativeCompiler
import LeanTrominoes.UnaryPolynomialPaddingMachine

/-!
# Polynomial padding for the periodic-CNF request generator

The compact compiler request contains loops whose bounds are the source
decider's fixed space polynomial.  This file turns that polynomial into the
increasing-degree coefficient list consumed by the verified unary Horner
machine.  On canonical native fields, the machine therefore preserves the
source stream and appends exactly the selected bounded-machine stack width in
unary.
-/

noncomputable section

open scoped BigOperators

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceRequestPadding

open UnaryPolynomialPaddingMachine

/-- Horner evaluation of the coefficients attached to a reversed initial
range.  The accumulator form makes the induction step algebraic. -/
theorem foldl_horner_reverse_range_map (coefficient : Nat → Nat)
    (input accumulator count : Nat) :
    ((List.range count).reverse.map coefficient).foldl
        (fun value next => value * input + next) accumulator =
      accumulator * input ^ count +
        ∑ index ∈ Finset.range count, coefficient index * input ^ index := by
  induction count generalizing accumulator with
  | zero => simp
  | succ count induction =>
      rw [List.range_succ, List.reverse_append, List.map_append,
        List.foldl_append]
      simp only [List.reverse_singleton, List.map_singleton,
        List.foldl_cons, List.foldl_nil]
      rw [induction, Finset.sum_range_succ]
      ring

/-- Natural coefficients of a polynomial in the increasing-degree order
expected by `UnaryPolynomialPaddingMachine`. -/
def polynomialCoefficients (polynomial : Polynomial Nat) : List Nat :=
  polynomial.coeffList.reverse

/-- The coefficient list evaluates to the original natural polynomial. -/
@[simp]
theorem evalCoefficients_polynomialCoefficients
    (polynomial : Polynomial Nat) (input : Nat) :
    evalCoefficients (polynomialCoefficients polynomial) input =
      polynomial.eval input := by
  by_cases polynomialZero : polynomial = 0
  · simp [polynomialZero, polynomialCoefficients, evalCoefficients]
  · unfold polynomialCoefficients evalCoefficients
    rw [List.reverse_reverse]
    simp only [Polynomial.coeffList,
      Polynomial.withBotSucc_degree_eq_natDegree_add_one polynomialZero]
    rw [foldl_horner_reverse_range_map]
    simp only [zero_mul, zero_add]
    exact (Polynomial.eval_eq_sum_range input).symm

/-- Native delimiter recognized by the padding machine. -/
def isDelimiter (symbol : PartrecToTM2.Γ') : Bool :=
  symbol == .cons

theorem selectedCount_append {Source : Type} (selected : Source → Bool)
    (first second : List Source) :
    selectedCount selected (first ++ second) =
      selectedCount selected first + selectedCount selected second := by
  induction first with
  | nil => simp [selectedCount]
  | cons source first induction =>
      simp only [List.cons_append, selectedCount_cons, induction]
      omega

theorem selectedCount_eq_zero_of {Source : Type} (selected : Source → Bool)
    (sources : List Source)
    (noneSelected : ∀ source ∈ sources, selected source = false) :
    selectedCount selected sources = 0 := by
  induction sources with
  | nil => rfl
  | cons source sources induction =>
      simp only [selectedCount_cons, noneSelected source (by simp)]
      rw [if_neg (by simp)]
      simpa using induction (by
        intro tailSource membership
        exact noneSelected tailSource (by simp [membership]))

@[simp]
theorem selectedCount_trNat (number : Nat) :
    selectedCount isDelimiter (PartrecToTM2.trNat number) = 0 := by
  apply selectedCount_eq_zero_of
  intro symbol membership
  have symbolNe :=
    TransitionEvaluatorMachine.trNat_noDelimiter number symbol membership
  simp [isDelimiter, symbolNe]

@[simp]
theorem selectedCount_trList (fields : List Nat) :
    selectedCount isDelimiter (PartrecToTM2.trList fields) = fields.length := by
  induction fields with
  | nil => rfl
  | cons field fields induction =>
      rw [PartrecToTM2.trList, selectedCount_append,
        selectedCount_trNat]
      simp [selectedCount, isDelimiter, induction]
      omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Fixed coefficient list for the exact stack-width polynomial used by the
bounded-machine reduction. -/
def spaceCoefficients : List Nat :=
  polynomialCoefficients
    (PolySpaceReduction.reductionSpacePolynomial decider)

/-- Physical output of the padding phase on a native source-field stream. -/
def spacePaddedNativeFields (fields : List Nat) :
    List (PartrecToTM2.Γ' ⊕ Unit) :=
  paddedOutput isDelimiter (spaceCoefficients decider)
    (PartrecToTM2.trList fields)

@[simp]
theorem evalCoefficients_spaceCoefficients (fieldCount : Nat) :
    evalCoefficients (spaceCoefficients decider) fieldCount =
      (PolySpaceReduction.reductionSpacePolynomial decider).eval
        fieldCount := by
  simp [spaceCoefficients]

theorem spaceOfSymbols_eq_polynomial_eval
    (symbols : List encoding.Γ) :
    PolySpaceCompiler.spaceOfSymbols decider symbols =
      (PolySpaceReduction.reductionSpacePolynomial decider).eval
        symbols.length := by
  simp [PolySpaceCompiler.spaceOfSymbols,
    PolySpaceReduction.reductionSpacePolynomial, Polynomial.eval_add]

/-- On source fields emitted by the finite-alphabet front end, the padding is
exactly the stack width used by the subsequent bounded compiler. -/
@[simp]
theorem spacePaddedNativeFields_fields (symbols : List encoding.Γ) :
    spacePaddedNativeFields decider
        (FiniteEncodingNativeFields.fields symbols) =
      (FiniteEncodingNativeFields.encode symbols).map Sum.inl ++
        List.replicate (PolySpaceCompiler.spaceOfSymbols decider symbols)
          (Sum.inr ()) := by
  unfold spacePaddedNativeFields paddedOutput
  rw [selectedCount_trList, evalCoefficients_spaceCoefficients,
    FiniteEncodingNativeFields.fields_length,
    ← spaceOfSymbols_eq_polynomial_eval]
  rfl

/-- The concrete padding phase is polynomial-time on native field encodings. -/
def computableInPolyTime :
    @TM2ComputableInPolyTime
      (List Nat) (List (PartrecToTM2.Γ' ⊕ Unit))
      PartrecToTM2.Γ' (PartrecToTM2.Γ' ⊕ Unit)
      PartrecToTM2.trList id (spacePaddedNativeFields decider) := by
  let certificate := UnaryPolynomialPaddingMachine.computableInPolyTime
    (Source := PartrecToTM2.Γ') isDelimiter (spaceCoefficients decider)
  refine
    { tm := certificate.tm
      inputAlphabet := certificate.inputAlphabet
      outputAlphabet := certificate.outputAlphabet
      time := certificate.time
      outputsFun := ?_ }
  intro fields
  exact certificate.outputsFun (PartrecToTM2.trList fields)

/-- Alphabet after appending the unary stack width. -/
abbrev SpacePaddedSymbol := PartrecToTM2.Γ' ⊕ Unit

/-- Alphabet after appending both the unary stack and reset-clock widths. -/
abbrev WidthPaddedSymbol := SpacePaddedSymbol ⊕ Unit

/-- Delimiters remain recognizable after the first padding phase. -/
def isSourceDelimiter : SpacePaddedSymbol → Bool
  | .inl symbol => isDelimiter symbol
  | .inr _ => false

theorem selectedCount_map_inl {Source Extra : Type}
    (selected : Source → Bool) (sources : List Source) :
    selectedCount (fun symbol : Source ⊕ Extra =>
        match symbol with
        | .inl source => selected source
        | .inr _ => false)
      (sources.map Sum.inl) =
      selectedCount selected sources := by
  induction sources with
  | nil => rfl
  | cons source sources induction =>
      simp [selectedCount, induction]

theorem selectedCount_replicate_of_false {Source : Type}
    (selected : Source → Bool) (source : Source)
    (notSelected : selected source = false) (count : Nat) :
    selectedCount selected (List.replicate count source) = 0 := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, selectedCount_cons, notSelected]
      simpa using induction

/-- Appending padding does not change the count of a predicate lifted from
the retained source alphabet. -/
theorem selectedCount_paddedOutput {Source : Type}
    (selected : Source → Bool) (coefficients : List Nat)
    (sources : List Source) :
    selectedCount
        (fun symbol : Source ⊕ Unit =>
          match symbol with
          | .inl source => selected source
          | .inr _ => false)
        (paddedOutput selected coefficients sources) =
      selectedCount selected sources := by
  unfold paddedOutput
  rw [selectedCount_append]
  have sourceCount :
      selectedCount
          (fun symbol : Source ⊕ Unit =>
            match symbol with
            | .inl source => selected source
            | .inr _ => false)
          (sources.map Sum.inl) = selectedCount selected sources := by
    induction sources with
    | nil => rfl
    | cons source sources induction =>
        simp [selectedCount, induction]
  rw [sourceCount,
    selectedCount_replicate_of_false
      (fun symbol : Source ⊕ Unit =>
        match symbol with
        | .inl source => selected source
        | .inr _ => false)
      (Sum.inr ()) rfl]
  omega

@[simp]
theorem selectedCount_spacePaddedNativeFields (fields : List Nat) :
    selectedCount isSourceDelimiter
      (spacePaddedNativeFields decider fields) = fields.length := by
  unfold spacePaddedNativeFields paddedOutput
  rw [selectedCount_append]
  change selectedCount isSourceDelimiter
        ((PartrecToTM2.trList fields).map Sum.inl) +
      selectedCount isSourceDelimiter
        (List.replicate
          (evalCoefficients (spaceCoefficients decider)
            (selectedCount isDelimiter (PartrecToTM2.trList fields)))
          (Sum.inr ())) = fields.length
  change selectedCount
        (fun symbol : PartrecToTM2.Γ' ⊕ Unit =>
          match symbol with
          | .inl source => isDelimiter source
          | .inr _ => false)
        ((PartrecToTM2.trList fields).map Sum.inl) +
      selectedCount isSourceDelimiter
        (List.replicate
          (evalCoefficients (spaceCoefficients decider)
            (selectedCount isDelimiter (PartrecToTM2.trList fields)))
          (Sum.inr ())) = fields.length
  have sourceCount :
      selectedCount
          (fun symbol : PartrecToTM2.Γ' ⊕ Unit =>
            match symbol with
            | .inl source => isDelimiter source
            | .inr _ => false)
          ((PartrecToTM2.trList fields).map Sum.inl) =
        selectedCount isDelimiter (PartrecToTM2.trList fields) :=
    by
      induction PartrecToTM2.trList fields with
      | nil => rfl
      | cons symbol symbols induction =>
          simp [selectedCount, induction]
  rw [sourceCount, selectedCount_trList,
    selectedCount_replicate_of_false isSourceDelimiter (Sum.inr ()) rfl]
  omega

/-- Fixed coefficient list for the exact reset-clock width polynomial. -/
def clockCoefficients : List Nat :=
  polynomialCoefficients
    (PolySpaceReduction.reductionClockPolynomial decider)

/-- Physical output after materializing both dynamic widths. -/
def widthsPaddedNativeFields (fields : List Nat) :
    List WidthPaddedSymbol :=
  paddedOutput isSourceDelimiter (clockCoefficients decider)
    (spacePaddedNativeFields decider fields)

@[simp]
theorem evalCoefficients_clockCoefficients (fieldCount : Nat) :
    evalCoefficients (clockCoefficients decider) fieldCount =
      (PolySpaceReduction.reductionClockPolynomial decider).eval
        fieldCount := by
  simp [clockCoefficients]

theorem clockBitsOfSymbols_eq_polynomial_eval
    (symbols : List encoding.Γ) :
    PolySpaceCompiler.clockBitsOfSymbols decider symbols =
      (PolySpaceReduction.reductionClockPolynomial decider).eval
        symbols.length := by
  rw [PolySpaceCompiler.clockBitsOfSymbols,
    BoundedMachineAtom.configurationBitCount_eq,
    spaceOfSymbols_eq_polynomial_eval]
  simp [PolySpaceReduction.reductionClockPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul]

/-- On canonical source fields, the two marker blocks are exactly the stack
and reset-clock widths consumed by the bounded expression printer. -/
@[simp]
theorem widthsPaddedNativeFields_fields (symbols : List encoding.Γ) :
    widthsPaddedNativeFields decider
        (FiniteEncodingNativeFields.fields symbols) =
      (FiniteEncodingNativeFields.encode symbols).map
          (fun symbol => Sum.inl (Sum.inl symbol)) ++
        List.replicate (PolySpaceCompiler.spaceOfSymbols decider symbols)
          (Sum.inl (Sum.inr ())) ++
        List.replicate (PolySpaceCompiler.clockBitsOfSymbols decider symbols)
          (Sum.inr ()) := by
  unfold widthsPaddedNativeFields paddedOutput
  rw [selectedCount_spacePaddedNativeFields,
    FiniteEncodingNativeFields.fields_length,
    evalCoefficients_clockCoefficients,
    ← clockBitsOfSymbols_eq_polynomial_eval,
    spacePaddedNativeFields_fields]
  simp only [List.map_append, List.map_map, List.map_replicate,
    List.append_assoc]
  rfl

/-- The second Horner phase, viewed as a transformation of a word already
carrying unary stack-width padding. -/
def appendClockComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List SpacePaddedSymbol) (List WidthPaddedSymbol)
      SpacePaddedSymbol WidthPaddedSymbol id id
      (paddedOutput isSourceDelimiter (clockCoefficients decider)) :=
  UnaryPolynomialPaddingMachine.computableInPolyTime
    isSourceDelimiter (clockCoefficients decider)

/-- Sequentially materializing both widths remains polynomial-time. -/
def widthsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Nat) (List WidthPaddedSymbol)
      PartrecToTM2.Γ' WidthPaddedSymbol PartrecToTM2.trList id
      (widthsPaddedNativeFields decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (computableInPolyTime decider)
    (appendClockComputableInPolyTime decider)
  exact composed

/-- Alphabet after also appending the first fresh Tseitin atom boundary. -/
abbrev FreshPaddedSymbol := WidthPaddedSymbol ⊕ Unit

/-- Source delimiters remain recognizable after both width blocks. -/
def isSourceDelimiterAfterWidths : WidthPaddedSymbol → Bool
  | .inl symbol => isSourceDelimiter symbol
  | .inr _ => false

@[simp]
theorem selectedCount_widthsPaddedNativeFields (fields : List Nat) :
    selectedCount isSourceDelimiterAfterWidths
      (widthsPaddedNativeFields decider fields) = fields.length := by
  unfold widthsPaddedNativeFields
  change selectedCount
      (fun symbol : SpacePaddedSymbol ⊕ Unit =>
        match symbol with
        | .inl source => isSourceDelimiter source
        | .inr _ => false)
      (paddedOutput isSourceDelimiter (clockCoefficients decider)
        (spacePaddedNativeFields decider fields)) = fields.length
  unfold paddedOutput
  rw [selectedCount_append]
  have sourceCount :
      selectedCount
          (fun symbol : SpacePaddedSymbol ⊕ Unit =>
            match symbol with
            | .inl source => isSourceDelimiter source
            | .inr _ => false)
          ((spacePaddedNativeFields decider fields).map Sum.inl) =
        selectedCount isSourceDelimiter
          (spacePaddedNativeFields decider fields) := by
    induction spacePaddedNativeFields decider fields with
    | nil => rfl
    | cons symbol symbols induction =>
        simp [selectedCount, induction]
  rw [sourceCount,
    selectedCount_replicate_of_false
      (fun symbol : SpacePaddedSymbol ⊕ Unit =>
        match symbol with
        | .inl source => isSourceDelimiter source
        | .inr _ => false)
      (Sum.inr ()) rfl,
    selectedCount_spacePaddedNativeFields]
  omega

/-- Fixed coefficients for the exact source-atom boundary at which the
structural Tseitin evaluator starts allocating fresh atoms. -/
def freshCoefficients : List Nat :=
  polynomialCoefficients
    (PolySpaceReduction.sourceAtomPolynomial decider)

/-- Physical preprocessing output carrying source, space, clock, and fresh
blocks in that order. -/
def freshPaddedNativeFields (fields : List Nat) :
    List FreshPaddedSymbol :=
  paddedOutput isSourceDelimiterAfterWidths (freshCoefficients decider)
    (widthsPaddedNativeFields decider fields)

@[simp]
theorem evalCoefficients_freshCoefficients (fieldCount : Nat) :
    evalCoefficients (freshCoefficients decider) fieldCount =
      (PolySpaceReduction.sourceAtomPolynomial decider).eval
        fieldCount := by
  simp [freshCoefficients]

theorem atomCountOfSymbols_eq_polynomial_eval
    (symbols : List encoding.Γ) :
    BoundedMachineAtom.atomCount (tm := decider.tm)
        (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
        (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols) =
      (PolySpaceReduction.sourceAtomPolynomial decider).eval
        symbols.length := by
  rw [BoundedMachineAtom.atomCount_eq]
  simp only [PolySpaceReduction.sourceAtomPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← spaceOfSymbols_eq_polynomial_eval,
    ← clockBitsOfSymbols_eq_polynomial_eval]

/-- On canonical source fields, the third marker block is exactly the `fresh`
header field of the compact compiler request. -/
@[simp]
theorem freshPaddedNativeFields_fields (symbols : List encoding.Γ) :
    freshPaddedNativeFields decider
        (FiniteEncodingNativeFields.fields symbols) =
      (FiniteEncodingNativeFields.encode symbols).map
          (fun symbol => Sum.inl (Sum.inl (Sum.inl symbol))) ++
        List.replicate (PolySpaceCompiler.spaceOfSymbols decider symbols)
          (Sum.inl (Sum.inl (Sum.inr ()))) ++
        List.replicate (PolySpaceCompiler.clockBitsOfSymbols decider symbols)
          (Sum.inl (Sum.inr ())) ++
        List.replicate
          (BoundedMachineAtom.atomCount (tm := decider.tm)
            (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
            (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols))
          (Sum.inr ()) := by
  unfold freshPaddedNativeFields paddedOutput
  rw [selectedCount_widthsPaddedNativeFields,
    FiniteEncodingNativeFields.fields_length,
    evalCoefficients_freshCoefficients,
    ← atomCountOfSymbols_eq_polynomial_eval,
    widthsPaddedNativeFields_fields]
  simp only [List.map_append, List.map_map, List.map_replicate,
    List.append_assoc]
  rfl

/-- The third Horner phase as a transformation of the doubly padded word. -/
def appendFreshComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List WidthPaddedSymbol) (List FreshPaddedSymbol)
      WidthPaddedSymbol FreshPaddedSymbol id id
      (paddedOutput isSourceDelimiterAfterWidths
        (freshCoefficients decider)) :=
  UnaryPolynomialPaddingMachine.computableInPolyTime
    isSourceDelimiterAfterWidths (freshCoefficients decider)

/-- Source, both widths, and the fresh-atom boundary can all be materialized
sequentially in polynomial time. -/
def freshComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Nat) (List FreshPaddedSymbol)
      PartrecToTM2.Γ' FreshPaddedSymbol PartrecToTM2.trList id
      (freshPaddedNativeFields decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (widthsComputableInPolyTime decider)
    (appendFreshComputableInPolyTime decider)
  exact composed

end PolySpaceRequestPadding
end PeriodicCNF
end LeanTrominoes
