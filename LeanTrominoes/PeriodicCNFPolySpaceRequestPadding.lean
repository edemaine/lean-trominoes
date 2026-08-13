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

end PolySpaceRequestPadding
end PeriodicCNF
end LeanTrominoes
