import LeanTrominoes.PeriodicCNFMachineStepAffine
import LeanTrominoes.PeriodicCNFPolySpaceReductionSemantics
import LeanTrominoes.PeriodicCNFFlatEncodingSize

/-!
# Polynomial size of the local periodic-CNF reduction

This file composes the bounded-machine estimates with a source decider's
polynomial space certificate.  It constructs an explicit natural-coefficient
polynomial bounding the number of clauses emitted for an encoded input.
-/

noncomputable section

open scoped BigOperators

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PolySpaceReduction

variable {Input : Type} {encoding : Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- An initial TM2 configuration occupies exactly its input-list length. -/
theorem configurationSpace_initList (symbols : List (decider.tm.Γ decider.tm.k₀)) :
    Complexity.configurationSpace decider.tm (initList decider.tm symbols) =
      symbols.length := by
  classical
  unfold Complexity.configurationSpace
  simp only [initList]
  rw [Fintype.sum_eq_single decider.tm.k₀]
  · simp
  · intro stack stackNe
    simp [stackNe]

/-- Polynomial represented stack width chosen by the reduction. -/
def reductionSpacePolynomial : Polynomial Nat :=
  decider.space + Polynomial.X +
    Polynomial.C (Complexity.configurationSpace decider.tm
      (acceptingConfiguration decider))

/-- The selected stack width is exactly the evaluation of the explicit source
space polynomial. -/
theorem reductionSpace_eq_polynomial_eval (input : Input) :
    reductionSpace decider input =
      (reductionSpacePolynomial decider).eval (encoding.encode input).length := by
  rw [reductionSpace]
  rw [show Complexity.configurationSpace decider.tm
      (initialConfiguration decider input) =
      (encoding.encode input).length by
    unfold initialConfiguration
    rw [configurationSpace_initList]
    simp]
  simp [reductionSpacePolynomial, Polynomial.eval_add]

/-- Polynomial reset-clock width after substituting the stack-width
polynomial into the exact configuration-bit count. -/
def reductionClockPolynomial : Polynomial Nat :=
  Polynomial.C (Fintype.card (Option decider.tm.Λ)) +
    Polynomial.C (Fintype.card decider.tm.σ) +
    reductionSpacePolynomial decider *
      Polynomial.C
        (BoundedMachineAtom.stackCellBitRate (tm := decider.tm))

/-- The reset-clock width is exactly polynomial in encoded input length. -/
theorem reductionClockBits_eq_polynomial_eval (input : Input) :
    reductionClockBits decider input =
      (reductionClockPolynomial decider).eval (encoding.encode input).length := by
  rw [reductionClockBits,
    BoundedMachineAtom.configurationBitCount_eq,
    reductionSpace_eq_polynomial_eval]
  simp [reductionClockPolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Polynomial obtained from the structural well-formedness node budget. -/
def wellFormedNodePolynomial : Polynomial Nat :=
  let stackWidth := reductionSpacePolynomial decider
  (Polynomial.C 2 + Polynomial.C (Fintype.card decider.tm.K) * stackWidth) *
        Polynomial.C
          (BoundedMachineAtom.oneHotFieldNodeBudget (tm := decider.tm) + 1) +
      Polynomial.C 1 +
    (Polynomial.C 5 *
        (Polynomial.C (Fintype.card decider.tm.K) * stackWidth) +
      Polynomial.C 1) +
    Polynomial.C 1

theorem wellFormedNodePolynomial_eval (input : Input) :
    (wellFormedNodePolynomial decider).eval (encoding.encode input).length =
      BoundedMachineAtom.wellFormedNodeBudget (tm := decider.tm)
        (space := reductionSpace decider input) := by
  unfold wellFormedNodePolynomial BoundedMachineAtom.wellFormedNodeBudget
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← reductionSpace_eq_polynomial_eval]

/-- Polynomial obtained from the exact fixed-configuration node count. -/
def fixedConfigNodePolynomial : Polynomial Nat :=
  Polynomial.C (Fintype.card decider.tm.K) *
      (Polynomial.C 2 * reductionSpacePolynomial decider + Polynomial.C 2) +
    Polynomial.C 5

theorem fixedConfigNodePolynomial_eval (input : Input) :
    (fixedConfigNodePolynomial decider).eval (encoding.encode input).length =
      BoundedMachineAtom.fixedConfigNodeCount (tm := decider.tm)
        (space := reductionSpace decider input) := by
  unfold fixedConfigNodePolynomial BoundedMachineAtom.fixedConfigNodeCount
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← reductionSpace_eq_polynomial_eval]

/-- Polynomial for every designated relation component except the ordinary
machine step. -/
def designatedNonStepNodePolynomial : Polynomial Nat :=
  let clockWidth := reductionClockPolynomial decider
  wellFormedNodePolynomial decider +
    Polynomial.C 3 * fixedConfigNodePolynomial decider +
    (Polynomial.C 3 * clockWidth + Polynomial.C 1) +
    Polynomial.C 12 * (clockWidth + Polynomial.C 1) ^ 2 +
    Polynomial.C 7

theorem designatedNonStepNodePolynomial_eval (input : Input) :
    (designatedNonStepNodePolynomial decider).eval
        (encoding.encode input).length =
      BoundedMachineAtom.designatedNonStepNodeBudget (tm := decider.tm)
        (space := reductionSpace decider input)
        (clockBits := reductionClockBits decider input) := by
  unfold designatedNonStepNodePolynomial
    BoundedMachineAtom.designatedNonStepNodeBudget
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow]
  rw [wellFormedNodePolynomial_eval, fixedConfigNodePolynomial_eval,
    ← reductionClockBits_eq_polynomial_eval]

/-- Affine ordinary-step budget composed with the source space polynomial. -/
def machineStepNodePolynomial : Polynomial Nat :=
  Polynomial.C
      (BoundedMachineAtom.machineStepSlope (tm := decider.tm)) *
      reductionSpacePolynomial decider +
    Polynomial.C
      (BoundedMachineAtom.machineStepIntercept (tm := decider.tm))

theorem machineStepNodePolynomial_eval (input : Input) :
    (machineStepNodePolynomial decider).eval (encoding.encode input).length =
      BoundedMachineAtom.machineStepNodeBudget (tm := decider.tm)
        (space := reductionSpace decider input) := by
  unfold machineStepNodePolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← reductionSpace_eq_polynomial_eval,
    BoundedMachineAtom.machineStepNodeBudget_eq_affine]

/-- Polynomial budget for the complete designated transition expression. -/
def designatedMachineNodePolynomial : Polynomial Nat :=
  designatedNonStepNodePolynomial decider + machineStepNodePolynomial decider

theorem designatedMachineNodePolynomial_eval (input : Input) :
    (designatedMachineNodePolynomial decider).eval
        (encoding.encode input).length =
      BoundedMachineAtom.designatedMachineNodeBudget (tm := decider.tm)
        (space := reductionSpace decider input)
        (clockBits := reductionClockBits decider input) := by
  unfold designatedMachineNodePolynomial
    BoundedMachineAtom.designatedMachineNodeBudget
  rw [Polynomial.eval_add, designatedNonStepNodePolynomial_eval,
    machineStepNodePolynomial_eval]

/-- Polynomial for the source-atom boundary at which Tseitin allocation
begins. -/
def sourceAtomPolynomial : Polynomial Nat :=
  Polynomial.C (Fintype.card (Option decider.tm.Λ)) +
    Polynomial.C (Fintype.card decider.tm.σ) +
    reductionSpacePolynomial decider *
      Polynomial.C
        (BoundedMachineAtom.stackCellBitRate (tm := decider.tm)) +
    reductionClockPolynomial decider

theorem sourceAtomPolynomial_eval (input : Input) :
    (sourceAtomPolynomial decider).eval (encoding.encode input).length =
      BoundedMachineAtom.atomCount (tm := decider.tm)
        (space := reductionSpace decider input)
        (clockBits := reductionClockBits decider input) := by
  unfold sourceAtomPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← reductionSpace_eq_polynomial_eval,
    ← reductionClockBits_eq_polynomial_eval,
    BoundedMachineAtom.atomCount_eq]

/-- Polynomial upper boundary for every source and generated atom occurring
in the emitted formula. -/
def formulaAtomPolynomial : Polynomial Nat :=
  sourceAtomPolynomial decider + designatedMachineNodePolynomial decider

theorem formulaAtomPolynomial_eval (input : Input) :
    (formulaAtomPolynomial decider).eval (encoding.encode input).length =
      BoundedMachineAtom.atomCount (tm := decider.tm)
          (space := reductionSpace decider input)
          (clockBits := reductionClockBits decider input) +
        BoundedMachineAtom.designatedMachineNodeBudget (tm := decider.tm)
          (space := reductionSpace decider input)
          (clockBits := reductionClockBits decider input) := by
  unfold formulaAtomPolynomial
  rw [Polynomial.eval_add, sourceAtomPolynomial_eval,
    designatedMachineNodePolynomial_eval]

/-- Explicit polynomial clause budget for the local periodic-CNF reduction. -/
def formulaClausePolynomial : Polynomial Nat :=
  Polynomial.C 3 * designatedMachineNodePolynomial decider + Polynomial.C 1

/-- The actual emitted horizontal CNF has polynomially many clauses in the
encoded source input length. -/
theorem formula_clause_length_le_polynomial_eval (input : Input) :
    (formula decider input).clauses.length ≤
      (formulaClausePolynomial decider).eval (encoding.encode input).length := by
  apply (BoundedMachineAtom.designatedMachinePeriodicCNF_clause_length_le_budget
    (initialConfiguration decider input)
    (acceptingConfiguration decider)).trans
  unfold formulaClausePolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [designatedMachineNodePolynomial_eval]

/-- Explicit polynomial bound on the number of symbols in the flat output
encoding, rather than merely on its number of clauses. -/
def formulaEncodingPolynomial : Polynomial Nat :=
  let clauses := formulaClausePolynomial decider
  let atoms := formulaAtomPolynomial decider
  Polynomial.C 1 + Polynomial.C 2 * clauses +
    clauses * Polynomial.C 3 *
      (atoms + Polynomial.C
        (PeriodicCNFFlatEncoding.forwardLiteralFieldBudget + 5))

/-- The complete emitted flat formula encoding has polynomial length in the
encoded source input. -/
theorem formula_encoding_length_le_polynomial_eval (input : Input) :
    (PeriodicCNFFlatEncoding.finEncoding.encode
      (formula decider input)).length ≤
      (formulaEncodingPolynomial decider).eval
        (encoding.encode input).length := by
  let space := reductionSpace decider input
  let clockBits := reductionClockBits decider input
  let initial := initialConfiguration decider input
  let accepting := acceptingConfiguration decider
  let expression :=
    BoundedMachineAtom.designatedMachineResetClockExpression
      (tm := decider.tm) (space := space) (clockBits := clockBits)
      initial accepting
  let fresh := BoundedMachineAtom.atomCount (tm := decider.tm)
    (space := space) (clockBits := clockBits)
  let clauseBound :=
    (formulaClausePolynomial decider).eval
      (encoding.encode input).length
  let atomBound :=
    (formulaAtomPolynomial decider).eval
      (encoding.encode input).length
  have sourceAtoms : expression.AtomsBelow fresh := by
    exact BoundedMachineAtom.designatedMachineResetClockExpression_atomsBelow
      initial accepting
  have gateBound : expression.gateCount ≤
      BoundedMachineAtom.designatedMachineNodeBudget (tm := decider.tm)
        (space := space) (clockBits := clockBits) := by
    exact BoundedMachineAtom.designatedMachineResetClockExpression_gateCount_le_budget
      initial accepting
  have atoms : ClausesAtomsBelow
      (requireTransitionExpr expression fresh).clauses atomBound := by
    apply clausesAtomsBelow_mono
      (requireTransitionExpr_atomsBelow expression fresh sourceAtoms)
    dsimp [atomBound, fresh]
    rw [formulaAtomPolynomial_eval]
    exact Nat.add_le_add_left gateBound _
  have clauses : (requireTransitionExpr expression fresh).clauses.length ≤
      clauseBound := by
    change (formula decider input).clauses.length ≤ clauseBound
    exact formula_clause_length_le_polynomial_eval decider input
  have encoded := PeriodicCNFFlatEncoding.finEncoding_encode_length_le
    (requireTransitionExpr expression fresh) 3 atomBound clauseBound
    (requireTransitionExpr_widthAtMost_three expression fresh)
    (requireTransitionExpr_forward expression fresh) atoms clauses
  change (PeriodicCNFFlatEncoding.finEncoding.encode
    (requireTransitionExpr expression fresh)).length ≤ _
  apply encoded.trans_eq
  unfold formulaEncodingPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rfl

end PolySpaceReduction

end PeriodicCNF

end LeanTrominoes
