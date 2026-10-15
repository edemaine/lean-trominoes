/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteNPTableau
import LeanTrominoes.SAT.CNF.FiniteCNFFlatEncoding

/-! # Polynomial encoded length of NP tableaux -/
noncomputable section
namespace LeanTrominoes.Complexity.VerifierInPolyTime
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (verifier : VerifierInPolyTime encoding language)
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack

def tableauGatePolynomial : Polynomial Nat :=
  Polynomial.C (FiniteMachineTrace.paddedTraceSlope verifier.computer.tm)*spacePolynomial verifier+
    Polynomial.C (FiniteMachineTrace.paddedTraceIntercept verifier.computer.tm)+
    (Polynomial.C (Fintype.card verifier.computer.tm.K)*(Polynomial.C 2*spacePolynomial verifier+2)+
      Polynomial.C 6*spacePolynomial verifier+7)

def tableauSourcePolynomial : Polynomial Nat :=
  Polynomial.C (Fintype.card (Option verifier.computer.tm.Λ)+Fintype.card verifier.computer.tm.σ)+
    spacePolynomial verifier*Polynomial.C (stackSymbolCount (tm := verifier.computer.tm))

theorem tableauSourcePolynomial_eval (input : Input) :
    (tableauSourcePolynomial verifier).eval (encoding.encode input).length=
      atomCount (tm := verifier.computer.tm) (space := spaceLimit verifier input) (clockBits := 0) := by
  simp [tableauSourcePolynomial,atomCount,spaceLimit]
  omega

theorem tableau_expression_gateCount_le (input : Input) (time : Nat) :
    (FiniteMachineTrace.symbolicExpression verifier.computer.tm (spaceLimit verifier input)
      (FiniteCertificate.initialExpression verifier.computer.tm (spaceLimit verifier input)
        (initialPrefix verifier input) (certificateBit verifier)
        (verifier.witnessBound.eval (encoding.encode input).length))
      (acceptingConfiguration verifier) (timeLimit verifier input) time).gateCount ≤
      (tableauGatePolynomial verifier).eval (encoding.encode input).length := by
  have h := FiniteMachineTrace.symbolicExpression_gateCount_le verifier.computer.tm
    (spaceLimit verifier input) (FiniteCertificate.initialExpression verifier.computer.tm (spaceLimit verifier input)
      (initialPrefix verifier input) (certificateBit verifier)
      (verifier.witnessBound.eval (encoding.encode input).length)) (acceptingConfiguration verifier) (timeLimit verifier input) time
  have count := FiniteCertificate.initialExpression_gateCount_le verifier.computer.tm
    (spaceLimit verifier input) (initialPrefix verifier input) (certificateBit verifier)
    (verifier.witnessBound.eval (encoding.encode input).length)
  have total := h.trans (Nat.add_le_add_left count (FiniteMachineTrace.paddedNodeBudget verifier.computer.tm (spaceLimit verifier input)))
  simpa [FiniteMachineTrace.paddedNodeBudget_affine,tableauGatePolynomial,spaceLimit] using total

theorem tableau_variable_bounds (input : Input) (clause : FiniteCNF.Clause (Nat × Nat))
    (member : clause∈tableau verifier input) (literal : FiniteCNF.Literal (Nat × Nat)) (hl : literal∈clause) :
    literal.1.1 ≤ timeLimit verifier input+1 ∧ literal.1.2 ≤
      (tableauSourcePolynomial verifier+tableauGatePolynomial verifier).eval (encoding.encode input).length := by
  have source := FiniteCertificate.initialExpression_atomsBelow verifier.computer.tm
    (spaceLimit verifier input) (initialPrefix verifier input) (certificateBit verifier)
    (verifier.witnessBound.eval (encoding.encode input).length)
  have ranges := FiniteCNF.traceFormula_variable_bounds
    (FiniteMachineTrace.symbolicExpression verifier.computer.tm (spaceLimit verifier input) _
      (acceptingConfiguration verifier) (timeLimit verifier input))
    (atomCount (tm := verifier.computer.tm) (space := spaceLimit verifier input) (clockBits := 0))
    (timeLimit verifier input+1)
    ((tableauGatePolynomial verifier).eval (encoding.encode input).length)
    (fun time _ => FiniteMachineTrace.symbolicExpression_atomsBelow _ _ _ _ _ time source)
    (fun time _ => tableau_expression_gateCount_le verifier input time) clause member literal hl
  refine ⟨ranges.1,?_⟩
  rw [Polynomial.eval_add,tableauSourcePolynomial_eval]
  exact ranges.2.le

def tableauEncodingPolynomial : Polynomial Nat :=
  1+Polynomial.C 2*tableauClausePolynomial verifier+
    tableauClausePolynomial verifier*Polynomial.C 3*
      ((timePolynomial verifier+1+tableauSourcePolynomial verifier+tableauGatePolynomial verifier+1)^2+
        Polynomial.C PeriodicCNFFlatEncoding.forwardLiteralFieldBudget+5)

theorem tableau_encode_length_le (input : Input) :
    (FiniteCNFFlatEncoding.finEncoding.encode (tableau verifier input)).length ≤
      (tableauEncodingPolynomial verifier).eval (encoding.encode input).length := by
  have h := FiniteCNFFlatEncoding.encode_length_le (tableau verifier input)
    (timeLimit verifier input+1)
    ((tableauSourcePolynomial verifier+tableauGatePolynomial verifier).eval (encoding.encode input).length)
    ((tableauClausePolynomial verifier).eval (encoding.encode input).length)
    (tableau_width verifier input) (tableau_variable_bounds verifier input) (tableau_length_le verifier input)
  simpa [tableauEncodingPolynomial,timeLimit,Polynomial.eval_add,Nat.add_assoc] using h

end LeanTrominoes.Complexity.VerifierInPolyTime
