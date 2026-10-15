/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteCNFCompilerSize
import LeanTrominoes.Complexity.FiniteNPTableauEncoding

/-! # Correct bounded native compiler requests for NP verifiers

The semantic request and native CNF backend are complete. A polynomial-time
source-to-request emitter is still needed to establish an NP-hardness endpoint.
-/
noncomputable section
namespace LeanTrominoes.Complexity.VerifierInPolyTime
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (verifier : VerifierInPolyTime encoding language)
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack

def expressions (input : Input) : Nat → TransitionExpr :=
  FiniteMachineTrace.symbolicExpression verifier.computer.tm (spaceLimit verifier input)
    (FiniteCertificate.initialExpression verifier.computer.tm (spaceLimit verifier input)
      (initialPrefix verifier input) (certificateBit verifier)
      (verifier.witnessBound.eval (encoding.encode input).length))
    (acceptingConfiguration verifier) (timeLimit verifier input)

theorem expressions_atomsBelow (input : Input) (time : Nat) :
    (expressions verifier input time).AtomsBelow
      ((tableauSourcePolynomial verifier).eval (encoding.encode input).length) := by
  rw [tableauSourcePolynomial_eval]
  exact FiniteMachineTrace.symbolicExpression_atomsBelow _ _ _ _ _ _
    (FiniteCertificate.initialExpression_atomsBelow _ _ _ _ _)

def requestFreshPolynomial : Polynomial Nat :=
  (timePolynomial verifier+1+tableauSourcePolynomial verifier+1)^2

def nativeRequest (input : Input) : FiniteCNFCompiler.Request where
  expression := FiniteCNF.tableauExpression (expressions verifier input) (timeLimit verifier input+1)
  fresh := (requestFreshPolynomial verifier).eval (encoding.encode input).length
  sourceBound := by
    have h := FiniteCNF.tableauExpression_atomsBelow (expressions verifier input)
      ((tableauSourcePolynomial verifier).eval (encoding.encode input).length) (timeLimit verifier input+1)
      (fun time _ => expressions_atomsBelow verifier input time)
    simpa [requestFreshPolynomial,timeLimit,Nat.add_assoc] using h

theorem nativeRequest_correct (input : Input) :
    FiniteCNF.Satisfiable (nativeRequest verifier input).compile ↔ language input := by
  rw [FiniteCNFCompiler.Request.correct]
  change (∃ assignment : Nat → Bool,
    (FiniteCNF.tableauExpression (expressions verifier input) (timeLimit verifier input+1)).eval assignment assignment=true) ↔ _
  rw [FiniteCNF.tableauExpression_correct (expressions verifier input)
    ((tableauSourcePolynomial verifier).eval (encoding.encode input).length) (timeLimit verifier input+1)
    (fun time _ => expressions_atomsBelow verifier input time)]
  have h := tableau_correct verifier input
  rw [tableauSourcePolynomial_eval]
  exact h

theorem nativeRequest_width (input : Input) :
    FiniteCNF.WidthAtMost 3 (nativeRequest verifier input).compile := FiniteCNFCompiler.Request.width _

def requestGatePolynomial : Polynomial Nat :=
  (timePolynomial verifier+1)*(tableauGatePolynomial verifier+1)+1

theorem nativeRequest_gateCount_le (input : Input) :
    (nativeRequest verifier input).expression.gateCount ≤
      (requestGatePolynomial verifier).eval (encoding.encode input).length := by
  have h := FiniteCNF.tableauExpression_gateCount_le (expressions verifier input)
    (timeLimit verifier input+1) ((tableauGatePolynomial verifier).eval (encoding.encode input).length)
    (fun time _ => tableau_expression_gateCount_le verifier input time)
  simpa [nativeRequest,requestGatePolynomial,timeLimit] using h

def requestSizePolynomial : Polynomial Nat :=
  requestFreshPolynomial verifier+3+
    requestGatePolynomial verifier*(requestFreshPolynomial verifier+10)

theorem nativeRequest_encode_length_le (input : Input) :
    (nativeRequest verifier input).encode.length ≤
      (requestSizePolynomial verifier).eval (encoding.encode input).length := by
  have h := FiniteCNFCompiler.Request.encode_length_le (nativeRequest verifier input)
  have gates := nativeRequest_gateCount_le verifier input
  have total := h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right ((nativeRequest verifier input).fresh+10) gates)
    ((nativeRequest verifier input).fresh+3))
  simpa [nativeRequest,requestSizePolynomial] using total

def backendTimePolynomial : Polynomial Nat :=
  Polynomial.C 400*(requestSizePolynomial verifier+1)^2

theorem nativeRequest_backend_time_le (input : Input) :
    FiniteCNFCompiler.computableInPolyTime.time.eval (nativeRequest verifier input).encode.length ≤
      (backendTimePolynomial verifier).eval (encoding.encode input).length := by
  rw [FiniteCNFCompiler.compiler_time]
  have h := Nat.add_le_add_right (nativeRequest_encode_length_le verifier input) 1
  have bound := Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left h 2)
  simpa [backendTimePolynomial] using bound

end LeanTrominoes.Complexity.VerifierInPolyTime
