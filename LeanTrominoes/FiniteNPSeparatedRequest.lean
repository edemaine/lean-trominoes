/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteSeparatedTableau
import LeanTrominoes.FiniteNPInitializationEmitter
import LeanTrominoes.FiniteNPPaddedProgramEmitter

/-! # Correct finite compiler requests in the order emitted by the machine -/
noncomputable section
namespace LeanTrominoes.Complexity.VerifierInPolyTime
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
open FiniteNPMachineProgramEmitter (sourceSpace)
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (verifier : VerifierInPolyTime encoding language)
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack

def sourceInitialExpression (symbols : List encoding.Γ) : TransitionExpr :=
  FiniteCertificate.initialExpression verifier.computer.tm (sourceSpace verifier symbols)
    (FiniteNPCertificateStackEmitter.initialWord verifier symbols) (certificateBit verifier)
    (verifier.witnessBound.eval symbols.length)

def sourceSeparatedExpression (symbols : List encoding.Γ) : TransitionExpr :=
  FiniteMachineTrace.separatedExpression verifier.computer.tm (sourceSpace verifier symbols)
    (sourceInitialExpression verifier symbols) (acceptingConfiguration verifier)
    ((timePolynomial verifier).eval symbols.length)

def separatedRequest (input : Input) : FiniteCNFCompiler.Request where
  expression := sourceSeparatedExpression verifier (encoding.encode input)
  fresh := (requestFreshPolynomial verifier).eval (encoding.encode input).length
  sourceBound := by
    have bound := FiniteMachineTrace.separatedExpression_atomsBelow verifier.computer.tm
      (sourceSpace verifier (encoding.encode input))
      (sourceInitialExpression verifier (encoding.encode input)) (acceptingConfiguration verifier)
      ((timePolynomial verifier).eval (encoding.encode input).length)
      (FiniteCertificate.initialExpression_atomsBelow _ _ _ _ _)
    simpa [sourceSeparatedExpression,requestFreshPolynomial,tableauSourcePolynomial_eval,
      sourceSpace,spaceLimit,Nat.add_assoc] using bound

theorem separatedRequest_correct (input : Input) :
    FiniteCNF.Satisfiable (separatedRequest verifier input).compile ↔ language input := by
  rw [FiniteCNFCompiler.Request.correct]
  have original := nativeRequest_correct verifier input
  rw [FiniteCNFCompiler.Request.correct] at original
  rw [← original]
  apply exists_congr
  intro assignment
  simpa [separatedRequest,sourceSeparatedExpression,sourceInitialExpression,sourceSpace,
    spaceLimit,timeLimit,nativeRequest,expressions,FiniteNPCertificateStackEmitter.initialWord_encode] using
    FiniteMachineTrace.separatedExpression_eval verifier.computer.tm (spaceLimit verifier input)
      (FiniteCertificate.initialExpression verifier.computer.tm (spaceLimit verifier input)
        (initialPrefix verifier input) (certificateBit verifier)
        (verifier.witnessBound.eval (encoding.encode input).length))
      (acceptingConfiguration verifier) (timeLimit verifier input) assignment

theorem separatedRequest_width (input : Input) :
    FiniteCNF.WidthAtMost 3 (separatedRequest verifier input).compile :=
  FiniteCNFCompiler.Request.width _

theorem sourceSeparatedExpression_atCurrent (symbols : List encoding.Γ) :
    (sourceSeparatedExpression verifier symbols).atCurrent=sourceSeparatedExpression verifier symbols :=
  FiniteMachineTrace.separatedExpression_atCurrent _ _ _ _ _

end LeanTrominoes.Complexity.VerifierInPolyTime
