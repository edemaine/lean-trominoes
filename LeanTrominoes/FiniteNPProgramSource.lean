/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.FiniteNPRequestEmitter
import LeanTrominoes.FiniteCNFZeroOffsets

/-! # The finite Cook–Levin printer supplies the shared geometry interface -/
noncomputable section
namespace LeanTrominoes.FiniteNPProgramSource
open _root_.Computability Turing PeriodicCNF UnaryProgramTokens
open Complexity.VerifierInPolyTime FiniteNPMachineProgramEmitter FiniteNPTokenAssembly
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (verifier : Complexity.VerifierInPolyTime encoding language)
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack

def request (symbols : List encoding.Γ) : TransitionEvaluatorMachine.TransitionCompilerRequest where
  expression := sourceSeparatedExpression verifier symbols
  fresh := (requestFreshPolynomial verifier).eval symbols.length
  sourceBound := by
    have bound := FiniteMachineTrace.separatedExpression_atomsBelow verifier.computer.tm
      (sourceSpace verifier symbols) (sourceInitialExpression verifier symbols) (acceptingConfiguration verifier)
      ((timePolynomial verifier).eval symbols.length)
      (FiniteCertificate.initialExpression_atomsBelow _ _ _ _ _)
    have scalarEq : (tableauSourcePolynomial verifier).eval symbols.length=
        BoundedMachineAtom.atomCount (tm := verifier.computer.tm)
          (space := sourceSpace verifier symbols) (clockBits := 0) := by
      simp [tableauSourcePolynomial,BoundedMachineAtom.atomCount,sourceSpace]
      omega
    rw [← scalarEq] at bound
    simpa [sourceSeparatedExpression,requestFreshPolynomial,Nat.add_assoc] using bound

def formula (symbols : List encoding.Γ) : PeriodicCNF Nat :=
  requireTransitionExpr (request verifier symbols).expression (request verifier symbols).fresh

def tokens (symbols : List encoding.Γ) : List Token :=
  requestSource (request verifier symbols).fresh (request verifier symbols).expression.program

def tokensComputableInPolyTime : TM2ComputableInPolyTime id id (tokens verifier) := by
  let fresh := freshCompiler (polynomialScalar (Source := encoding.Γ) (requestFreshPolynomial verifier))
  let root : TM2ComputableInPolyTime (id : List encoding.Γ → List encoding.Γ) id
      (fun _ => [Token.clauseMarker]) := TM2ConstantValueCompiler.computableInPolyTime id id [Token.clauseMarker]
  let header := TM2ListAppend.nativeComputableInPolyTime fresh root
  let complete := TM2ListAppend.nativeComputableInPolyTime header
    (FiniteNPRequestEmitter.programComputableInPolyTime verifier)
  exact complete.of_eq (fun _ => by simp [tokens,request,requestSource,List.append_assoc])

private def requestComputableInPolyTime : TM2ComputableInPolyTime id
    TransitionEvaluatorMachine.TransitionCompilerRequest.encode (request verifier) := by
  let binary := TM2CompositionMachine.computableInPolyTime
    (FiniteNPRequestEmitter.fieldsComputableInPolyTime verifier) UnaryFieldEncoderMachine.computableInPolyTime
  refine { tm := binary.tm
           inputAlphabet := binary.inputAlphabet
           outputAlphabet := binary.outputAlphabet
           time := binary.time
           outputsFun := ?_ }
  intro symbols
  exact binary.outputsFun symbols

def formulaComputableInPolyTime : TM2ComputableInPolyTime id
    PeriodicCNFFlatEncoding.finEncoding.encode (formula verifier) := by
  let compiled := TM2CompositionMachine.computableInPolyTime (requestComputableInPolyTime verifier)
    TransitionEvaluatorMachine.computableInPolyTime
  refine { tm := compiled.tm
           inputAlphabet := compiled.inputAlphabet
           outputAlphabet := compiled.outputAlphabet
           time := compiled.time
           outputsFun := ?_ }
  intro symbols
  have result := compiled.outputsFun symbols
  have eq : (request verifier symbols).compile=PeriodicCNFFlatEncoding.formulaFields (formula verifier symbols) :=
    requireTransitionExprFields_eq_formulaFields _ _
  rw [eq,PolySpaceNativeCompiler.trList_formulaFields_eq_finEncoding_encode] at result
  exact result

theorem formula_zero (symbols : List encoding.Γ) : FiniteCNF.ZeroOffsets (formula verifier symbols) := by
  have zero := FiniteCNFCompiler.required_zeroOffsets (sourceSeparatedExpression verifier symbols)
    ((requestFreshPolynomial verifier).eval symbols.length)
  rw [sourceSeparatedExpression_atCurrent] at zero
  exact zero

theorem correct (input : Input) : language input ↔ LocalPeriodicCNF1DSAT
    (formula verifier (encoding.encode input)) := by
  have finiteEq : FiniteCNF.erase (formula verifier (encoding.encode input))=(separatedRequest verifier input).compile := by
    change FiniteCNF.erase (requireTransitionExpr _ _)=FiniteCNFCompiler.erase
      (requireTransitionExpr (sourceSeparatedExpression verifier (encoding.encode input)).atCurrent _)
    rw [sourceSeparatedExpression_atCurrent]
    rfl
  have semantic : language input ↔ (formula verifier (encoding.encode input)).Satisfiable := by
    rw [← FiniteCNF.satisfiable_erase _ (formula_zero verifier _),finiteEq]
    exact (separatedRequest_correct verifier input).symm
  have forward := requireTransitionExpr_forward (request verifier (encoding.encode input)).expression
    (request verifier (encoding.encode input)).fresh
  have horizontal := isOneDimensional_of_isForwardLocal forward
  exact ⟨fun truth => ⟨horizontal,isLocalOnLine_of_isForwardLocal forward,
      (satisfiable_iff_satisfiableOnLine horizontal).mp (semantic.mp truth)⟩,
    fun truth => semantic.mpr ((satisfiable_iff_satisfiableOnLine horizontal).mpr truth.2.2)⟩

/-- The same interface and the same verified geometry machines accept finite
NP tableaux, with zero offsets and no decider-specific assumptions. -/
def source : ProgramSource encoding language where
  request := request verifier
  formulaOfSymbols := formula verifier
  formula_eq := fun _ => rfl
  sourceTokens := tokens verifier
  sourceTokens_eq_requestSource := fun _ => rfl
  sourceTokensComputableInPolyTime := tokensComputableInPolyTime verifier
  directSourceFormulaComputableInPolyTime := formulaComputableInPolyTime verifier
  correct := correct verifier
end LeanTrominoes.FiniteNPProgramSource
