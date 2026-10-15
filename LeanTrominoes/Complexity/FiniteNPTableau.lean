/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.NP
import LeanTrominoes.Complexity.FiniteCertificateCNF
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Finite 3CNF tableaux for polynomial-time NP verifiers

This module proves the semantic reduction and polynomial formula-size bound.
A machine that emits the formula in polynomial time is a separate obligation.
-/
noncomputable section
namespace LeanTrominoes.Complexity.VerifierInPolyTime
open Computability Turing
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (verifier : VerifierInPolyTime encoding language)
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
noncomputable local instance (stack : verifier.computer.tm.K) :
    Fintype (verifier.computer.tm.Γ stack) := verifier.computer.stackAlphabetFinite stack

def initialPrefix (input : Input) : List (verifier.computer.tm.Γ verifier.computer.tm.k₀) :=
  (((encoding.encode input).map Sum.inl)++[Sum.inr none]).map verifier.computer.inputAlphabet.invFun

def certificateBit (bit : Bool) : verifier.computer.tm.Γ verifier.computer.tm.k₀ :=
  verifier.computer.inputAlphabet.invFun (Sum.inr (some bit))

def acceptingWord : List (verifier.computer.tm.Γ verifier.computer.tm.k₁) :=
  ((primcodableFinEncoding Bool).encode true).map verifier.computer.outputAlphabet.invFun

def acceptingConfiguration : verifier.computer.tm.Cfg :=
  haltList verifier.computer.tm (acceptingWord verifier)

def timePolynomial : Polynomial Nat :=
  verifier.computer.time.comp (Polynomial.X+verifier.witnessBound+1)

def timeLimit (input : Input) : Nat := (timePolynomial verifier).eval (encoding.encode input).length

def spacePolynomial : Polynomial Nat :=
  Polynomial.X+1+verifier.witnessBound+
    timePolynomial verifier*Polynomial.C (TM2OutputLength.machinePushBound verifier.computer.tm)+
    Polynomial.C (acceptingWord verifier).length

def spaceLimit (input : Input) : Nat := (spacePolynomial verifier).eval (encoding.encode input).length

@[simp] theorem initialPrefix_length (input : Input) :
    (initialPrefix verifier input).length=(encoding.encode input).length+1 := by
  simp [initialPrefix]

theorem inputWord (input : Input) (certificate : List Bool) :
    initialPrefix verifier input++certificate.map (certificateBit verifier)=
      (encodeWitness encoding (input,certificate)).map verifier.computer.inputAlphabet.invFun := by
  simp [initialPrefix,certificateBit,encodeWitness,List.map_append,List.map_map,Function.comp_def]

theorem timeLimit_eq (input : Input) : timeLimit verifier input=
    verifier.computer.time.eval ((encoding.encode input).length+
      verifier.witnessBound.eval (encoding.encode input).length+1) := by
  simp [timeLimit,timePolynomial]

theorem spaceLimit_eq (input : Input) : spaceLimit verifier input=
    (initialPrefix verifier input).length+verifier.witnessBound.eval (encoding.encode input).length+
      timeLimit verifier input*TM2OutputLength.machinePushBound verifier.computer.tm+
      (acceptingWord verifier).length := by
  simp [spaceLimit,spacePolynomial,timeLimit]

theorem acceptance_iff (input : Input) (certificate : List Bool)
    (bounded : certificate.length ≤ verifier.witnessBound.eval (encoding.encode input).length) :
    Nonempty (StateTransition.EvalsToInTime verifier.computer.tm.step
      (initList verifier.computer.tm (initialPrefix verifier input++certificate.map (certificateBit verifier)))
      (some (acceptingConfiguration verifier)) (timeLimit verifier input)) ↔
      verifier.verify input certificate=true := by
  have actualRun := verifier.computer.outputsFun (input,certificate)
  constructor
  · rintro ⟨acceptedRun⟩
    let actualTerminal := haltList verifier.computer.tm
      (((primcodableFinEncoding Bool).encode (verifier.verify input certificate)).map
        verifier.computer.outputAlphabet.invFun)
    have run : StateTransition.EvalsTo verifier.computer.tm.step
        (initList verifier.computer.tm (initialPrefix verifier input++certificate.map (certificateBit verifier)))
        (some actualTerminal) := by
      simpa only [inputWord,TM2OutputsInTime,Option.map_some,actualTerminal] using actualRun.toEvalsTo
    have eq := PeriodicComputation.eq_of_reachable_terminals
      (PeriodicComputation.evalsTo_reaches run)
      (PeriodicComputation.evalsTo_reaches acceptedRun.toEvalsTo) (by rfl) (by rfl)
    have stackEq := congrArg (fun cfg : verifier.computer.tm.Cfg => cfg.stk verifier.computer.tm.k₁) eq
    have mapped :
        (((primcodableFinEncoding Bool).encode (verifier.verify input certificate)).map
          verifier.computer.outputAlphabet.invFun)=acceptingWord verifier := by
      simpa [actualTerminal,acceptingConfiguration,haltList] using stackEq
    have encoded := (List.map_injective_iff.mpr verifier.computer.outputAlphabet.symm.injective) mapped
    exact _root_.Computability.Encoding.encode_injective (primcodableFinEncoding Bool).encoding encoded
  · intro accepted
    have actualSteps : actualRun.steps ≤ timeLimit verifier input := by
      apply actualRun.steps_le_m.trans
      rw [timeLimit_eq]
      apply TM2CompositionMachine.polynomial_eval_monotone
      rw [encodeWitness_length]
      dsimp only [Prod.fst,Prod.snd]
      omega
    refine ⟨⟨⟨actualRun.steps,?_⟩,actualSteps⟩⟩
    simpa only [inputWord,TM2OutputsInTime,Option.map_some,accepted,
      acceptingConfiguration,acceptingWord] using actualRun.evals_in_steps

def tableau (input : Input) : FiniteCNF.Formula (Nat × Nat) :=
  FiniteCertificate.formula verifier.computer.tm (spaceLimit verifier input)
    (initialPrefix verifier input) (certificateBit verifier)
    (verifier.witnessBound.eval (encoding.encode input).length)
    (acceptingConfiguration verifier) (timeLimit verifier input)

theorem tableau_correct (input : Input) : FiniteCNF.Satisfiable (tableau verifier input) ↔ language input := by
  have enough : (initialPrefix verifier input).length+verifier.witnessBound.eval (encoding.encode input).length+
      timeLimit verifier input*TM2OutputLength.machinePushBound verifier.computer.tm ≤ spaceLimit verifier input := by
    rw [spaceLimit_eq]
    omega
  have finalFits (stack : verifier.computer.tm.K) :
      ((acceptingConfiguration verifier).stk stack).length ≤ spaceLimit verifier input := by
    have room : (acceptingWord verifier).length ≤ spaceLimit verifier input := by
      rw [spaceLimit_eq]
      omega
    by_cases same : stack=verifier.computer.tm.k₁
    · subst stack
      simpa [acceptingConfiguration,haltList] using room
    · simp [acceptingConfiguration,haltList,same]
  rw [tableau,FiniteCertificate.formula_correct _ _ _ _ _ _ _ enough finalFits,verifier.correct input]
  apply exists_congr
  intro certificate
  exact and_congr_right (fun bounded => acceptance_iff verifier input certificate bounded)

theorem tableau_width (input : Input) : FiniteCNF.WidthAtMost 3 (tableau verifier input) :=
  FiniteCertificate.formula_width _ _ _ _ _ _ _

def tableauClausePolynomial : Polynomial Nat :=
  (timePolynomial verifier+1)*
    (Polynomial.C 3*(Polynomial.C (FiniteMachineTrace.paddedTraceSlope verifier.computer.tm)*spacePolynomial verifier+
      Polynomial.C (FiniteMachineTrace.paddedTraceIntercept verifier.computer.tm)+
      (Polynomial.C (Fintype.card verifier.computer.tm.K)*(Polynomial.C 2*spacePolynomial verifier+2)+
        Polynomial.C 6*spacePolynomial verifier+7))+1)

theorem tableau_length_le (input : Input) :
    (tableau verifier input).length ≤ (tableauClausePolynomial verifier).eval (encoding.encode input).length := by
  have h := FiniteCertificate.formula_length_le verifier.computer.tm (spaceLimit verifier input)
    (initialPrefix verifier input) (certificateBit verifier)
    (verifier.witnessBound.eval (encoding.encode input).length) (acceptingConfiguration verifier) (timeLimit verifier input)
  simpa [tableau,tableauClausePolynomial,timeLimit,spaceLimit] using h

end LeanTrominoes.Complexity.VerifierInPolyTime
