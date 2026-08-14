/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineBivariateClockSuccessorTemplates

/-!
# Semantic contract for a triangular template emitter

One outer position emits a fixed outer template, the same equality template
at every strictly higher position, a base and one closer per higher position,
a fixed frame closer, and a second outer template.  Recursion ends in a fixed
base and appends one unwind block per outer position.  This finite recipe
contract is exactly the pattern required by clock succession.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace TriangularTemplateEmitter

open UnaryProgramTokens

abbrev Recipe := BivariateProgramTemplates.Recipe

/-- Repeat one fixed token block without changing its internal order. -/
def repeatTokens (tokens : List Token) : Nat → List Token
  | 0 => []
  | count + 1 => tokens ++ repeatTokens tokens count

/-- Token prefix belonging to one outer position. -/
def frameTokens (outerFirst inner outerSecond : List Recipe)
    (innerBase innerCloser frameCloser : List Token)
    (first position higherCount : Nat) : List Token :=
  BivariateProgramTemplates.positionTokens outerFirst first position ++
    BivariateTemplateEmitterMachine.positionRangeTokens inner first
      (position + 1) higherCount ++
    innerBase ++
    repeatTokens innerCloser higherCount ++
    frameCloser ++
    BivariateProgramTemplates.positionTokens outerSecond first position

/-- Recursive triangular stream beginning at one outer position. -/
def emittedAux (outerFirst inner outerSecond : List Recipe)
    (innerBase innerCloser frameCloser finalBase finalCloser : List Token)
    (first position : Nat) : Nat → List Token
  | 0 => finalBase
  | count + 1 =>
      frameTokens outerFirst inner outerSecond innerBase innerCloser
          frameCloser first position count ++
        emittedAux outerFirst inner outerSecond innerBase innerCloser
          frameCloser finalBase finalCloser first (position + 1) count ++
        finalCloser

/-- Complete triangular stream beginning at outer position zero. -/
def emitted (outerFirst inner outerSecond : List Recipe)
    (innerBase innerCloser frameCloser finalBase finalCloser : List Token)
    (first count : Nat) : List Token :=
  emittedAux outerFirst inner outerSecond innerBase innerCloser frameCloser
    finalBase finalCloser first 0 count

theorem ofProgram_replicate_instruction
    (instruction : TransitionInstruction) (count : Nat) :
    UnaryProgramTokens.ofProgram (List.replicate count instruction) =
      repeatTokens (UnaryProgramTokens.ofProgram [instruction]) count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, repeatTokens]
      change UnaryProgramTokens.ofProgram
          ([instruction] ++ List.replicate count instruction) =
        UnaryProgramTokens.ofProgram [instruction] ++
          repeatTokens (UnaryProgramTokens.ofProgram [instruction]) count
      rw [UnaryProgramTokenAlgebra.ofProgram_append, induction]

theorem equalityEnding_tokens (count : Nat) :
    UnaryProgramTokens.ofProgram
        (BinarySuccessorSchedule.equalityEnding count) =
      UnaryProgramTokens.ofProgram (TransitionProgram.constant true) ++
        repeatTokens (UnaryProgramTokens.ofProgram [.conjoin]) count := by
  unfold BinarySuccessorSchedule.equalityEnding
  rw [UnaryProgramTokenAlgebra.ofProgram_append,
    ofProgram_replicate_instruction]

/-- The generic triangular contract specializes exactly to the previously
verified clock-successor token recursion. -/
theorem emitted_clockSuccessor
    {tm : Turing.FinTM2}
    [stackFinite : ∀ stack, Fintype (tm.Γ stack)]
    (space clockBits : Nat) :
    emitted
        (BoundedMachineBivariateClockSuccessor.rise (tm := tm)).recipes
        (BoundedMachineBivariateClockSuccessor.equalBit (tm := tm)).recipes
        (BoundedMachineBivariateClockSuccessor.fall (tm := tm)).recipes
        (UnaryProgramTokens.ofProgram (TransitionProgram.constant true))
        (UnaryProgramTokens.ofProgram [.conjoin])
        (UnaryProgramTokens.ofProgram [.conjoin])
        (UnaryProgramTokens.ofProgram (TransitionProgram.constant false))
        (UnaryProgramTokens.ofProgram [.conjoin, .disjoin])
        space clockBits =
      BoundedMachineBivariateClockSuccessor.clockSuccessorTokens
        (tm := tm) space clockBits := by
  unfold emitted BoundedMachineBivariateClockSuccessor.clockSuccessorTokens
  apply aux space 0 clockBits
where
  aux (space position count : Nat) :
      emittedAux
          (BoundedMachineBivariateClockSuccessor.rise (tm := tm)).recipes
          (BoundedMachineBivariateClockSuccessor.equalBit (tm := tm)).recipes
          (BoundedMachineBivariateClockSuccessor.fall (tm := tm)).recipes
          (UnaryProgramTokens.ofProgram (TransitionProgram.constant true))
          (UnaryProgramTokens.ofProgram [.conjoin])
          (UnaryProgramTokens.ofProgram [.conjoin])
          (UnaryProgramTokens.ofProgram (TransitionProgram.constant false))
          (UnaryProgramTokens.ofProgram [.conjoin, .disjoin])
          space position count =
        BoundedMachineBivariateClockSuccessor.tokensAux
          (tm := tm) space position count := by
    induction count generalizing position with
    | zero => rfl
    | succ count induction =>
        rw [emittedAux,
          BoundedMachineBivariateClockSuccessor.tokensAux, induction]
        unfold frameTokens
        unfold BoundedMachineBivariateClockSuccessor.frameTokens
        rw [equalityEnding_tokens]
        simp [List.append_assoc]

end TriangularTemplateEmitter
end PeriodicCNF
end LeanTrominoes
