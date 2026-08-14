/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineProgramTemplates

/-!
# Algebra of unary postorder-program token streams

This file records the append and finite-fold identities needed to assemble a
large normalized program from independently emitted phases.  It also rewrites
the affine emitter's recursive position range as the flat map of its exact
per-position program tokens.
-/

namespace LeanTrominoes
namespace PeriodicCNF
namespace UnaryProgramTokenAlgebra

open UnaryProgramTokens
open AffineTemplateEmitterMachine
open AffineProgramTemplates

@[simp]
theorem ofProgram_append (first second : TransitionProgram.Program) :
    ofProgram (first ++ second) = ofProgram first ++ ofProgram second := by
  simp [ofProgram]

@[simp]
theorem ofProgram_constant (value : Bool) :
    ofProgram (TransitionProgram.constant value) =
      instructionTokens (.constant value) :=
  rfl

@[simp]
theorem ofProgram_negate (input : TransitionProgram.Program) :
    ofProgram (TransitionProgram.negate input) =
      ofProgram input ++ instructionTokens .negate := by
  simp [TransitionProgram.negate, ofProgram]

@[simp]
theorem ofProgram_conjoin (first second : TransitionProgram.Program) :
    ofProgram (TransitionProgram.conjoin first second) =
      ofProgram first ++ ofProgram second ++ instructionTokens .conjoin := by
  simp [TransitionProgram.conjoin, ofProgram]

@[simp]
theorem ofProgram_disjoin (first second : TransitionProgram.Program) :
    ofProgram (TransitionProgram.disjoin first second) =
      ofProgram first ++ ofProgram second ++ instructionTokens .disjoin := by
  simp [TransitionProgram.disjoin, ofProgram]

/-- Tokens closing a right-associated finite Boolean fold after its operands
have already been emitted. -/
def foldEnding (emptyValue : Bool) (operator : TransitionInstruction) :
    Nat → List UnaryProgramTokens.Token
  | 0 => instructionTokens (.constant emptyValue)
  | count + 1 => foldEnding emptyValue operator count ++
      instructionTokens operator

def allEnding : Nat → List UnaryProgramTokens.Token :=
  foldEnding true .conjoin

def anyEnding : Nat → List UnaryProgramTokens.Token :=
  foldEnding false .disjoin

@[simp]
theorem ofProgram_all (programs : List TransitionProgram.Program) :
    ofProgram (TransitionProgram.all programs) =
      programs.flatMap ofProgram ++ allEnding programs.length := by
  induction programs with
  | nil => rfl
  | cons program programs induction =>
      rw [TransitionProgram.all, ofProgram_conjoin, induction]
      simp [allEnding, foldEnding, List.append_assoc]

@[simp]
theorem ofProgram_any (programs : List TransitionProgram.Program) :
    ofProgram (TransitionProgram.any programs) =
      programs.flatMap ofProgram ++ anyEnding programs.length := by
  induction programs with
  | nil => rfl
  | cons program programs induction =>
      rw [TransitionProgram.any, ofProgram_disjoin, induction]
      simp [anyEnding, foldEnding, List.append_assoc]

/-- Consecutive natural positions, written recursively in the same direction
as `positionRangeTokens`. -/
def positions (firstPosition : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 => firstPosition :: positions (firstPosition + 1) count

@[simp]
theorem positions_zero (firstPosition : Nat) :
    positions firstPosition 0 = [] :=
  rfl

@[simp]
theorem positions_succ (firstPosition count : Nat) :
    positions firstPosition (count + 1) =
      firstPosition :: positions (firstPosition + 1) count :=
  rfl

theorem positionRangeTokens_eq_flatMap (recipes : List Recipe)
    (firstPosition count : Nat) :
    positionRangeTokens recipes firstPosition count =
      (positions firstPosition count).flatMap
        (positionTokens recipes) := by
  induction count generalizing firstPosition with
  | zero => rfl
  | succ count induction =>
      rw [positionRangeTokens_succ, positions_succ, List.flatMap_cons,
        induction]

theorem positionRangeTokens_program (program : AffineProgramTemplates.Program)
    (firstPosition count : Nat) :
    positionRangeTokens program.recipes firstPosition count =
      (positions firstPosition count).flatMap fun position =>
        ofProgram (program.evaluate position) := by
  rw [positionRangeTokens_eq_flatMap]
  apply List.flatMap_congr
  intro position _
  exact AffineProgramTemplates.Program.positionTokens_recipes program position

end UnaryProgramTokenAlgebra
end PeriodicCNF
end LeanTrominoes
