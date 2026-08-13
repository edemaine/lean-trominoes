/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineProgramStatementPaths

/-!
# Normalized designated accepting-reset program

This file completes the instruction-level normalization of the bounded TM2
relation.  It combines structural well-formedness, the direct symbolic-step
program, reset-clock arithmetic, and tests for the fixed initial and
designated accepting configurations.  The resulting instruction word is
proved exactly equal to the postorder traversal used by the semantic
periodic-CNF reduction.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineProgram

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def designatedMachineAccepts (accepting : tm.Cfg) :
    TransitionProgram.Program :=
  currentConfigIs (tm := tm) (space := space) accepting

def designatedMachineReset (initial accepting : tm.Cfg) :
    TransitionProgram.Program :=
  TransitionProgram.conjoin
    (designatedMachineAccepts (tm := tm) (space := space) accepting)
    (TransitionProgram.conjoin
      (clockReset (tm := tm) (space := space) (clockBits := clockBits))
      (nextConfigIs (tm := tm) (space := space) initial))

def designatedMachineOrdinary (accepting : tm.Cfg) :
    TransitionProgram.Program :=
  TransitionProgram.conjoin
    (TransitionProgram.negate
      (designatedMachineAccepts (tm := tm) (space := space) accepting))
    (TransitionProgram.conjoin
      (clockSuccessor (tm := tm) (space := space) (clockBits := clockBits))
      (machineStep (tm := tm) (space := space)))

/-- Complete instruction word for the bounded designated reset-clock
relation. -/
def designatedMachineResetClock (initial accepting : tm.Cfg) :
    TransitionProgram.Program :=
  TransitionProgram.conjoin
    (wellFormedFields (tm := tm) (space := space))
    (TransitionProgram.disjoin
      (designatedMachineReset (tm := tm) (space := space)
        (clockBits := clockBits) initial accepting)
      (designatedMachineOrdinary (tm := tm) (space := space)
        (clockBits := clockBits) accepting))

@[simp]
theorem program_designatedMachineAccepts (accepting : tm.Cfg) :
    (BoundedMachineAtom.designatedMachineAcceptsExpression (tm := tm)
      (space := space) (clockBits := clockBits) accepting).program =
        designatedMachineAccepts (tm := tm) (space := space) accepting := by
  simp [BoundedMachineAtom.designatedMachineAcceptsExpression,
    designatedMachineAccepts]

@[simp]
theorem program_designatedMachineReset (initial accepting : tm.Cfg) :
    (BoundedMachineAtom.designatedMachineResetExpression (tm := tm)
      (space := space) (clockBits := clockBits) initial accepting).program =
        designatedMachineReset (tm := tm) (space := space)
          (clockBits := clockBits) initial accepting := by
  simp [BoundedMachineAtom.designatedMachineResetExpression,
    designatedMachineReset]

@[simp]
theorem program_designatedMachineOrdinary (accepting : tm.Cfg) :
    (BoundedMachineAtom.designatedMachineOrdinaryExpression (tm := tm)
      (space := space) (clockBits := clockBits) accepting).program =
        designatedMachineOrdinary (tm := tm) (space := space)
          (clockBits := clockBits) accepting := by
  simp [BoundedMachineAtom.designatedMachineOrdinaryExpression,
    designatedMachineOrdinary]

@[simp]
theorem program_designatedMachineResetClock (initial accepting : tm.Cfg) :
    (BoundedMachineAtom.designatedMachineResetClockExpression (tm := tm)
      (space := space) (clockBits := clockBits) initial accepting).program =
        designatedMachineResetClock (tm := tm) (space := space)
          (clockBits := clockBits) initial accepting := by
  simp [BoundedMachineAtom.designatedMachineResetClockExpression,
    designatedMachineResetClock]

end BoundedMachineProgram

end PeriodicCNF
end LeanTrominoes
