/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialSourceEmitter
import LeanTrominoes.PeriodicCNFBivariateProgramTokenAlgebra

/-!
# Bivariate templates for the initial input-stack tail

The input stack's first empty cell begins after the source word.  Its remaining
empty-cell atoms therefore depend affinely on two counters: the number of
source symbols and the zero-based tail-marker position.  This file gives that
fixed two-counter program and identifies its complete emitted range with the
tail schedule exposed by the initial-configuration specification.
-/

noncomputable section

namespace LeanTrominoes

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace PolySpaceInitialTailTemplates

open BivariateProgramTemplates
open BivariateProgramTokenAlgebra
open UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Data := PolySpaceInitialSourceEmitter.Data (encoding := encoding)

/-- Select prepared source symbols for the persistent first counter. -/
def sourceSelected : Data (encoding := encoding) → Bool
  | .inl symbol =>
      PolySpaceInitialTailPadding.isSource (encoding := encoding) symbol
  | .inr _ => false

/-- Select the newly appended unary tail markers for the position counter. -/
def tailSelected : Data (encoding := encoding) → Bool
  | .inl _ => false
  | .inr _ => true

/-- Bivariate code of an empty input-stack cell at
`sourceCount + tailPosition`. -/
def tailAtom : BivariateProgramTemplates.Atom where
  base := Fintype.card (Option decider.tm.Λ) +
    (Fintype.card decider.tm.σ +
      BoundedMachineAtom.stackSymbolCode ⟨decider.tm.k₀, none⟩)
  firstStride := BoundedMachineAtom.stackSymbolCount (tm := decider.tm)
  secondStride := BoundedMachineAtom.stackSymbolCount (tm := decider.tm)

@[simp]
theorem evaluate_tailAtom (sourceCount tailPosition : Nat) :
    (tailAtom decider).evaluate sourceCount tailPosition =
      Fintype.card (Option decider.tm.Λ) +
        (Fintype.card decider.tm.σ +
          (BoundedMachineAtom.stackSymbolCode ⟨decider.tm.k₀, none⟩ +
            BoundedMachineAtom.stackSymbolCount (tm := decider.tm) *
              (sourceCount + tailPosition))) := by
  simp [tailAtom, BivariateProgramTemplates.Atom.evaluate]
  ring

/-- One empty-cell test, parameterized by the two runtime counters. -/
def inputTailProgram : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.next (tailAtom decider)

@[simp]
theorem evaluate_inputTailProgram (sourceCount tailPosition : Nat) :
    (inputTailProgram decider).evaluate sourceCount tailPosition =
      BoundedMachineProgram.nextStackCellIs (tm := decider.tm)
        decider.tm.k₀ (sourceCount + tailPosition) none := by
  simp [inputTailProgram, BoundedMachineProgram.nextStackCellIs]

/-- The recipe range from an arbitrary tail offset is exactly the corresponding
range of empty input-stack cell tests. -/
theorem positionRangeTokens_eq (sourceCount firstPosition count : Nat) :
    BivariateTemplateEmitterMachine.positionRangeTokens
        (inputTailProgram decider).recipes sourceCount firstPosition count =
      (List.range count).flatMap fun offset =>
        ofProgram
          (BoundedMachineProgram.nextStackCellIs (tm := decider.tm)
            decider.tm.k₀ (sourceCount + firstPosition + offset) none) := by
  rw [BivariateProgramTokenAlgebra.positionRangeTokens_program,
    BoundedMachineOneHotEmitter.positions_eq_range_map,
    List.flatMap_map]
  apply List.flatMap_congr
  intro offset _
  rw [evaluate_inputTailProgram]
  have positionEq : sourceCount + (firstPosition + offset) =
      sourceCount + firstPosition + offset := by omega
  rw [positionEq]

/-- Starting the position counter at zero recovers the exact input-stack tail
word from the source-dependent initial-configuration schedule. -/
@[simp]
theorem positionRangeTokens_zero_eq (symbols : List encoding.Γ) :
    BivariateTemplateEmitterMachine.positionRangeTokens
        (inputTailProgram decider).recipes symbols.length 0
        (PolySpaceInitialTailPadding.tailCount decider symbols) =
      PolySpaceInitialEmitter.emptyTailTokens decider decider.tm.k₀
        symbols.length
        (PolySpaceInitialTailPadding.tailCount decider symbols) := by
  rw [positionRangeTokens_eq]
  unfold PolySpaceInitialEmitter.emptyTailTokens
  simp [BoundedMachineFixedConfigurationEmitter.stackCellIs]

end PolySpaceInitialTailTemplates
end PeriodicCNF
end LeanTrominoes
