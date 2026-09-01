/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteUnaryFieldBlockMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Canonical element degrees for the direct final 3DM source -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- Every variable-local element has degree two.  A fixed-red occurrence
contributes three such elements per color; either ordinary connector
contributes one. -/
def directSourceFinalVariableElementDegreeBlock
    (pair : GroupedVariableFanSlot) : List Nat :=
  match pair.1.kind (groupedVariableFanSiteSlot pair.2) with
  | .fixedRed => [2, 2, 2]
  | .fixedGreen | .fixedBlue => [2]

/-- The clause internal has degree three.  Terminal degree is two plus the
presence of its top, left, or right literal. -/
def directSourceFinalClauseElementDegreeBlock :
    FormulaShapeDirectionOrdering.Token → List Nat
  | .clause (.unary _ _) => [3, 3, 2, 2]
  | .clause (.binary _ _ _ _) => [3, 3, 3, 2]
  | .clause (.ternary _ _ _ _ _ _) => [3, 3, 3, 3]
  | .variable => []

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCanonicalElementDegreeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Variable-element degrees for one color, in canonical variable-major,
slot-major, local-element order. -/
def directSourceFinalVariableElementDegrees
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldBlockMap.values
    directSourceFinalVariableElementDegreeBlock
    (directSourceFinalGroupedVariableFanSlots decider symbols)

/-- Clause-element degrees for one color, with internal/top/left/right minor
order at each final clause. -/
def directSourceFinalClauseElementDegrees
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldBlockMap.values
    directSourceFinalClauseElementDegreeBlock
    (directSourceFinalClauseDescriptors decider symbols)

/-- Complete element-degree column for one color. -/
def directSourceFinalOneColorElementDegrees
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalVariableElementDegrees decider symbols ++
    directSourceFinalClauseElementDegrees decider symbols

/-- Canonical red, green, blue element-degree column.  The three colors have
the same local degree pattern in the planar 3DM construction. -/
def directSourceFinalGreenBlueElementDegrees
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalOneColorElementDegrees decider symbols ++
    directSourceFinalOneColorElementDegrees decider symbols

def directSourceFinalCanonicalElementDegrees
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalOneColorElementDegrees decider symbols ++
    directSourceFinalGreenBlueElementDegrees decider symbols

noncomputable def
    directSourceFinalVariableElementDegreesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalVariableElementDegrees decider) := by
  unfold directSourceFinalVariableElementDegrees
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableFanSlotsComputableInPolyTime decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime
      directSourceFinalVariableElementDegreeBlock)

noncomputable def
    directSourceFinalClauseElementDegreesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseElementDegrees decider) := by
  unfold directSourceFinalClauseElementDegrees
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime
      directSourceFinalClauseElementDegreeBlock)

noncomputable def
    directSourceFinalOneColorElementDegreesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOneColorElementDegrees decider) := by
  unfold directSourceFinalOneColorElementDegrees
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalVariableElementDegreesComputableInPolyTime decider)
    (directSourceFinalClauseElementDegreesComputableInPolyTime decider)

/-- The complete canonical color-major degree column compiles in polynomial
time. -/
noncomputable def
    directSourceFinalGreenBlueElementDegreesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGreenBlueElementDegrees decider) := by
  unfold directSourceFinalGreenBlueElementDegrees
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalOneColorElementDegreesComputableInPolyTime decider)
    (directSourceFinalOneColorElementDegreesComputableInPolyTime decider)

/-- The complete canonical color-major degree column compiles in polynomial
time. -/
noncomputable def
    directSourceFinalCanonicalElementDegreesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalElementDegrees decider) := by
  unfold directSourceFinalCanonicalElementDegrees
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalOneColorElementDegreesComputableInPolyTime decider)
    (directSourceFinalGreenBlueElementDegreesComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
