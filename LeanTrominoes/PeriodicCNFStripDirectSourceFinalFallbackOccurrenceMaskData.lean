/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedRetainedTerminalSlotFilterCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalClauseQueryAssemblyData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGlobalTerminalSlotCompiler
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleSemantics

/-! # Direct-source masks for fallback-family occurrence slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFallbackOccurrenceMaskStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFallbackOccurrenceMaskVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Constant Boolean block with one entry per occurrence represented by a
finite direction-aware clause descriptor. -/
def descriptorOccurrenceMaskBlock
    (active : Bool)
    (descriptor : PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    List Bool :=
  List.replicate
    (retainedFinalCopiedDescriptorArity descriptor) active

def descriptorOccurrenceMask
    (active : Bool)
    (descriptors : List
      PeriodicCNF.FormulaShapeDirectionOrdering.Token) : List Bool :=
  descriptors.flatMap (descriptorOccurrenceMaskBlock active)

@[simp] theorem descriptorOccurrenceMask_length
    (active : Bool)
    (descriptors : List
      PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    (descriptorOccurrenceMask active descriptors).length =
      (descriptors.map retainedFinalCopiedDescriptorArity).sum := by
  unfold descriptorOccurrenceMask
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors induction =>
      simp [descriptorOccurrenceMaskBlock, induction]

def directSourceFinalRoutedOccurrenceMaskSuffix
    (symbols : List encoding.Γ) : List Bool :=
  descriptorOccurrenceMask false
      (retainedFinalCopiedClauseDescriptors
        (directRetainedFinalRoutedClauseQueries decider symbols)) ++
    descriptorOccurrenceMask false
      (retainedFinalCopiedClauseDescriptors
        (directRetainedFinalRoutedVariableClauseQueries decider symbols))

def directSourceFinalBendOccurrenceMaskSuffix
    (bendActive : Bool)
    (symbols : List encoding.Γ) : List Bool :=
  descriptorOccurrenceMask bendActive
      (directRetainedPlanarMetadataBaseBendClauseDescriptors
        decider symbols) ++
    directSourceFinalRoutedOccurrenceMaskSuffix decider symbols

def directSourceFinalCarrierOccurrenceMaskSuffix
    (carrierActive bendActive : Bool)
    (symbols : List encoding.Γ) : List Bool :=
  descriptorOccurrenceMask carrierActive
      (directRetainedPlanarMetadataCarrierClauseDescriptors
        decider symbols) ++
    directSourceFinalBendOccurrenceMaskSuffix
      decider bendActive symbols

/-- One occurrence control per final copied incidence, with independently
chosen values on the carrier and bend families. -/
def directSourceFinalFallbackOccurrenceMask
    (carrierActive bendActive : Bool)
    (symbols : List encoding.Γ) : List Bool :=
  descriptorOccurrenceMask false
      (retainedFinalCopiedClauseDescriptors
        (directRetainedFinalCrossoverClauseQueries decider symbols)) ++
    directSourceFinalCarrierOccurrenceMaskSuffix
      decider carrierActive bendActive symbols

def directSourceFinalCarrierOccurrenceMask
    (symbols : List encoding.Γ) : List Bool :=
  directSourceFinalFallbackOccurrenceMask decider true false symbols

def directSourceFinalBendOccurrenceMask
    (symbols : List encoding.Γ) : List Bool :=
  directSourceFinalFallbackOccurrenceMask decider false true symbols

def directSourceFinalGlobalTerminalSlots
    (symbols : List encoding.Γ) : List RetainedTerminalSlot :=
  BoundedRetainedTerminalSlots.slots
    (retainedOccurrenceGlobalStableTerminalRanks
      (retainedFinalCoordinatedScaledSource
        (directSourceFormula decider symbols)).erase
      (retainedFinalCoordinatedScaledSourceRoutes
        (directSourceFormula decider symbols)))

def directSourceFinalCarrierOccurrenceSlots
    (symbols : List encoding.Γ) : List RetainedTerminalSlot :=
  AlignedRetainedTerminalSlotFilter.selected
    (directSourceFinalCarrierOccurrenceMask decider symbols)
    (directSourceFinalGlobalTerminalSlots decider symbols)

def directSourceFinalBendOccurrenceSlots
    (symbols : List encoding.Γ) : List RetainedTerminalSlot :=
  AlignedRetainedTerminalSlotFilter.selected
    (directSourceFinalBendOccurrenceMask decider symbols)
    (directSourceFinalGlobalTerminalSlots decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
