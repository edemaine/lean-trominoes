/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedScopedAtomWordData
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Source positions of copied-clause final occurrences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderCopiedSourcePosition

open Computability Turing
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open HorizontalRoutedRouteHeader

/-- The bounded amount by which the compact presentation stream advances
after one copied clause. -/
abbrev SourceAdvance := Fin 4

def SourceAdvance.zero : SourceAdvance := ⟨0, by decide⟩
def SourceAdvance.one : SourceAdvance := ⟨1, by decide⟩
def SourceAdvance.two : SourceAdvance := ⟨2, by decide⟩
def SourceAdvance.three : SourceAdvance := ⟨3, by decide⟩

def SourceAdvance.toNat : SourceAdvance → Nat
  | advance => advance.val

def profileAdvance : DirectedClauseProfile → SourceAdvance
  | .unary _ _ => .one
  | .binary _ _ _ _ => .two
  | .ternary _ _ _ _ _ _ => .three

@[simp] theorem profileAdvance_toNat (profile : DirectedClauseProfile) :
    (profileAdvance profile).toNat =
      HorizontalRoutedRouteHeaderCopiedScopedAtomWords.sourceWordCount
        profile := by
  cases profile <;>
    rfl

/-- A block-ending source advance.  Its prefix sums are constant throughout
the block and move to the next clause immediately afterward. -/
def endingAdvances : Nat → SourceAdvance → List SourceAdvance
  | 0, _ => []
  | count + 1, advance =>
      List.replicate count .zero ++ [advance]

def tokenAdvances : Token → List SourceAdvance
  | .variable => []
  | .clause profile =>
      endingAdvances
        (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
          (.clause profile)).length
        (profileAdvance profile)

def advances (source : List Token) : List SourceAdvance :=
  source.flatMap tokenAdvances

def increments (source : List Token) : List Nat :=
  FiniteUnaryFieldMap.values SourceAdvance.toNat (advances source)

/-- Starting position in the compact presentation stream, repeated at every
final occurrence of the copied parent clause. -/
def sourceStarts (source : List Token) : List Nat :=
  PrefixSums.starts (increments source)

/-- Presentation-relative source slot.  The value at a parent-local
occurrence is harmless because the later scope selection ignores it. -/
def scopeOffset : AtomScopeControl → Nat
  | .inherited sourceSlot => sourceSlotNat sourceSlot
  | .parentLocal _ => 0

def scopeOffsets (source : List Token) : List Nat :=
  FiniteUnaryFieldMap.values scopeOffset
    (HorizontalRoutedRouteHeaderPresentationAtomScope.output source)

/-- Zero-based compact-source query position of every inherited final
occurrence.  Values at parent-local positions are intentionally irrelevant. -/
def positions (source : List Token) : List Nat :=
  AlignedUnaryListClosure.added
    (sourceStarts source) (scopeOffsets source)

@[simp] theorem endingAdvances_length (count : Nat)
    (advance : SourceAdvance) :
    (endingAdvances count advance).length = count := by
  cases count <;>
    simp [endingAdvances]

@[simp] theorem tokenAdvances_length (token : Token) :
    (tokenAdvances token).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock token).length := by
  cases token <;>
    simp [tokenAdvances]

theorem advances_length (source : List Token) :
    (advances source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  simp [advances, HorizontalRoutedRouteHeaderOccurrenceBlock.output]

theorem increments_length (source : List Token) :
    (increments source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  unfold increments FiniteUnaryFieldMap.values
  rw [List.length_map, advances_length]

theorem sourceStarts_length (source : List Token) :
    (sourceStarts source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  simp [sourceStarts, increments_length]

theorem scopeOffsets_length (source : List Token) :
    (scopeOffsets source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  unfold scopeOffsets FiniteUnaryFieldMap.values
  rw [List.length_map,
    HorizontalRoutedRouteHeaderPresentationAtomScope.output_length]

/-- There is exactly one source-position query per copied final occurrence. -/
theorem positions_length (source : List Token) :
    (positions source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  rw [positions, AlignedUnaryListClosure.added_length,
    sourceStarts_length, scopeOffsets_length, min_self]

noncomputable def advancesComputableInPolyTime :
    TM2ComputableInPolyTime id id advances :=
  FiniteBlockTransducer.computableInPolyTime tokenAdvances

noncomputable def incrementsComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields increments := by
  unfold increments
  exact TM2CompositionMachine.computableInPolyTime
    advancesComputableInPolyTime
    (FiniteUnaryFieldMap.computableInPolyTime SourceAdvance.toNat)

noncomputable def sourceStartsComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields sourceStarts := by
  unfold sourceStarts
  exact TM2CompositionMachine.computableInPolyTime
    incrementsComputableInPolyTime
    UnaryPrefixSumsMachine.computableInPolyTime

noncomputable def scopeOffsetsComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields scopeOffsets := by
  unfold scopeOffsets
  exact TM2CompositionMachine.computableInPolyTime
    HorizontalRoutedRouteHeaderPresentationAtomScope.computableInPolyTime
    (FiniteUnaryFieldMap.computableInPolyTime scopeOffset)

/-- The complete compact-source query column is polynomial-time computable
as unary fields. -/
noncomputable def positionsComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields positions := by
  exact AlignedUnaryListClosure.addedComputableInPolyTime
    id sourceStarts scopeOffsets
    (fun source => (sourceStarts_length source).trans
      (scopeOffsets_length source).symm)
    sourceStartsComputableInPolyTime scopeOffsetsComputableInPolyTime

end HorizontalRoutedRouteHeaderCopiedSourcePosition
end PeriodicCNFStripReduction
end LeanTrominoes

end
