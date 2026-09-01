/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderAtomScopeData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceBlockCompiler

/-! # Presentation-relative atom scopes for copied clauses -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderPresentationAtomScope

open Computability Turing
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader

abbrev TaggedLiteral :=
  (PeriodicCNF.UnaryProgramClauseProfile.LiteralProfile × AxisDirection) ×
    SourceLiteralSlot

/-- Presentation-ordered literals tagged by their original source slot. -/
def presentationTaggedLiterals : DirectedClauseProfile → List TaggedLiteral
  | .unary first firstDirection =>
      [((first, firstDirection), .first)]
  | .binary first firstDirection second secondDirection =>
      [((first, firstDirection), .first),
        ((second, secondDirection), .second)]
  | .ternary first firstDirection second secondDirection
      third thirdDirection =>
      [((first, firstDirection), .first),
        ((second, secondDirection), .second),
        ((third, thirdDirection), .third)]

def taggedDirectionLE (first second : TaggedLiteral) : Prop :=
  directionLE first.1 second.1

instance : DecidableRel taggedDirectionLE := by
  intro first second
  unfold taggedDirectionLE
  infer_instance

/-- The stable clockwise ordering, retaining each literal's presentation
slot as a payload. -/
def orderedTaggedLiterals (profile : DirectedClauseProfile) :
    List TaggedLiteral :=
  (presentationTaggedLiterals profile).insertionSort taggedDirectionLE

/-- For each clockwise source slot, its original presentation slot. -/
def orderedPresentationSlots (profile : DirectedClauseProfile) :
    List SourceLiteralSlot :=
  (orderedTaggedLiterals profile).map Prod.snd

/-- Total lookup from a clockwise slot used by Figure 9 back to the
presentation slot of the pre-Figure9 copied clause. -/
def presentationSlotAt (profile : DirectedClauseProfile)
    (orderedSlot : SourceLiteralSlot) : SourceLiteralSlot :=
  (orderedPresentationSlots profile).getD
    (sourceSlotNat orderedSlot) .first

@[simp] theorem presentationTaggedLiterals_map_fst
    (profile : DirectedClauseProfile) :
    (presentationTaggedLiterals profile).map Prod.fst =
      profile.taggedLiterals := by
  cases profile <;> rfl

/-- Payload tagging does not change the stable clockwise literal order. -/
theorem orderedTaggedLiterals_map_fst
    (profile : DirectedClauseProfile) :
    (orderedTaggedLiterals profile).map Prod.fst =
      profile.taggedLiterals.insertionSort directionLE := by
  have mappedSort := List.map_insertionSort
    (r := taggedDirectionLE) (s := directionLE)
    Prod.fst (presentationTaggedLiterals profile) (by
      intro first _ second _
      rfl)
  unfold orderedTaggedLiterals
  rw [mappedSort, presentationTaggedLiterals_map_fst]

@[simp] theorem orderedPresentationSlots_length
    (profile : DirectedClauseProfile) :
    (orderedPresentationSlots profile).length =
      profile.taggedLiterals.length := by
  unfold orderedPresentationSlots orderedTaggedLiterals
  rw [List.length_map, List.length_insertionSort,
    ← List.length_map, presentationTaggedLiterals_map_fst]

/-- Replace a clockwise inherited slot by its presentation-relative source
slot; parent-local controls are unchanged. -/
def remapScopeControl (profile : DirectedClauseProfile) :
    HorizontalRoutedRouteHeader.AtomScopeControl →
      HorizontalRoutedRouteHeader.AtomScopeControl
  | .inherited orderedSlot =>
      .inherited (presentationSlotAt profile orderedSlot)
  | .parentLocal control => .parentLocal control

/-- Presentation-relative scope controls of every final occurrence generated
from one copied source clause. -/
def clauseBlock (profile : DirectedClauseProfile) :
    List HorizontalRoutedRouteHeader.AtomScopeControl :=
  (sourceClauseHeaders profile).map fun header =>
    remapScopeControl profile
      (HorizontalRoutedRouteHeader.outputAtomScopeControl header)

def tokenBlock : PeriodicCNF.FormulaShapeDirectionOrdering.Token →
    List HorizontalRoutedRouteHeader.AtomScopeControl
  | .clause profile => clauseBlock profile
  | .variable => []

/-- Complete presentation-relative scope stream of a copied descriptor list. -/
def output (source :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    List HorizontalRoutedRouteHeader.AtomScopeControl :=
  source.flatMap tokenBlock

@[simp] theorem clauseBlock_length (profile : DirectedClauseProfile) :
    (clauseBlock profile).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
        (.clause profile)).length := by
  simp [clauseBlock,
    HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock]

/-- The scope stream has exactly one control per expanded final occurrence. -/
theorem output_length (source :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    (output source).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  unfold output HorizontalRoutedRouteHeaderOccurrenceBlock.output
  simp only [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro token _
  cases token <;>
    simp [tokenBlock,
      HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock,
      clauseBlock]

/-- Presentation-relative scope expansion is a fixed finite block
transducer. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

end HorizontalRoutedRouteHeaderPresentationAtomScope
end PeriodicCNFStripReduction
end LeanTrominoes

end
