/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineVertexTokens
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterSpec

/-! # Indexed affine templates for compact sparse vertex records -/

namespace LeanTrominoes
namespace GadgetSparseAffineIndexedEmitter

open Gadget
open PeriodicCNF
open PeriodicCNF.AffineTemplateEmitterMachine
open PeriodicCNF.UnaryProgramTokens

/-- The five normalized vertex cell types that can occur in the compact
vertex-request stream. -/
inductive VertexCellTag
  | monochromatic (color : WireColor)
  | trichromatic (order : TrichromaticOrder)
  deriving DecidableEq, Fintype

instance : Inhabited VertexCellTag :=
  ⟨.monochromatic .red⟩

def VertexCellTag.cellType : VertexCellTag → OrthogonalCellType
  | .monochromatic color => .monochromaticVertex color
  | .trichromatic order => .trichromaticVertex order

/-- Five distinct fixed unary-program tokens used as finite codes for the
five vertex tags. -/
def VertexCellTag.code : VertexCellTag → Token
  | .monochromatic .red => .constant false
  | .monochromatic .green => .constant true
  | .monochromatic .blue => .negate
  | .trichromatic .blueRedGreen => .conjoin
  | .trichromatic .greenRedBlue => .disjoin

/-- Translate one unary-template token to compact affine vertex tokens.
Unallocated instruction tokens translate to the empty block. -/
def tokenBlock : Token → List GadgetSparseAffineVertexTokens.Token
  | .atomUnit => [.scaledCoordinateUnit]
  | .freshUnit => [.horizontalOffset]
  | .freshEnd => [.fieldEnd]
  | .atomEnd => [.verticalOffset]
  | .constant false => [.cellType (.monochromaticVertex .red)]
  | .constant true => [.cellType (.monochromaticVertex .green)]
  | .negate => [.cellType (.monochromaticVertex .blue)]
  | .conjoin => [.cellType (.trichromaticVertex .blueRedGreen)]
  | .disjoin => [.cellType (.trichromaticVertex .greenRedBlue)]
  | .clauseMarker | .wireStart _ => []

def translateTokens (tokens : List Token) :
    List GadgetSparseAffineVertexTokens.Token :=
  tokens.flatMap tokenBlock

@[simp] theorem translateTokens_nil : translateTokens [] = [] :=
  rfl

@[simp] theorem translateTokens_cons (token : Token) (tokens : List Token) :
    translateTokens (token :: tokens) =
      tokenBlock token ++ translateTokens tokens :=
  rfl

@[simp] theorem translateTokens_append (first second : List Token) :
    translateTokens (first ++ second) =
      translateTokens first ++ translateTokens second := by
  simp [translateTokens]

/-- Recipes for one compact vertex record whose two coordinate fields are
affine in the selected item's zero-based position. -/
def recordRecipes
    (horizontalBase horizontalStride verticalBase verticalStride : Nat)
    (tag : VertexCellTag) : List Recipe :=
  [.atom horizontalBase horizontalStride,
    .fixed .freshUnit,
    .fixed .freshEnd,
    .atom verticalBase verticalStride,
    .fixed .atomEnd,
    .fixed tag.code]

@[simp] theorem tokenBlock_code (tag : VertexCellTag) :
    tokenBlock tag.code = [.cellType tag.cellType] := by
  cases tag with
  | monochromatic color =>
      cases color <;>
        simp [VertexCellTag.code, VertexCellTag.cellType, tokenBlock]
  | trichromatic order =>
      cases order <;>
        simp [VertexCellTag.code, VertexCellTag.cellType, tokenBlock]

@[simp] theorem translateTokens_replicate_atomUnit (count : Nat) :
    translateTokens (List.replicate count .atomUnit) =
      List.replicate count
        GadgetSparseAffineVertexTokens.Token.scaledCoordinateUnit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change tokenBlock .atomUnit ++
          translateTokens (List.replicate count .atomUnit) = _
      rw [induction, List.replicate_succ]
      rfl

/-- Translating an affine record recipe gives exactly the corresponding
compact sparse vertex record. -/
@[simp] theorem translateTokens_positionTokens_recordRecipes
    (horizontalBase horizontalStride verticalBase verticalStride position : Nat)
    (tag : VertexCellTag) :
    translateTokens
        (positionTokens
          (recordRecipes horizontalBase horizontalStride
            verticalBase verticalStride tag)
          position) =
      GadgetSparseAffineVertexTokens.record
        (horizontalBase + horizontalStride * position)
        (verticalBase + verticalStride * position)
        tag.cellType := by
  simp [positionTokens, recordRecipes, Recipe.tokens,
    tokenBlock, GadgetSparseAffineVertexTokens.record]
  exact tokenBlock_code tag

/-- One complete compact record template with both coordinate fields affine
in the selected position. -/
structure RecordTemplate where
  horizontalBase : Nat
  horizontalStride : Nat
  verticalBase : Nat
  verticalStride : Nat
  tag : VertexCellTag
  deriving DecidableEq

namespace RecordTemplate

def recipes (template : RecordTemplate) : List Recipe :=
  recordRecipes template.horizontalBase template.horizontalStride
    template.verticalBase template.verticalStride template.tag

def record (template : RecordTemplate) (position : Nat) :
    List GadgetSparseAffineVertexTokens.Token :=
  GadgetSparseAffineVertexTokens.record
    (template.horizontalBase + template.horizontalStride * position)
    (template.verticalBase + template.verticalStride * position)
    template.tag.cellType

@[simp] theorem translateTokens_positionTokens
    (template : RecordTemplate) (position : Nat) :
    translateTokens (positionTokens template.recipes position) =
      template.record position := by
  rcases template with
    ⟨horizontalBase, horizontalStride, verticalBase, verticalStride, tag⟩
  exact translateTokens_positionTokens_recordRecipes
    horizontalBase horizontalStride verticalBase verticalStride position tag

end RecordTemplate

def recordTemplatesRecipes (templates : List RecordTemplate) : List Recipe :=
  templates.flatMap RecordTemplate.recipes

@[simp] theorem positionTokens_append (first second : List Recipe)
    (position : Nat) :
    positionTokens (first ++ second) position =
      positionTokens first position ++ positionTokens second position := by
  simp [positionTokens]

@[simp] theorem translateTokens_positionTokens_recordTemplatesRecipes
    (templates : List RecordTemplate) (position : Nat) :
    translateTokens
        (positionTokens (recordTemplatesRecipes templates) position) =
      templates.flatMap fun template => template.record position := by
  induction templates with
  | nil => rfl
  | cons template templates induction =>
      rw [show recordTemplatesRecipes (template :: templates) =
          template.recipes ++ recordTemplatesRecipes templates by
        simp [recordTemplatesRecipes]]
      rw [positionTokens_append, translateTokens_append,
        RecordTemplate.translateTokens_positionTokens, induction]
      rfl

/-- A finite input datum either contributes one finite list of affine compact
record templates or is ignored. -/
abbrev RecordFamily (Data : Type) :=
  Data → Option (List RecordTemplate)

def recipeFamily {Data : Type} (family : RecordFamily Data) :
    IndexedTemplateEmitter.Family Data := fun data =>
  (family data).map recordTemplatesRecipes

/-- Expected compact-record word, beginning at an arbitrary selected
position. -/
def recordsEmittedAux {Data : Type} (family : RecordFamily Data) :
    Nat → List Data → List GadgetSparseAffineVertexTokens.Token
  | _, [] => []
  | position, data :: datas =>
      match family data with
      | none => recordsEmittedAux family position datas
      | some templates =>
          templates.flatMap (fun template => template.record position) ++
            recordsEmittedAux family (position + 1) datas

def recordsEmitted {Data : Type} (family : RecordFamily Data)
    (data : List Data) : List GadgetSparseAffineVertexTokens.Token :=
  recordsEmittedAux family 0 data

theorem translateTokens_indexed_emittedAux
    {Data : Type} (family : RecordFamily Data)
    (position : Nat) (data : List Data) :
    translateTokens
        (IndexedTemplateEmitter.emittedAux
          (recipeFamily family) position data) =
      recordsEmittedAux family position data := by
  induction data generalizing position with
  | nil => rfl
  | cons datum data induction =>
      cases familyEq : family datum with
      | none =>
          simp [IndexedTemplateEmitter.emittedAux, recipeFamily,
            recordsEmittedAux, familyEq, induction]
      | some templates =>
          simp [IndexedTemplateEmitter.emittedAux, recipeFamily,
            recordsEmittedAux, familyEq, translateTokens_append,
            induction]

@[simp] theorem translateTokens_indexed_emitted
    {Data : Type} (family : RecordFamily Data) (data : List Data) :
    translateTokens
        (IndexedTemplateEmitter.emitted (recipeFamily family) data) =
      recordsEmitted family data := by
  exact translateTokens_indexed_emittedAux family 0 data

end GadgetSparseAffineIndexedEmitter
end LeanTrominoes
