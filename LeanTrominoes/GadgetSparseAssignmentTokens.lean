/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseExpandedMotifFiniteTokens

/-! # Finite unary records for sparse drawing-cell assignments -/

namespace LeanTrominoes
namespace GadgetSparseAssignmentTokens

open Gadget

/-- Finite source alphabet for unary `(horizontal, vertical, cellType)`
assignment records. -/
inductive Token
  | coordinateUnit
  | fieldEnd
  | cellType (value : OrthogonalCellType)
  deriving DecidableEq, Fintype, Inhabited

inductive Phase
  | horizontal
  | vertical
  deriving DecidableEq

/-- One unary sparse-assignment record. -/
def assignmentTokens (assignment : Cell × OrthogonalCellType) : List Token :=
  List.replicate assignment.1.1.toNat .coordinateUnit ++
    .fieldEnd ::
      List.replicate assignment.1.2.toNat .coordinateUnit ++
        [.cellType assignment.2]

/-- Concatenated unary records for an assignment list. -/
def assignmentsTokens
    (assignments : List (Cell × OrthogonalCellType)) : List Token :=
  assignments.flatMap assignmentTokens

@[simp] theorem assignmentsTokens_append
    (first second : List (Cell × OrthogonalCellType)) :
    assignmentsTokens (first ++ second) =
      assignmentsTokens first ++ assignmentsTokens second := by
  simp [assignmentsTokens]

@[simp] theorem assignmentsTokens_map {Value : Type}
    (values : List Value) (assignment : Value → Cell × OrthogonalCellType) :
    assignmentsTokens (values.map assignment) =
      values.flatMap (fun value => assignmentTokens (assignment value)) := by
  unfold assignmentsTokens
  exact List.flatMap_map assignment assignmentTokens values

@[simp] theorem assignmentsTokens_flatMap {Value : Type}
    (values : List Value)
    (assignments : Value → List (Cell × OrthogonalCellType)) :
    assignmentsTokens (values.flatMap assignments) =
      values.flatMap (fun value => assignmentsTokens (assignments value)) := by
  unfold assignmentsTokens
  exact List.flatMap_assoc

/-- Prepared pixel stream associated with natural block coordinates and one
finite drawing cell type. -/
def preparedNatAssignmentPixels (tromino : Tromino)
    (horizontal vertical : Nat) (cellType : OrthogonalCellType) :
    List GadgetPixelFiniteTokens.Token :=
  (orthogonalCellPixels tromino cellType).flatMap fun pixel =>
    GadgetPixelFiniteTokens.pixelBlock horizontal vertical
      (GadgetExpandedMotifFiniteTokens.boundedPixel pixel)

/-- Total parser and expander for arbitrary unary assignment-token words. -/
def expandAux (tromino : Tromino) :
    Phase → Nat → Nat → List Token → List GadgetPixelFiniteTokens.Token
  | _, _, _, [] => []
  | .horizontal, horizontal, _, .coordinateUnit :: tokens =>
      expandAux tromino .horizontal (horizontal + 1) 0 tokens
  | .horizontal, horizontal, _, .fieldEnd :: tokens =>
      expandAux tromino .vertical horizontal 0 tokens
  | .horizontal, _, _, .cellType _ :: tokens =>
      expandAux tromino .horizontal 0 0 tokens
  | .vertical, horizontal, vertical, .coordinateUnit :: tokens =>
      expandAux tromino .vertical horizontal (vertical + 1) tokens
  | .vertical, _, _, .fieldEnd :: tokens =>
      expandAux tromino .horizontal 0 0 tokens
  | .vertical, horizontal, vertical, .cellType cellType :: tokens =>
      preparedNatAssignmentPixels tromino horizontal vertical cellType ++
        expandAux tromino .horizontal 0 0 tokens

/-- Parse a complete word from the start of a horizontal field. -/
def expand (tromino : Tromino) (tokens : List Token) :
    List GadgetPixelFiniteTokens.Token :=
  expandAux tromino .horizontal 0 0 tokens

theorem expandAux_horizontal_replicate (tromino : Tromino)
    (initial count : Nat) (tokens : List Token) :
    expandAux tromino .horizontal initial 0
        (List.replicate count .coordinateUnit ++ tokens) =
      expandAux tromino .horizontal (initial + count) 0 tokens := by
  induction count generalizing initial with
  | zero => simp
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [expandAux]
      rw [induction]
      simp only [Nat.add_assoc]
      congr 2
      omega

theorem expandAux_vertical_replicate (tromino : Tromino)
    (horizontal initial count : Nat) (tokens : List Token) :
    expandAux tromino .vertical horizontal initial
        (List.replicate count .coordinateUnit ++ tokens) =
      expandAux tromino .vertical horizontal (initial + count) tokens := by
  induction count generalizing initial with
  | zero => simp
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [expandAux]
      rw [induction]
      simp only [Nat.add_assoc]
      congr 2
      omega

/-- Parsing one canonical record emits its prepared pixel stream and resumes
at the next horizontal field. -/
theorem expandAux_assignmentTokens_append (tromino : Tromino)
    (assignment : Cell × OrthogonalCellType) (tokens : List Token) :
    expandAux tromino .horizontal 0 0
        (assignmentTokens assignment ++ tokens) =
      preparedNatAssignmentPixels tromino assignment.1.1.toNat
          assignment.1.2.toNat assignment.2 ++
        expandAux tromino .horizontal 0 0 tokens := by
  unfold assignmentTokens
  simp only [List.append_assoc, List.cons_append]
  rw [expandAux_horizontal_replicate]
  simp only [Nat.zero_add, expandAux]
  rw [expandAux_vertical_replicate]
  simp [expandAux]

/-- Canonical assignment records expand to exactly the previously defined
sparse prepared motif. -/
@[simp] theorem expand_assignmentsTokens (tromino : Tromino)
    (assignments : List (Cell × OrthogonalCellType)) :
    expand tromino (assignmentsTokens assignments) =
      GadgetSparseExpandedMotifFiniteTokens.preparedSparseExpandedMotif
        tromino assignments := by
  unfold expand assignmentsTokens
  induction assignments with
  | nil => rfl
  | cons assignment assignments induction =>
      rw [List.flatMap_cons, expandAux_assignmentTokens_append, induction]
      rfl

end GadgetSparseAssignmentTokens
end LeanTrominoes
