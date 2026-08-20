/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokens
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine

/-! # Finite affine tokens for normalized sparse vertex records -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseAffineVertexTokens

open Computability Turing
open Gadget

/-- Finite source alphabet for the two fixed affine vertex coordinates. -/
inductive Token
  | scaledCoordinateUnit
  | horizontalOffset
  | verticalOffset
  | fieldEnd
  | cellType (value : OrthogonalCellType)
  deriving DecidableEq, Fintype, Inhabited

/-- First-stage symbols.  A `scale144Unit` still needs two factor-12
expansions; a `scale12Unit` needs one. -/
inductive IntermediateToken
  | scale144Unit
  | scale12Unit
  | coordinateUnit
  | fieldEnd
  | cellType (value : OrthogonalCellType)
  deriving DecidableEq, Fintype, Inhabited

/-- Second-stage symbols, after all factor-144 units have been expanded. -/
inductive PreparedToken
  | scale12Unit
  | coordinateUnit
  | fieldEnd
  | cellType (value : OrthogonalCellType)
  deriving DecidableEq, Fintype, Inhabited

/-- First factor-12 expansion.  The two offsets use
`471 = 3·144 + 3·12 + 3` and `1257 = 8·144 + 8·12 + 9`. -/
def firstBlock : Token → List IntermediateToken
  | .scaledCoordinateUnit => List.replicate 12 .scale144Unit
  | .horizontalOffset =>
      List.replicate 3 .scale144Unit ++
        List.replicate 3 .scale12Unit ++
          List.replicate 3 .coordinateUnit
  | .verticalOffset =>
      List.replicate 8 .scale144Unit ++
        List.replicate 8 .scale12Unit ++
          List.replicate 9 .coordinateUnit
  | .fieldEnd => [.fieldEnd]
  | .cellType value => [.cellType value]

/-- Second factor-12 expansion. -/
def secondBlock : IntermediateToken → List PreparedToken
  | .scale144Unit => List.replicate 12 .scale12Unit
  | .scale12Unit => [.scale12Unit]
  | .coordinateUnit => [.coordinateUnit]
  | .fieldEnd => [.fieldEnd]
  | .cellType value => [.cellType value]

/-- Final factor-12 expansion into canonical assignment tokens. -/
def thirdBlock : PreparedToken → List GadgetSparseAssignmentTokens.Token
  | .scale12Unit => List.replicate 12 .coordinateUnit
  | .coordinateUnit => [.coordinateUnit]
  | .fieldEnd => [.fieldEnd]
  | .cellType value => [.cellType value]

def firstExpand (tokens : List Token) : List IntermediateToken :=
  tokens.flatMap firstBlock

def secondExpand (tokens : List IntermediateToken) : List PreparedToken :=
  tokens.flatMap secondBlock

def thirdExpand (tokens : List PreparedToken) :
    List GadgetSparseAssignmentTokens.Token :=
  tokens.flatMap thirdBlock

/-- Complete staged expansion. -/
def expand (tokens : List Token) :
    List GadgetSparseAssignmentTokens.Token :=
  thirdExpand (secondExpand (firstExpand tokens))

@[simp] theorem firstExpand_append (first second : List Token) :
    firstExpand (first ++ second) =
      firstExpand first ++ firstExpand second := by
  simp [firstExpand]

@[simp] theorem secondExpand_append
    (first second : List IntermediateToken) :
    secondExpand (first ++ second) =
      secondExpand first ++ secondExpand second := by
  simp [secondExpand]

@[simp] theorem thirdExpand_append (first second : List PreparedToken) :
    thirdExpand (first ++ second) =
      thirdExpand first ++ thirdExpand second := by
  simp [thirdExpand]

@[simp] theorem expand_nil : expand [] = [] := rfl

@[simp] theorem expand_append (first second : List Token) :
    expand (first ++ second) = expand first ++ expand second := by
  simp [expand]

@[simp] theorem secondExpand_replicate_scale144Unit (count : Nat) :
    secondExpand (List.replicate count .scale144Unit) =
      List.replicate (12 * count) .scale12Unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change List.replicate 12 .scale12Unit ++
          secondExpand (List.replicate count .scale144Unit) = _
      rw [induction, ← List.replicate_add]
      congr 1
      omega

@[simp] theorem secondExpand_replicate_scale12Unit (count : Nat) :
    secondExpand (List.replicate count .scale12Unit) =
      List.replicate count .scale12Unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change .scale12Unit ::
          secondExpand (List.replicate count .scale12Unit) = _
      rw [induction]
      rw [List.replicate_succ]

@[simp] theorem secondExpand_replicate_coordinateUnit (count : Nat) :
    secondExpand (List.replicate count .coordinateUnit) =
      List.replicate count .coordinateUnit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change .coordinateUnit ::
          secondExpand (List.replicate count .coordinateUnit) = _
      rw [induction]
      rw [List.replicate_succ]

@[simp] theorem thirdExpand_replicate_scale12Unit (count : Nat) :
    thirdExpand (List.replicate count .scale12Unit) =
      List.replicate (12 * count)
        GadgetSparseAssignmentTokens.Token.coordinateUnit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change List.replicate 12 .coordinateUnit ++
          thirdExpand (List.replicate count .scale12Unit) = _
      rw [induction, ← List.replicate_add]
      congr 1
      omega

@[simp] theorem thirdExpand_replicate_coordinateUnit (count : Nat) :
    thirdExpand (List.replicate count .coordinateUnit) =
      List.replicate count
        GadgetSparseAssignmentTokens.Token.coordinateUnit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change GadgetSparseAssignmentTokens.Token.coordinateUnit ::
          thirdExpand (List.replicate count .coordinateUnit) = _
      rw [induction]
      rw [List.replicate_succ]

@[simp] theorem expand_singleton_scaledCoordinateUnit :
    expand [.scaledCoordinateUnit] =
      List.replicate 1728
        GadgetSparseAssignmentTokens.Token.coordinateUnit := by
  change thirdExpand
      (secondExpand (List.replicate 12 .scale144Unit)) = _
  rw [secondExpand_replicate_scale144Unit,
    thirdExpand_replicate_scale12Unit]

@[simp] theorem expand_singleton_horizontalOffset :
    expand [.horizontalOffset] =
      List.replicate 471
        GadgetSparseAssignmentTokens.Token.coordinateUnit := by
  change thirdExpand (secondExpand
    (List.replicate 3 .scale144Unit ++
      List.replicate 3 .scale12Unit ++
        List.replicate 3 .coordinateUnit)) = _
  rw [secondExpand_append, secondExpand_append,
    secondExpand_replicate_scale144Unit,
    secondExpand_replicate_scale12Unit,
    secondExpand_replicate_coordinateUnit,
    thirdExpand_append, thirdExpand_append,
    thirdExpand_replicate_scale12Unit,
    thirdExpand_replicate_scale12Unit,
    thirdExpand_replicate_coordinateUnit,
    ← List.replicate_add, ← List.replicate_add]

@[simp] theorem expand_singleton_verticalOffset :
    expand [.verticalOffset] =
      List.replicate 1257
        GadgetSparseAssignmentTokens.Token.coordinateUnit := by
  change thirdExpand (secondExpand
    (List.replicate 8 .scale144Unit ++
      List.replicate 8 .scale12Unit ++
        List.replicate 9 .coordinateUnit)) = _
  rw [secondExpand_append, secondExpand_append,
    secondExpand_replicate_scale144Unit,
    secondExpand_replicate_scale12Unit,
    secondExpand_replicate_coordinateUnit,
    thirdExpand_append, thirdExpand_append,
    thirdExpand_replicate_scale12Unit,
    thirdExpand_replicate_scale12Unit,
    thirdExpand_replicate_coordinateUnit,
    ← List.replicate_add, ← List.replicate_add]

@[simp] theorem expand_singleton_fieldEnd :
    expand [.fieldEnd] = [.fieldEnd] := rfl

@[simp] theorem expand_singleton_cellType
    (cellType : OrthogonalCellType) :
    expand [.cellType cellType] = [.cellType cellType] := rfl

theorem expand_cons (token : Token) (tokens : List Token) :
    expand (token :: tokens) = expand [token] ++ expand tokens := by
  change expand ([token] ++ tokens) = _
  rw [expand_append]

@[simp] theorem expand_replicate_scaledCoordinateUnit (count : Nat) :
    expand (List.replicate count .scaledCoordinateUnit) =
      List.replicate (1728 * count)
        GadgetSparseAssignmentTokens.Token.coordinateUnit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, expand_cons,
        expand_singleton_scaledCoordinateUnit, induction,
        ← List.replicate_add]
      congr 1
      omega

@[simp] theorem expand_horizontalFieldEnd :
    expand [.horizontalOffset, .fieldEnd] =
      List.replicate 471
          GadgetSparseAssignmentTokens.Token.coordinateUnit ++
        [.fieldEnd] := by
  change expand ([.horizontalOffset] ++ [.fieldEnd]) = _
  rw [expand_append, expand_singleton_horizontalOffset,
    expand_singleton_fieldEnd]

@[simp] theorem expand_verticalCellType
    (cellType : OrthogonalCellType) :
    expand [.verticalOffset, .cellType cellType] =
      List.replicate 1257
          GadgetSparseAssignmentTokens.Token.coordinateUnit ++
        [.cellType cellType] := by
  change expand ([.verticalOffset] ++ [.cellType cellType]) = _
  rw [expand_append, expand_singleton_verticalOffset,
    expand_singleton_cellType]

/-- One prepared record with horizontal scale index and reflected vertical
complement index. -/
def record (horizontal verticalComplement : Nat)
    (cellType : OrthogonalCellType) : List Token :=
  List.replicate horizontal .scaledCoordinateUnit ++
    [.horizontalOffset, .fieldEnd] ++
    List.replicate verticalComplement .scaledCoordinateUnit ++
    [.verticalOffset, .cellType cellType]

/-- Assignment represented by one prepared affine record. -/
def assignment (horizontal verticalComplement : Nat)
    (cellType : OrthogonalCellType) :
    Cell × OrthogonalCellType :=
  (((1728 * horizontal + 471 : Nat),
      (1728 * verticalComplement + 1257 : Nat)), cellType)

/-- Fixed staged expansion recovers the exact canonical unary assignment
record. -/
@[simp] theorem expand_record
    (horizontal verticalComplement : Nat)
    (cellType : OrthogonalCellType) :
    expand (record horizontal verticalComplement cellType) =
      GadgetSparseAssignmentTokens.assignmentTokens
        (assignment horizontal verticalComplement cellType) := by
  unfold record assignment GadgetSparseAssignmentTokens.assignmentTokens
  rw [expand_append, expand_append, expand_append,
    expand_replicate_scaledCoordinateUnit,
    expand_replicate_scaledCoordinateUnit,
    expand_horizontalFieldEnd, expand_verticalCellType]
  simp only [Int.toNat_natCast]
  rw [List.replicate_add, List.replicate_add]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

noncomputable def firstComputableInPolyTime :
    TM2ComputableInPolyTime id id firstExpand :=
  FiniteBlockTransducer.computableInPolyTime firstBlock

noncomputable def secondComputableInPolyTime :
    TM2ComputableInPolyTime id id secondExpand :=
  FiniteBlockTransducer.computableInPolyTime secondBlock

noncomputable def thirdComputableInPolyTime :
    TM2ComputableInPolyTime id id thirdExpand :=
  FiniteBlockTransducer.computableInPolyTime thirdBlock

/-- Affine vertex-record expansion is a composition of three small fixed
block transductions. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id expand := by
  let firstTwo := TM2CompositionMachine.computableInPolyTime
    firstComputableInPolyTime secondComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime
    firstTwo thirdComputableInPolyTime
  exact complete

end GadgetSparseAffineVertexTokens
end LeanTrominoes
