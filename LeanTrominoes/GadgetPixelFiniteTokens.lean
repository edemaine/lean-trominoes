/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CountedUnaryFieldTokens
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.GadgetSubstitution
import LeanTrominoes.PeriodicStripFlatEncoding

/-! # Finite affine tokens for gadget-pixel coordinates

Every local gadget pixel lies in a fixed `6 × 6` window.  A block coordinate
therefore has the form `6 * index + local`, and its nonnegative integer code
has the affine form `12 * index + 2 * local`.  This file represents that
arithmetic by a finite input alphabet and verifies a fixed block transducer
which expands the representation to the counted unary-field tokens used by
the strip compiler.
-/

noncomputable section

namespace LeanTrominoes
namespace GadgetPixelFiniteTokens

open Computability Turing
open Gadget
open PeriodicCNF.UnaryProgramTokens

/-- Finite symbols from which affine gadget-pixel fields are assembled. -/
inductive Token
  | headerUnit
  | coordinateUnit
  | localOffset (offset : Fin 6)
  | fieldEnd
  | cellMarker
  deriving DecidableEq, Fintype, Inhabited

/-- Fixed expansion of one affine-coordinate symbol. -/
def block : Token → List PeriodicCNF.UnaryProgramTokens.Token
  | .headerUnit => List.replicate 6 .atomUnit
  | .coordinateUnit => List.replicate 12 .atomUnit
  | .localOffset offset => List.replicate (2 * offset.val) .atomUnit
  | .fieldEnd => [.atomEnd]
  | .cellMarker => [.clauseMarker]

/-- Expand a prepared finite stream into ordinary counted field tokens. -/
def expand (tokens : List Token) :
    List PeriodicCNF.UnaryProgramTokens.Token :=
  tokens.flatMap block

@[simp] theorem expand_nil : expand [] = [] := rfl

@[simp] theorem expand_cons (token : Token) (tokens : List Token) :
    expand (token :: tokens) = block token ++ expand tokens := rfl

@[simp] theorem expand_append (first second : List Token) :
    expand (first ++ second) = expand first ++ expand second := by
  simp [expand]

@[simp] theorem expand_replicate_headerUnit (count : Nat) :
    expand (List.replicate count .headerUnit) =
      List.replicate (6 * count) .atomUnit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, expand_cons, induction]
      simp only [block, List.replicate_add]
      congr 1

@[simp] theorem expand_replicate_coordinateUnit (count : Nat) :
    expand (List.replicate count .coordinateUnit) =
      List.replicate (12 * count) .atomUnit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, expand_cons, induction]
      simp only [block, List.replicate_add]
      congr 1

/-- Prepared unary field for an unsigned header scaled by six. -/
def headerField (number : Nat) : List Token :=
  List.replicate number .headerUnit ++ [.fieldEnd]

/-- Prepared unary field for the code of `6 * index + offset`. -/
def coordinateField (index : Nat) (offset : Fin 6) : List Token :=
  List.replicate index .coordinateUnit ++ [.localOffset offset, .fieldEnd]

@[simp] theorem expand_headerField (number : Nat) :
    expand (headerField number) =
      CountedUnaryFieldTokens.field (6 * number) := by
  unfold headerField CountedUnaryFieldTokens.field
    PeriodicCNF.UnaryProgramTokens.atomTokens
  rw [expand_append, expand_replicate_headerUnit]
  rfl

@[simp] theorem expand_coordinateField (index : Nat) (offset : Fin 6) :
    expand (coordinateField index offset) =
      CountedUnaryFieldTokens.field (12 * index + 2 * offset.val) := by
  unfold coordinateField CountedUnaryFieldTokens.field
    PeriodicCNF.UnaryProgramTokens.atomTokens
  rw [expand_append, expand_replicate_coordinateUnit]
  change List.replicate (12 * index)
        PeriodicCNF.UnaryProgramTokens.Token.atomUnit ++
      (List.replicate (2 * offset.val)
          PeriodicCNF.UnaryProgramTokens.Token.atomUnit ++ [.atomEnd]) =
    List.replicate (12 * index + 2 * offset.val)
        PeriodicCNF.UnaryProgramTokens.Token.atomUnit ++
      [.atomEnd]
  rw [← List.append_assoc, ← List.replicate_add]

/-- Regard a pair of bounded local coordinates as an integer cell. -/
def localCell (pixel : Fin 6 × Fin 6) : Cell :=
  (pixel.1.val, pixel.2.val)

/-- One prepared counted block for a translated gadget pixel. -/
def pixelBlock (horizontal vertical : Nat) (pixel : Fin 6 × Fin 6) :
    List Token :=
  .cellMarker ::
    (coordinateField horizontal pixel.1 ++
      coordinateField vertical pixel.2)

theorem encode_blockCoordinate (index : Nat) (offset : Fin 6) :
    Encodable.encode
        ((6 * (index : Int) + (offset.val : Int)) : Int) =
      12 * index + 2 * offset.val := by
  change Encodable.encode (Int.ofNat (6 * index + offset.val)) = _
  rw [Computability.encode_int_ofNat]
  omega

@[simp] theorem expand_pixelBlock
    (horizontal vertical : Nat) (pixel : Fin 6 × Fin 6) :
    expand (pixelBlock horizontal vertical pixel) =
      CountedUnaryFieldTokens.countedFieldBlock
        (PeriodicStripFlatEncoding.cellFields
          (Cell.add
            (PeriodicOrthogonalDrawing.blockOrigin horizontal vertical)
            (localCell pixel))) := by
  rcases pixel with ⟨x, y⟩
  simp only [pixelBlock, expand_cons, block, expand_append,
    expand_coordinateField, CountedUnaryFieldTokens.countedFieldBlock,
    PeriodicStripFlatEncoding.cellFields, localCell,
    PeriodicOrthogonalDrawing.blockOrigin, Cell.add]
  rw [encode_blockCoordinate horizontal x,
    encode_blockCoordinate vertical y]
  simp [CountedUnaryFieldTokens.fields]

/-- The affine-token expansion is a fixed finite block transduction. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id expand :=
  FiniteBlockTransducer.computableInPolyTime block

end GadgetPixelFiniteTokens
end LeanTrominoes
