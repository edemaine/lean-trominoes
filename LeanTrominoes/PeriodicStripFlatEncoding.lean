/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Periodic
import LeanTrominoes.PeriodicCNFFlatEncoding

/-!
# A flat finite encoding of periodic strips

As with periodic CNF, the standard `Primcodable` representation recursively
Cantor-pairs the motif list.  This file instead stores

`[width, period, motif length, x₀, y₀, x₁, y₁, ...]`

as delimiter-terminated binary natural-number fields.  The list overhead is
linear, and the parser's round trip is verified below.
-/

namespace LeanTrominoes

open Computability

namespace PeriodicStripFlatEncoding

abbrev Symbol := PeriodicCNFFlatEncoding.Symbol

/-- The two signed-coordinate fields of one motif cell. -/
def cellFields (cell : Cell) : List Nat :=
  [Encodable.encode cell.1, Encodable.encode cell.2]

/-- Parse one motif cell, leaving all unconsumed fields. -/
def decodeCellFields : List Nat → Option (Cell × List Nat)
  | x :: y :: rest =>
      some ((PeriodicCNFFlatEncoding.decodeIntField x,
        PeriodicCNFFlatEncoding.decodeIntField y), rest)
  | _ => none

@[simp]
theorem decodeCellFields_cellFields_append (cell : Cell) (rest : List Nat) :
    decodeCellFields (cellFields cell ++ rest) = some (cell, rest) := by
  rcases cell with ⟨x, y⟩
  simp [cellFields, decodeCellFields]

/-- Parse exactly `count` motif cells. -/
def decodeCells : Nat → List Nat → Option (List Cell × List Nat)
  | 0, fields => some ([], fields)
  | count + 1, fields => do
      let (cell, rest) ← decodeCellFields fields
      let (cells, suffix) ← decodeCells count rest
      pure (cell :: cells, suffix)

@[simp]
theorem decodeCells_flatMap_cellFields_append
    (cells : List Cell) (rest : List Nat) :
    decodeCells cells.length (cells.flatMap cellFields ++ rest) =
      some (cells, rest) := by
  induction cells with
  | nil => simp [decodeCells]
  | cons cell cells ih =>
      simp [decodeCells, ih]

/-- Flat natural-number fields for a complete periodic-strip presentation. -/
def stripFields (periodicStrip : PeriodicStrip) : List Nat :=
  [periodicStrip.width, periodicStrip.period, periodicStrip.motif.length] ++
    periodicStrip.motif.flatMap cellFields

/-- Decode a complete strip field list, rejecting any unconsumed suffix. -/
def decodeStripFields : List Nat → Option PeriodicStrip
  | width :: period :: motifLength :: fields => do
      let (motif, rest) ← decodeCells motifLength fields
      if rest.isEmpty then some ⟨width, period, motif⟩ else none
  | _ => none

@[simp]
theorem decodeStripFields_stripFields (periodicStrip : PeriodicStrip) :
    decodeStripFields (stripFields periodicStrip) = some periodicStrip := by
  rcases periodicStrip with ⟨width, period, motif⟩
  have parsed : decodeCells motif.length (motif.flatMap cellFields) =
      some (motif, []) := by
    simpa using decodeCells_flatMap_cellFields_append motif []
  simp [stripFields, decodeStripFields, parsed]

/-- Flat finite encoding used by the formal statement of the 1.5D problem. -/
def finEncoding : FinEncoding PeriodicStrip :=
  PeriodicCNFFlatEncoding.finEncodingOfFields stripFields decodeStripFields
    decodeStripFields_stripFields

@[simp]
theorem finEncoding_encode_length (periodicStrip : PeriodicStrip) :
    (finEncoding.encode periodicStrip).length =
      ((stripFields periodicStrip).map fun field =>
        (encodeNat field).length + 1).sum := by
  exact PeriodicCNFFlatEncoding.encodeNatFields_length _

@[simp]
theorem stripFields_length (periodicStrip : PeriodicStrip) :
    (stripFields periodicStrip).length = 3 + 2 * periodicStrip.motif.length := by
  have flat : (periodicStrip.motif.flatMap cellFields).length =
      2 * periodicStrip.motif.length := by
    induction periodicStrip.motif with
    | nil => rfl
    | cons cell cells ih =>
        simp [cellFields, ih]
        omega
  simp [stripFields, flat]
  omega

end PeriodicStripFlatEncoding

end LeanTrominoes
