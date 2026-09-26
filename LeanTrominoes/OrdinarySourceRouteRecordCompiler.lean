/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOrdinarySourceRouteGeometry
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupGetD
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderTailData
import LeanTrominoes.TM2ComputableInPolyTimeCongr

/-! # Native selection and decoding of ordinary source route records -/
noncomputable section
namespace LeanTrominoes.OrdinarySourceRouteRecord
open Turing PeriodicCNF.OrdinarySourceProjection PeriodicCNFStripReduction
abbrev RecordToken := HorizontalRoutedRouteHeaderTail.Token
abbrev BlockToken := FiniteAlphabetDelimitedBlockJoin.Token RecordToken
abbrev Pair := HorizontalRoutedRouteHeaderTail.Header × List AxisDirection

def body (pair : Pair) : List RecordToken := .header pair.1 :: pair.2.map .tailDirection

def markEnd : RecordToken → BlockToken
  | .recordEnd => .blockEnd
  | token => .value token

def decode : BlockToken → List DelimitedDirectionDisplacement.Token
  | .blockEnd => [.routeEnd]
  | .value (.header header) => [.direction (sourceFirstDirection header)]
  | .value (.tailDirection direction) => [.direction direction]
  | .value .recordEnd => []

def directions (pair : Pair) : List AxisDirection := sourceFirstDirection pair.1 :: pair.2

theorem markEnd_record (pair : Pair) :
    (HorizontalRoutedRouteHeaderTail.record pair.1 pair.2).map markEnd =
      FiniteAlphabetDelimitedBlockJoin.block (body pair) := by
  simp only [HorizontalRoutedRouteHeaderTail.record, List.map_cons, List.map_append, List.map_map,
    List.map_nil, markEnd, FiniteAlphabetDelimitedBlockJoin.block, body]
  rfl

theorem markEnd_records (pairs : List Pair) :
    (HorizontalRoutedRouteHeaderTail.records pairs).map markEnd =
      FiniteAlphabetDelimitedBlockJoin.blocks (pairs.map body) := by
  simp only [HorizontalRoutedRouteHeaderTail.records, List.map_flatMap,
    FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_map]
  exact List.flatMap_congr (fun pair _ => markEnd_record pair)

theorem decode_block (pair : Pair) :
    (FiniteAlphabetDelimitedBlockJoin.block (body pair)).flatMap decode =
      DelimitedDirectionDisplacement.word (directions pair) := by
  simp only [FiniteAlphabetDelimitedBlockJoin.block, body, List.map_cons, List.map_map,
    List.flatMap_append, List.flatMap_cons, List.flatMap_map, List.flatMap_nil, List.append_nil,
    decode, DelimitedDirectionDisplacement.word, directions, List.cons_append]
  rw [List.map_eq_flatMap]
  rfl

theorem decode_blocks (pairs : List Pair) :
    (FiniteAlphabetDelimitedBlockJoin.blocks (pairs.map body)).flatMap decode =
      DelimitedDirectionDisplacement.words (pairs.map directions) := by
  simp only [FiniteAlphabetDelimitedBlockJoin.blocks, List.flatMap_map, List.flatMap_assoc,
    DelimitedDirectionDisplacement.words]
  exact List.flatMap_congr (fun pair _ => decode_block pair)

theorem select_decode (indices : List Nat) (pairs : List Pair)
    (valid : ∀ i ∈ indices, i < pairs.length) :
    (FiniteAlphabetIndexedDelimitedBlockLookup.selected indices
      ((HorizontalRoutedRouteHeaderTail.records pairs).map markEnd)).flatMap decode =
      DelimitedDirectionDisplacement.words ((indices.map (fun i => pairs.getD i default)).map directions) := by
  rw [markEnd_records, FiniteAlphabetIndexedDelimitedBlockLookup.selected_blocks_getD _ _
    (fun i hi => by simpa only [List.length_map] using valid i hi)]
  have bodies : indices.map (fun i => (pairs.map body).getD i []) =
      (indices.map (fun i => pairs.getD i default)).map body := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_def]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using valid i hi),
      List.getD_eq_getElem _ _ (valid i hi), List.getElem_map]
  rw [bodies, decode_blocks]

def compiler {Source Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (encodeSource : Source → List Symbol) (indices : Source → List Nat) (pairs : Source → List Pair)
    (indexCompiler : TM2ComputableInPolyTime encodeSource UnaryFieldEncoderMachine.unaryFields indices)
    (recordCompiler : TM2ComputableInPolyTime encodeSource id
      (fun s => HorizontalRoutedRouteHeaderTail.records (pairs s)))
    (valid : ∀ s i, i ∈ indices s → i < (pairs s).length) :
    TM2ComputableInPolyTime encodeSource id (fun s =>
      DelimitedDirectionDisplacement.words (((indices s).map (fun i => (pairs s).getD i default)).map directions)) := by
  let tokens := TM2CompositionMachine.computableInPolyTime recordCompiler
    (FiniteBlockTransducer.computableInPolyTime (fun token => [markEnd token]))
  have tokensCompiler : TM2ComputableInPolyTime encodeSource id
      (fun s => (HorizontalRoutedRouteHeaderTail.records (pairs s)).map markEnd) :=
    TM2ComputableInPolyTime.of_eq tokens (fun s => by rw [List.map_eq_flatMap])
  let selected := FiniteAlphabetIndexedDelimitedBlockLookup.selectedComputableInPolyTimeOf encodeSource
    indices _ indexCompiler tokensCompiler
  let physical := TM2CompositionMachine.computableInPolyTime selected (FiniteBlockTransducer.computableInPolyTime decode)
  exact TM2ComputableInPolyTime.of_eq physical (fun s => select_decode (indices s) (pairs s) (valid s))

end LeanTrominoes.OrdinarySourceRouteRecord
end
