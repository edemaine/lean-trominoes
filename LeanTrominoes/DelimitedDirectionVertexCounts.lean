/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionDisplacementCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Polynomial-time cumulative direction counts at every route vertex -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing
open UnaryFieldEncoderMachine (unaryField unaryFields)

/-- Route delimiters are retained in their blocks. -/
def isRouteEnd : Token → Bool
  | .direction _ => false
  | .routeEnd => true

private theorem blocksAux_word (reverseBlock : List Token)
    (directions : List AxisDirection) (rest : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isRouteEnd reverseBlock (word directions ++ rest) =
      (reverseBlock.reverse ++ word directions) ::
        TM2EndDelimitedBlockMap.blocksAux isRouteEnd [] rest := by
  induction directions generalizing reverseBlock with
  | nil => simp [word, TM2EndDelimitedBlockMap.blocksAux, isRouteEnd]
  | cons direction directions ih =>
      simpa [word, TM2EndDelimitedBlockMap.blocksAux, isRouteEnd,
        List.reverse_cons, List.append_assoc] using ih (.direction direction :: reverseBlock)

theorem blocks_words (routes : List (List AxisDirection)) :
    TM2EndDelimitedBlockMap.blocks isRouteEnd (words routes) = routes.map word := by
  change TM2EndDelimitedBlockMap.blocksAux isRouteEnd [] (words routes) = _
  induction routes with
  | nil => rfl
  | cons route routes ih =>
      simp only [words, List.flatMap_cons] at ih ⊢
      rw [blocksAux_word]
      simpa using congrArg (List.cons (word route)) ih

theorem mappedOutput_words {Target : Type} (f : List Token → List Target)
    (routes : List (List AxisDirection)) :
    TM2EndDelimitedBlockMap.mappedOutput isRouteEnd f (words routes) =
      routes.flatMap (fun route => f (word route)) := by
  simp only [TM2EndDelimitedBlockMap.mappedOutput, blocks_words, List.flatMap_map]

/-- A zero at the end reserves the final vertex's field. -/
def vertexIncrement (direction : AxisDirection) : Token → Nat
  | .direction next => if next = direction then 1 else 0
  | .routeEnd => 0

def vertexCounts (direction : AxisDirection) (route : List AxisDirection) : List Nat :=
  PrefixSums.starts ((route.map (fun next => if next = direction then 1 else 0)) ++ [0])

@[simp] theorem vertexCounts_length (direction : AxisDirection) (route : List AxisDirection) :
    (vertexCounts direction route).length = route.length + 1 := by
  simp [vertexCounts]

private def blockVertexCounts (direction : AxisDirection) (input : List Token) : List Nat :=
  PrefixSums.starts (input.map (vertexIncrement direction))

private theorem blockVertexCounts_word (direction : AxisDirection) (route : List AxisDirection) :
    blockVertexCounts direction (word route) = vertexCounts direction route := by
  simp [blockVertexCounts, word, vertexIncrement, vertexCounts, List.map_map, Function.comp_def]

private def blockVertexCountsCompiler (direction : AxisDirection) :
    TM2ComputableInPolyTime id id (fun input => unaryFields (blockVertexCounts direction input)) := by
  let scan := FiniteBlockTransducer.computableInPolyTime
    (fun token => unaryField (vertexIncrement direction token))
  have fields : TM2ComputableInPolyTime id unaryFields
      (fun input => input.map (vertexIncrement direction)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq scan
      (fun input => by simp [unaryFields, List.flatMap_map])
  let sums := TM2CompositionMachine.computableInPolyTime fields
    UnaryPrefixSumsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq sums (fun _ => rfl)

/-- Reset the four cumulative counters independently at each route delimiter. -/
def vertexCountsCompiler {Symbol : Type} [Fintype Symbol]
    (routes : List Symbol → List (List AxisDirection)) (direction : AxisDirection)
    (compiler : TM2ComputableInPolyTime id id (fun input => words (routes input))) :
    TM2ComputableInPolyTime id unaryFields
      (fun input => (routes input).flatMap (vertexCounts direction)) := by
  let physical := TM2CompositionMachine.computableInPolyTime compiler
    (TM2EndDelimitedBlockMap.computableInPolyTime (blockVertexCountsCompiler direction) isRouteEnd)
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro input
  rw [mappedOutput_words]
  simp only [blockVertexCounts_word, unaryFields, List.flatMap_assoc, id_eq]

end LeanTrominoes.DelimitedDirectionDisplacement
end
