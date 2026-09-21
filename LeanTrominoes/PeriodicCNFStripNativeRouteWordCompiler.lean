/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompiledRoutedRequestBlockCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteDirectionRequestCompiler
import LeanTrominoes.DelimitedDirectionDisplacementCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendFixedCompiler

/-! # Complete clause-to-variable route words with one delimiter per incidence -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction.NativeRouteWord
open Computability Turing PeriodicOrthocrossing
abbrev Token := HorizontalRoutedRouteHeaderTailBlock.Token
abbrev Request := HorizontalRoutedRouteDirectionRequest.Token
abbrev DirectionToken := DelimitedDirectionDisplacement.Token
local instance : Inhabited DirectionToken := ⟨.routeEnd⟩

def isEnd : Token → Bool
  | .requestEnd => true
  | .request _ => false

def untag : Token → List Request
  | .request token => [token]
  | .requestEnd => []

def body (tokens : List Token) : List AxisDirection :=
  HorizontalRoutedRouteDirectionRequest.polarityOutput
    (HorizontalRoutedRouteDirectionRequest.expanded (tokens.flatMap untag))

def innerOutput (tokens : List Token) : List DirectionToken := DelimitedDirectionDisplacement.word (body tokens)

def output (tokens : List Token) : List DirectionToken := TM2EndDelimitedBlockMap.mappedOutput isEnd innerOutput tokens

noncomputable def innerCompiler : TM2ComputableInPolyTime id id innerOutput := by
  let directions := TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (FiniteBlockTransducer.computableInPolyTime untag)
      HorizontalRoutedRouteDirectionRequest.expandedComputableInPolyTime)
    HorizontalRoutedRouteDirectionRequest.polarityOutputComputableInPolyTime
  let tagged := TM2CompositionMachine.computableInPolyTime directions
    (FiniteBlockTransducer.computableInPolyTime (fun d : AxisDirection => [(.direction d : DirectionToken)]))
  let result := TM2CompositionMachine.computableInPolyTime tagged
    (TM2ListAppend.appendFixedComputableInPolyTime [(.routeEnd : DirectionToken)])
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result (fun tokens => by
    simp only [innerOutput,body,DelimitedDirectionDisplacement.word,TM2ListAppend.appendFixedWords,List.map_eq_flatMap])

noncomputable def compiler : TM2ComputableInPolyTime id id output :=
  TM2EndDelimitedBlockMap.computableInPolyTime innerCompiler isEnd

theorem body_request (header : HorizontalRoutedRouteHeaderTail.Header) (tail : List AxisDirection) :
    body (HorizontalRoutedRouteHeaderTailBlock.requestBlock header tail) =
      (HorizontalRoutedRouteHeader.block header tail).directions RetainedFigureNineRouteDirectionBlock.directions := by
  have erase (ts : List Request) : ((ts.map HorizontalRoutedRouteHeaderTailBlock.Token.request)++[HorizontalRoutedRouteHeaderTailBlock.Token.requestEnd]).flatMap untag=ts := by
    simp [List.flatMap_append,List.flatMap_map,untag]
  rw [body,HorizontalRoutedRouteHeaderTailBlock.requestBlock,erase]
  generalize HorizontalRoutedRouteHeader.block header tail = block
  cases block <;> simp only [HorizontalRoutedRouteDirectionRequest.expanded_tokens,
    HorizontalRoutedRouteDirectionRequest.polarityOutput_operation_directions] <;> rfl

theorem blocksAux_end (reverseBlock body rest : List Token)
    (continues : ∀ token∈body, isEnd token=false) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock (body++HorizontalRoutedRouteHeaderTailBlock.Token.requestEnd::rest) =
      (reverseBlock.reverse++body++[HorizontalRoutedRouteHeaderTailBlock.Token.requestEnd])::TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil => simp [TM2EndDelimitedBlockMap.blocksAux,isEnd]
  | cons token body ih =>
    have current := continues token (by simp)
    have following : ∀ other∈body, isEnd other=false := fun other member => continues other (by simp [member])
    rw [List.cons_append,TM2EndDelimitedBlockMap.blocksAux]
    simp only [current,Bool.false_eq_true,if_false]
    rw [ih (token::reverseBlock) following]
    simp [List.reverse_cons,List.append_assoc]

theorem blocks_requests (pairs : List (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    TM2EndDelimitedBlockMap.blocks isEnd (pairs.flatMap fun p => HorizontalRoutedRouteHeaderTailBlock.requestBlock p.1 p.2) =
      pairs.map (fun p => HorizontalRoutedRouteHeaderTailBlock.requestBlock p.1 p.2) := by
  unfold TM2EndDelimitedBlockMap.blocks
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatMap_cons]
    unfold HorizontalRoutedRouteHeaderTailBlock.requestBlock
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [blocksAux_end _ _ _ (by
      intro token member
      obtain ⟨value,_,rfl⟩ := List.mem_map.mp member
      rfl)]
    simpa [HorizontalRoutedRouteHeaderTailBlock.requestBlock] using congrArg (List.cons (HorizontalRoutedRouteHeaderTailBlock.requestBlock p.1 p.2)) ih

theorem output_requests (pairs : List (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    output (pairs.flatMap fun p => HorizontalRoutedRouteHeaderTailBlock.requestBlock p.1 p.2) =
      DelimitedDirectionDisplacement.words (pairs.map fun p =>
        (HorizontalRoutedRouteHeader.block p.1 p.2).directions RetainedFigureNineRouteDirectionBlock.directions) := by
  simp only [output,TM2EndDelimitedBlockMap.mappedOutput,blocks_requests,List.flatMap_map,innerOutput,body_request,
    DelimitedDirectionDisplacement.words]

end LeanTrominoes.PeriodicCNFStripReduction.NativeRouteWord
end
