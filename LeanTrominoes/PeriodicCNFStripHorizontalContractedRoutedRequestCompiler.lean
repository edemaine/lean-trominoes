/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledContractedDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceRoutedRequestCompiler
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerBatchCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Compiler for compact routed contracted-edge requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalContractedRoutedRequest

open Computability Turing
open PeriodicThreeDM

abbrev Role := ContractedDirectionAssembler.Role
abbrev IncidenceToken := HorizontalTypedIncidenceRoutedRequest.Token
abbrev AssemblerToken := ContractedDirectionAssembler.Token
abbrev NormalizedToken :=
  NormalizationDirectionRequest.Batch.NormalizedToken

/-- One explicitly delimited routed incidence, tagged with its role in the
surrounding contracted edge. -/
inductive Token
  | role (value : Role)
  | incidence (token : IncidenceToken)
  | incidenceEnd
  deriving DecidableEq, Fintype

instance : Inhabited Token := ⟨.role .retained⟩

def isEnd : Token → Bool
  | .incidenceEnd => true
  | _ => false

def roleBlock : Token → List AssemblerToken
  | .role role => [.role role]
  | _ => []

def incidenceBlock : Token → List IncidenceToken
  | .incidence token => [token]
  | _ => []

def roleTokens (input : List Token) : List AssemblerToken :=
  input.flatMap roleBlock

def incidenceTokens (input : List Token) : List IncidenceToken :=
  input.flatMap incidenceBlock

def normalizedBlock : NormalizedToken → List AssemblerToken
  | .direction direction => [.direction direction]
  | .routeEnd => [.incidenceEnd]

@[simp] theorem flatMap_normalizedDirections
    (directions : List AxisDirection) :
    (directions.map
        NormalizationDirectionRequest.Batch.NormalizedToken.direction).flatMap
        normalizedBlock =
      directions.map ContractedDirectionAssembler.Token.direction := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [normalizedBlock, induction]

@[simp] theorem flatMap_normalizedRoute
    (directions : List AxisDirection) :
    (directions.map
          NormalizationDirectionRequest.Batch.NormalizedToken.direction ++
        [NormalizationDirectionRequest.Batch.NormalizedToken.routeEnd]).flatMap
        normalizedBlock =
      directions.map ContractedDirectionAssembler.Token.direction ++
        [.incidenceEnd] := by
  simp [normalizedBlock]

def normalizedAssemblerTokens (input : List Token) : List AssemblerToken :=
  (HorizontalTypedIncidenceRoutedRequest.normalizedOutput
    (incidenceTokens input)).flatMap normalizedBlock

def innerOutput (input : List Token) : List AssemblerToken :=
  roleTokens input ++ normalizedAssemblerTokens input

noncomputable def roleTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id roleTokens := by
  change TM2ComputableInPolyTime id id
    (fun input : List Token => input.flatMap roleBlock)
  exact FiniteBlockTransducer.computableInPolyTime roleBlock

noncomputable def incidenceTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id incidenceTokens := by
  change TM2ComputableInPolyTime id id
    (fun input : List Token => input.flatMap incidenceBlock)
  exact FiniteBlockTransducer.computableInPolyTime incidenceBlock

noncomputable def normalizedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id fun input : List Token =>
      HorizontalTypedIncidenceRoutedRequest.normalizedOutput
        (incidenceTokens input) :=
  TM2CompositionMachine.computableInPolyTime
    incidenceTokensComputableInPolyTime
    HorizontalTypedIncidenceRoutedRequest.normalizedOutputComputableInPolyTime

noncomputable def normalizedAssemblerTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizedAssemblerTokens := by
  let converted : TM2ComputableInPolyTime id id
      (fun tokens : List NormalizedToken => tokens.flatMap normalizedBlock) :=
    FiniteBlockTransducer.computableInPolyTime normalizedBlock
  let complete := TM2CompositionMachine.computableInPolyTime
    normalizedTokensComputableInPolyTime converted
  change TM2ComputableInPolyTime id id
    (fun input =>
      (HorizontalTypedIncidenceRoutedRequest.normalizedOutput
        (incidenceTokens input)).flatMap normalizedBlock)
  exact complete

noncomputable def innerOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id innerOutput := by
  change TM2ComputableInPolyTime id id
    (fun input => roleTokens input ++ normalizedAssemblerTokens input)
  exact TM2ListAppend.computableInPolyTime
    roleTokensComputableInPolyTime
    normalizedAssemblerTokensComputableInPolyTime

/-- Canonical compact routed request for one classified incidence role. -/
def requestBlock (role : Role)
    (block : HorizontalTypedIncidenceDirectionBlock) : List Token :=
  [.role role] ++
    (HorizontalTypedIncidenceRoutedRequest.blockTokens block).map
      .incidence ++
    [.incidenceEnd]

@[simp] theorem roleTokens_requestBlock
    (role : Role) (block : HorizontalTypedIncidenceDirectionBlock) :
    roleTokens (requestBlock role block) = [.role role] := by
  simp [roleTokens, requestBlock, roleBlock, List.flatMap_map]

@[simp] theorem incidenceTokens_requestBlock
    (role : Role) (block : HorizontalTypedIncidenceDirectionBlock) :
    incidenceTokens (requestBlock role block) =
      HorizontalTypedIncidenceRoutedRequest.blockTokens block := by
  simp [incidenceTokens, requestBlock, incidenceBlock, List.flatMap_map]

@[simp] theorem innerOutput_requestBlock
    (role : Role) (block : HorizontalTypedIncidenceDirectionBlock) :
    innerOutput (requestBlock role block) =
      ContractedDirectionAssembler.roleBlock role block.directions := by
  unfold innerOutput normalizedAssemblerTokens
  rw [roleTokens_requestBlock, incidenceTokens_requestBlock,
    HorizontalTypedIncidenceRoutedRequest.normalizedOutput_blockTokens]
  simp [normalizedBlock, ContractedDirectionAssembler.roleBlock]

/-- A tagged semantic incidence block used by canonical batch inputs. -/
structure TaggedBlock where
  role : Role
  incidence : HorizontalTypedIncidenceDirectionBlock

def TaggedBlock.tokens (block : TaggedBlock) : List Token :=
  requestBlock block.role block.incidence

def TaggedBlock.output (block : TaggedBlock) : List AssemblerToken :=
  ContractedDirectionAssembler.roleBlock
    block.role block.incidence.directions

def inputTokens (blocks : List TaggedBlock) : List Token :=
  blocks.flatMap TaggedBlock.tokens

def outputTokens (blocks : List TaggedBlock) : List AssemblerToken :=
  blocks.flatMap TaggedBlock.output

private theorem requestBlock_continues
    (role : Role) (block : HorizontalTypedIncidenceDirectionBlock) :
    ∀ token ∈
        ([Token.role role] ++
          (HorizontalTypedIncidenceRoutedRequest.blockTokens block).map
            Token.incidence),
      isEnd token = false := by
  intro token member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with rfl | member
  · rfl
  · obtain ⟨inner, _, rfl⟩ := List.mem_map.mp member
    rfl

private theorem blocksAux_append_incidenceEnd
    (reverseBlock body rest : List Token)
    (continues : ∀ token ∈ body, isEnd token = false) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (body ++ .incidenceEnd :: rest) =
      (reverseBlock.reverse ++ body ++ [.incidenceEnd]) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil => simp [TM2EndDelimitedBlockMap.blocksAux, isEnd]
  | cons token body induction =>
      have tokenContinues := continues token (by simp)
      have bodyContinues : ∀ other ∈ body, isEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, TM2EndDelimitedBlockMap.blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

private theorem blocksAux_requestBlock_append
    (reverseBlock : List Token) (role : Role)
    (block : HorizontalTypedIncidenceDirectionBlock)
    (rest : List Token) :
    TM2EndDelimitedBlockMap.blocksAux isEnd reverseBlock
        (requestBlock role block ++ rest) =
      (reverseBlock.reverse ++ requestBlock role block) ::
        TM2EndDelimitedBlockMap.blocksAux isEnd [] rest := by
  unfold requestBlock
  rw [List.append_assoc]
  simpa [List.append_assoc] using blocksAux_append_incidenceEnd
    reverseBlock
    ([Token.role role] ++
      (HorizontalTypedIncidenceRoutedRequest.blockTokens block).map
        Token.incidence)
    rest (requestBlock_continues role block)

@[simp] theorem blocks_inputTokens (blocks : List TaggedBlock) :
    TM2EndDelimitedBlockMap.blocks isEnd (inputTokens blocks) =
      blocks.map TaggedBlock.tokens := by
  unfold TM2EndDelimitedBlockMap.blocks inputTokens
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      rw [List.flatMap_cons]
      rw [show TaggedBlock.tokens block =
        requestBlock block.role block.incidence by rfl]
      rw [blocksAux_requestBlock_append]
      simp only [List.reverse_nil, List.nil_append, List.map_cons]
      rw [induction]
      rfl

/-- Reset the routed incidence compiler at every explicit incidence boundary. -/
def output (input : List Token) : List AssemblerToken :=
  TM2EndDelimitedBlockMap.mappedOutput isEnd innerOutput input

@[simp] theorem output_inputTokens (blocks : List TaggedBlock) :
    output (inputTokens blocks) = outputTokens blocks := by
  unfold output TM2EndDelimitedBlockMap.mappedOutput outputTokens
  rw [blocks_inputTokens, List.flatMap_map]
  apply List.flatMap_congr
  intro block _
  exact innerOutput_requestBlock block.role block.incidence

noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    innerOutputComputableInPolyTime isEnd

namespace ContractedBlock

def roleBlocks : HorizontalAssembledContractedDirectionBlock →
    List TaggedBlock
  | .retained route => [⟨.retained, route⟩]
  | .through first second =>
      [⟨.throughFirst, first⟩, ⟨.throughSecond, second⟩]

def assemblerEdge : HorizontalAssembledContractedDirectionBlock →
    ContractedDirectionAssembler.EdgeBlock
  | .retained route => .retained route.directions
  | .through first second =>
      .through first.directions second.directions

@[simp] theorem flatMap_output_roleBlocks
    (block : HorizontalAssembledContractedDirectionBlock) :
    (roleBlocks block).flatMap TaggedBlock.output =
      (assemblerEdge block).inputTokens := by
  cases block <;>
    simp [roleBlocks, assemblerEdge, TaggedBlock.output,
      ContractedDirectionAssembler.EdgeBlock.inputTokens]

@[simp] theorem assemblerEdge_directions
    (block : HorizontalAssembledContractedDirectionBlock) :
    (assemblerEdge block).directions = block.directions := by
  cases block <;> rfl

end ContractedBlock

def contractedInputTokens
    (blocks : List HorizontalAssembledContractedDirectionBlock) : List Token :=
  inputTokens (blocks.flatMap ContractedBlock.roleBlocks)

def contractedOutput (input : List Token) :
    List NormalizationDirectionRequest.Batch.NormalizedToken :=
  ContractedDirectionAssembler.output (output input)

def contractedOutputTokens
    (blocks : List HorizontalAssembledContractedDirectionBlock) :
    List NormalizationDirectionRequest.Batch.NormalizedToken :=
  blocks.flatMap fun block =>
    NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
      block.directions

private theorem output_contractedInputTokens
    (blocks : List HorizontalAssembledContractedDirectionBlock) :
    output (contractedInputTokens blocks) =
      ContractedDirectionAssembler.inputTokens
        (blocks.map ContractedBlock.assemblerEdge) := by
  unfold contractedInputTokens
  rw [output_inputTokens]
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      rw [List.flatMap_cons, List.map_cons]
      unfold outputTokens ContractedDirectionAssembler.inputTokens
      simp only [List.flatMap_append, List.flatMap_cons]
      rw [ContractedBlock.flatMap_output_roleBlocks]
      have rest :
          List.flatMap TaggedBlock.output
              (List.flatMap ContractedBlock.roleBlocks blocks) =
            List.flatMap ContractedDirectionAssembler.EdgeBlock.inputTokens
              (List.map ContractedBlock.assemblerEdge blocks) := by
        simpa only [outputTokens,
          ContractedDirectionAssembler.inputTokens] using induction
      rw [rest]

@[simp] theorem contractedOutput_inputTokens
    (blocks : List HorizontalAssembledContractedDirectionBlock) :
    contractedOutput (contractedInputTokens blocks) =
      contractedOutputTokens blocks := by
  unfold contractedOutput
  rw [output_contractedInputTokens,
    ContractedDirectionAssembler.output_inputTokens]
  unfold contractedOutputTokens ContractedDirectionAssembler.outputTokens
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro block _
  rw [ContractedBlock.assemblerEdge_directions]

noncomputable def contractedOutputComputableInPolyTime :
    TM2ComputableInPolyTime id id contractedOutput := by
  let complete := TM2CompositionMachine.computableInPolyTime
    outputComputableInPolyTime
    ContractedDirectionAssembler.outputComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => ContractedDirectionAssembler.output (output input))
  exact complete

end HorizontalContractedRoutedRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
