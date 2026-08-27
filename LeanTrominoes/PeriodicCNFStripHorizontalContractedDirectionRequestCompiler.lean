/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledContractedDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceRoleRequestCompiler
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerBatchCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiler for compact horizontal contracted-direction requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalContractedDirectionRequest

open Computability Turing
open PeriodicThreeDM

namespace RoleRequest

abbrev Token := HorizontalTypedIncidenceRoleRequest.Token
abbrev Role := ContractedDirectionAssembler.Role

/-- A role paired with the compact classified incidence serving that role. -/
structure Block where
  role : Role
  incidence : HorizontalTypedIncidenceDirectionBlock

noncomputable def Block.tokens (block : Block) : List Token :=
  HorizontalTypedIncidenceRoleRequest.blockTokens
    block.role block.incidence

def Block.output (block : Block) :
    List ContractedDirectionAssembler.Token :=
  ContractedDirectionAssembler.roleBlock
    block.role block.incidence.directions

def inputTokens (blocks : List Block) : List Token :=
  blocks.flatMap Block.tokens

def outputTokens (blocks : List Block) :
    List ContractedDirectionAssembler.Token :=
  blocks.flatMap Block.output

private theorem requestBlock_continues
    (role : Role) (request : List HorizontalTypedIncidenceRoleRequest.InnerToken) :
    ∀ token ∈
        ([HorizontalTypedIncidenceRoleRequest.Token.role role] ++
          request.map HorizontalTypedIncidenceRoleRequest.Token.request),
      HorizontalTypedIncidenceRoleRequest.isEnd token = false := by
  intro token member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with rfl | member
  · rfl
  · obtain ⟨inner, _, rfl⟩ := List.mem_map.mp member
    rfl

private theorem blocksAux_append_requestEnd
    (reverseBlock body rest : List Token)
    (continues : ∀ token ∈ body,
      HorizontalTypedIncidenceRoleRequest.isEnd token = false) :
    TM2EndDelimitedBlockMap.blocksAux
        HorizontalTypedIncidenceRoleRequest.isEnd reverseBlock
        (body ++ HorizontalTypedIncidenceRoleRequest.Token.requestEnd ::
          rest) =
      (reverseBlock.reverse ++ body ++
          [HorizontalTypedIncidenceRoleRequest.Token.requestEnd]) ::
        TM2EndDelimitedBlockMap.blocksAux
          HorizontalTypedIncidenceRoleRequest.isEnd [] rest := by
  induction body generalizing reverseBlock with
  | nil =>
      simp [TM2EndDelimitedBlockMap.blocksAux,
        HorizontalTypedIncidenceRoleRequest.isEnd]
  | cons token body induction =>
      have tokenContinues := continues token (by simp)
      have bodyContinues : ∀ other ∈ body,
          HorizontalTypedIncidenceRoleRequest.isEnd other = false := by
        intro other member
        exact continues other (by simp [member])
      rw [List.cons_append, TM2EndDelimitedBlockMap.blocksAux]
      simp only [tokenContinues, Bool.false_eq_true, ↓reduceIte]
      rw [induction (token :: reverseBlock) bodyContinues]
      simp [List.reverse_cons, List.append_assoc]

private theorem blocksAux_requestBlock_append
    (reverseBlock : List Token)
    (role : Role)
    (request : List HorizontalTypedIncidenceRoleRequest.InnerToken)
    (rest : List Token) :
    TM2EndDelimitedBlockMap.blocksAux
        HorizontalTypedIncidenceRoleRequest.isEnd reverseBlock
        (HorizontalTypedIncidenceRoleRequest.requestBlock role request ++
          rest) =
      (reverseBlock.reverse ++
          HorizontalTypedIncidenceRoleRequest.requestBlock role request) ::
        TM2EndDelimitedBlockMap.blocksAux
          HorizontalTypedIncidenceRoleRequest.isEnd [] rest := by
  unfold HorizontalTypedIncidenceRoleRequest.requestBlock
  rw [List.append_assoc]
  simpa [List.append_assoc] using blocksAux_append_requestEnd
    reverseBlock
    ([HorizontalTypedIncidenceRoleRequest.Token.role role] ++
      request.map HorizontalTypedIncidenceRoleRequest.Token.request)
    rest (requestBlock_continues role request)

@[simp] theorem blocks_inputTokens (blocks : List Block) :
    TM2EndDelimitedBlockMap.blocks
        HorizontalTypedIncidenceRoleRequest.isEnd (inputTokens blocks) =
      blocks.map Block.tokens := by
  unfold TM2EndDelimitedBlockMap.blocks inputTokens
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      rw [List.flatMap_cons]
      rw [show Block.tokens block =
        HorizontalTypedIncidenceRoleRequest.requestBlock block.role
          block.incidence.requestTokens by rfl]
      rw [blocksAux_requestBlock_append]
      simp only [List.reverse_nil, List.nil_append, List.map_cons]
      rw [induction]
      rfl

/-- Reset and run the verified role wrapper independently on every explicit
incidence boundary. -/
def output (input : List Token) :
    List ContractedDirectionAssembler.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    HorizontalTypedIncidenceRoleRequest.isEnd
    HorizontalTypedIncidenceRoleRequest.output input

@[simp] theorem output_inputTokens (blocks : List Block) :
    output (inputTokens blocks) = outputTokens blocks := by
  unfold output TM2EndDelimitedBlockMap.mappedOutput outputTokens
  rw [blocks_inputTokens, List.flatMap_map]
  apply List.flatMap_congr
  intro block _
  unfold Block.tokens Block.output
    HorizontalTypedIncidenceRoleRequest.blockTokens
  exact HorizontalTypedIncidenceRoleRequest.output_blockTokens
    block.role block.incidence

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    HorizontalTypedIncidenceRoleRequest.computableInPolyTime
    HorizontalTypedIncidenceRoleRequest.isEnd

end RoleRequest

namespace ContractedBlock

def roleBlocks : HorizontalAssembledContractedDirectionBlock →
    List RoleRequest.Block
  | .retained route =>
      [⟨.retained, route⟩]
  | .through first second =>
      [⟨.throughFirst, first⟩, ⟨.throughSecond, second⟩]

def assemblerEdge : HorizontalAssembledContractedDirectionBlock →
    ContractedDirectionAssembler.EdgeBlock
  | .retained route => .retained route.directions
  | .through first second =>
      .through first.directions second.directions

@[simp] theorem flatMap_output_roleBlocks
    (block : HorizontalAssembledContractedDirectionBlock) :
    (roleBlocks block).flatMap RoleRequest.Block.output =
      (assemblerEdge block).inputTokens := by
  cases block <;>
    simp [roleBlocks, assemblerEdge, RoleRequest.Block.output,
      ContractedDirectionAssembler.EdgeBlock.inputTokens]

@[simp] theorem assemblerEdge_directions
    (block : HorizontalAssembledContractedDirectionBlock) :
    (assemblerEdge block).directions = block.directions := by
  cases block <;> rfl

end ContractedBlock

/-- Compact role-request source for a list of classified contracted edges. -/
noncomputable def inputTokens
    (blocks : List HorizontalAssembledContractedDirectionBlock) :
    List RoleRequest.Token :=
  RoleRequest.inputTokens (blocks.flatMap
    ContractedBlock.roleBlocks)

/-- Run role tagging and then the existing contracted-word assembler. -/
def output (input : List RoleRequest.Token) :
    List NormalizationDirectionRequest.Batch.NormalizedToken :=
  ContractedDirectionAssembler.output (RoleRequest.output input)

def outputTokens
    (blocks : List HorizontalAssembledContractedDirectionBlock) :
    List NormalizationDirectionRequest.Batch.NormalizedToken :=
  blocks.flatMap fun block =>
    NormalizationDirectionRequest.Batch.DelimitedReversal.routeBlock
      block.directions

private theorem roleOutput_inputTokens
    (blocks : List HorizontalAssembledContractedDirectionBlock) :
    RoleRequest.output (inputTokens blocks) =
      ContractedDirectionAssembler.inputTokens
        (blocks.map
          ContractedBlock.assemblerEdge) := by
  unfold inputTokens
  rw [RoleRequest.output_inputTokens]
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      rw [List.flatMap_cons, List.map_cons]
      unfold RoleRequest.outputTokens
        ContractedDirectionAssembler.inputTokens
      simp only [List.flatMap_append, List.flatMap_cons]
      rw [ContractedBlock.flatMap_output_roleBlocks]
      have rest :
          List.flatMap RoleRequest.Block.output
              (List.flatMap ContractedBlock.roleBlocks blocks) =
            List.flatMap ContractedDirectionAssembler.EdgeBlock.inputTokens
              (List.map ContractedBlock.assemblerEdge blocks) := by
        simpa only [RoleRequest.outputTokens,
          ContractedDirectionAssembler.inputTokens] using induction
      rw [rest]

/-- Retained and through compact requests compile to their exact contracted
direction words, with one final route boundary per contracted edge. -/
@[simp] theorem output_inputTokens
    (blocks : List HorizontalAssembledContractedDirectionBlock) :
    output (inputTokens blocks) = outputTokens blocks := by
  unfold output
  rw [roleOutput_inputTokens]
  rw [ContractedDirectionAssembler.output_inputTokens]
  unfold outputTokens ContractedDirectionAssembler.outputTokens
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro block _
  rw [ContractedBlock.assemblerEdge_directions]

/-- The complete role-tagging and contracted assembly pipeline is
polynomial-time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output := by
  let complete := TM2CompositionMachine.computableInPolyTime
    RoleRequest.computableInPolyTime
    ContractedDirectionAssembler.outputComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => ContractedDirectionAssembler.output
      (RoleRequest.output input))
  exact complete

end HorizontalContractedDirectionRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
