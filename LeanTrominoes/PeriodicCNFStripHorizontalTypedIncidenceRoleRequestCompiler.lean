/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceRoleRequestData

/-! # Compiler for role-tagged compact typed-incidence requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalTypedIncidenceRoleRequest

open Computability Turing

abbrev State := HorizontalOccurrenceDirectionRequest.State

def initial : State := HorizontalOccurrenceDirectionRequest.initial

/-- Reuse the occurrence-request control while reinterpreting its direction
output for the contracted assembler. -/
def transition (state : State) : Token → State × List AssemblerToken
  | .role role => (state, [.role role])
  | .request token =>
      let current :=
        HorizontalOccurrenceDirectionRequest.transition state token
      (current.1, current.2.map fun direction =>
        PeriodicThreeDM.ContractedDirectionAssembler.Token.direction
          direction)
  | .requestEnd => (state, [.incidenceEnd])

def finish (_ : State) : List AssemblerToken := []

def output (input : List Token) : List AssemblerToken :=
  FiniteStateTransducer.output initial transition finish input

private theorem scan_request_map
    (state : State) (request : List InnerToken) :
    FiniteStateTransducer.scan transition state
        (request.map Token.request) =
      let scanned := FiniteStateTransducer.scan
        HorizontalOccurrenceDirectionRequest.transition state request
      (scanned.1, scanned.2.map fun direction =>
        PeriodicThreeDM.ContractedDirectionAssembler.Token.direction
          direction) := by
  induction request generalizing state with
  | nil => rfl
  | cons token request induction =>
      simp only [List.map_cons, FiniteStateTransducer.scan, transition]
      let current :=
        HorizontalOccurrenceDirectionRequest.transition state token
      rw [induction current.1]
      simp [current, List.map_append]

/-- A canonical role request compiles to exactly the assembler's canonical
role block for the underlying occurrence-request direction word. -/
@[simp] theorem output_requestBlock
    (role : Role) (request : List InnerToken) :
    output (requestBlock role request) =
      PeriodicThreeDM.ContractedDirectionAssembler.roleBlock role
        (HorizontalOccurrenceDirectionRequest.output request) := by
  unfold output requestBlock
    PeriodicThreeDM.ContractedDirectionAssembler.roleBlock
    HorizontalOccurrenceDirectionRequest.output
    FiniteStateTransducer.output
  rw [show ([Token.role role] ++ request.map Token.request ++
        [Token.requestEnd]) =
      [Token.role role] ++
        (request.map Token.request ++ [Token.requestEnd]) by
    rw [List.append_assoc]]
  rw [FiniteStateTransducer.scan_append]
  simp only [FiniteStateTransducer.scan, transition]
  rw [FiniteStateTransducer.scan_append]
  rw [scan_request_map]
  simp [FiniteStateTransducer.scan, transition, finish, initial,
    HorizontalOccurrenceDirectionRequest.finish]

/-- A classified typed incidence therefore compiles to its exact direction
word, tagged for its retained or through role. -/
@[simp] theorem output_blockTokens
    (role : Role) (block : HorizontalTypedIncidenceDirectionBlock) :
    output (blockTokens role block) =
      PeriodicThreeDM.ContractedDirectionAssembler.roleBlock role
        block.directions := by
  unfold blockTokens
  rw [output_requestBlock,
    HorizontalTypedIncidenceDirectionBlock.output_requestTokens]

/-- The role wrapper is one fixed finite-state linear-time compiler. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

end HorizontalTypedIncidenceRoleRequest
end PeriodicCNFStripReduction
end LeanTrominoes

end
