/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCanonicalCompiler

/-! # Canonical batches of valid normalized route requests -/

namespace LeanTrominoes

namespace GadgetSparseRouteRecordBatch

open GadgetSparseRouteRecordMachine
open PeriodicCNFStripReduction.RouteRasterRequest

def isEnd : InputToken → Bool
  | .routeEnd => true
  | _ => false

/-- The delimiter-free portion of one canonical normalized request. -/
def requestBody (request : ValidRequest) : List InputToken :=
  List.replicate request.1.metadata.period .unit ++
    .periodEnd ::
      (List.replicate request.1.metadata.cursorHorizontal .unit ++
        .horizontalEnd ::
          (List.replicate request.1.metadata.cursorVertical .unit ++
            .verticalEnd :: .color request.1.metadata.color ::
              (GadgetSparseRouteRecordMachine.requestDirections request.1).map
                .direction))

@[simp] theorem validRequestInput_eq_body (request : ValidRequest) :
    validRequestInput request = requestBody request ++ [.routeEnd] := by
  unfold validRequestInput requestBody
  rw [GadgetSparseRouteRecordTokens.normalizedRequestBlock_eq]
  simp [GadgetSparseRouteRecordMachine.requestDirections,
    List.append_assoc]

theorem requestBody_continues (request : ValidRequest) :
    ∀ token ∈ requestBody request, isEnd token = false := by
  intro token member
  unfold requestBody at member
  simp only [List.mem_append, List.mem_replicate, List.mem_cons,
    List.mem_map] at member
  rcases member with
      ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl | ⟨_, rfl⟩ | rfl | rfl |
        ⟨direction, _, rfl⟩ <;>
    rfl

@[simp] theorem isEnd_routeEnd : isEnd .routeEnd = true := rfl

def input (requests : List ValidRequest) : List InputToken :=
  requests.flatMap validRequestInput

def output (requests : List ValidRequest) : List OutputToken :=
  requests.flatMap validRequestOutput

@[simp] theorem input_nil : input [] = [] := rfl

@[simp] theorem input_cons (request : ValidRequest)
    (requests : List ValidRequest) :
    input (request :: requests) =
      requestBody request ++ .routeEnd :: input requests := by
  simp [input, validRequestInput_eq_body, List.append_assoc]

@[simp] theorem output_nil : output [] = [] := rfl

@[simp] theorem output_cons (request : ValidRequest)
    (requests : List ValidRequest) :
    output (request :: requests) =
      validRequestOutput request ++ output requests := by
  simp [output]

@[simp] theorem input_length_pos (request : ValidRequest) :
    0 < (validRequestInput request).length := by
  rw [validRequestInput_eq_body]
  simp

theorem requests_length_le_input_length
    (requests : List ValidRequest) :
    requests.length ≤ (input requests).length := by
  induction requests with
  | nil => simp
  | cons request requests induction =>
      rw [input_cons]
      simp only [List.length_append, List.length_cons]
      omega

end GadgetSparseRouteRecordBatch
end LeanTrominoes
