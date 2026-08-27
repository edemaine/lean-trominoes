/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordBatchData
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteComplementRequestSemantics

/-! # Cursor-valid direct sparse route requests

This packages every compact direct route request with the cursor-validity
proof required by the concrete complement-counter batch machine.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNFStripReduction.RouteRasterRequest
open GadgetSparseRouteRecordMachine

/-- Package a list of values whose associated requests all satisfy the
cursor invariant.  Keeping this list operation generic prevents downstream
proofs from unfolding the direct geometric input. -/
def validRouteRequestsOfList {α : Type} (values : List α)
    (toRequest : α → RouteRasterRequest.Request)
    (valid : ∀ value ∈ values,
      (toRequest value).metadata.CursorValid) : List ValidRequest :=
  values.attach.map fun value =>
    ⟨toRequest value.1, valid value.1 value.2⟩

@[simp] theorem validRouteRequestsOfList_map_val {α : Type}
    (values : List α) (toRequest : α → RouteRasterRequest.Request)
    (valid : ∀ value ∈ values,
      (toRequest value).metadata.CursorValid) :
    (validRouteRequestsOfList values toRequest valid).map Subtype.val =
      values.map toRequest := by
  unfold validRouteRequestsOfList
  rw [List.map_map]
  change values.attach.map (toRequest ∘ Subtype.val) =
    values.map toRequest
  rw [← List.map_map, List.attach_map_subtype_val]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseValidRouteRequestDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Contracted edges, in canonical order, packaged as cursor-valid compact
route requests. -/
def directSparseValidRouteRasterRequestsOfSymbols
    (symbols : List encoding.Γ) : List ValidRequest :=
  let input := directSparseComputedNormalizationInputOfSymbols decider symbols
  validRouteRequestsOfList input.problem.contractedEdges
    (RouteRasterRequest.ofEdge input) fun _ member =>
      RouteRasterRequest.directSparse_ofEdge_cursorValid
        decider symbols member

/-- Forgetting validity proofs recovers the original compact request list. -/
@[simp] theorem directSparseValidRouteRasterRequests_map_val
    (symbols : List encoding.Γ) :
    (directSparseValidRouteRasterRequestsOfSymbols decider symbols).map
        Subtype.val =
      RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
        decider symbols := by
  unfold directSparseValidRouteRasterRequestsOfSymbols
    RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
  exact validRouteRequestsOfList_map_val _ _ _

end PeriodicCNFStripReduction
end LeanTrominoes

end
