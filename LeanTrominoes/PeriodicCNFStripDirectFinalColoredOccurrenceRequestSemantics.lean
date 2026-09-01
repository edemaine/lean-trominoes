/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinSemantics
import LeanTrominoes.PeriodicCNFStripDirectFinalColoredOccurrenceRequestData

/-! # Semantics of aligned colored occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace DirectFinalColoredOccurrenceRequest

@[simp] theorem routedBlocks_append
    (first second : List RoutedBlockToken) :
    routedBlocks (first ++ second) =
      routedBlocks first ++ routedBlocks second := by
  simp [routedBlocks]

@[simp] theorem routedBlocks_routedSourceBlock
    (route : List RouteToken) :
    routedBlocks (routedSourceBlock route) =
      FiniteAlphabetDelimitedBlockJoin.block (routedBody route) := by
  unfold routedBlocks routedSourceBlock routedBody
    FiniteAlphabetDelimitedBlockJoin.block
  rw [List.flatMap_append, List.flatMap_map]
  simp only [routedBlockToken, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [← List.map_eq_flatMap]
  rw [List.map_map]
  change (route.map fun token =>
      (FiniteAlphabetDelimitedBlockJoin.Token.value
        (.routed token) : Token)) ++ [.blockEnd] = _
  rfl

@[simp] theorem routedBlocks_routedSourceBlocks
    (routes : List (List RouteToken)) :
    routedBlocks (routedSourceBlocks routes) =
      FiniteAlphabetDelimitedBlockJoin.blocks (routes.map routedBody) := by
  induction routes with
  | nil => rfl
  | cons route routes induction =>
      rw [show routedSourceBlocks (route :: routes) =
          routedSourceBlock route ++ routedSourceBlocks routes by rfl,
        routedBlocks_append, routedBlocks_routedSourceBlock, induction]
      rfl

@[simp] theorem openingBlocks_eq_blocks (frames : List Frame) :
    openingBlocks frames =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (frames.map openingBody) := by
  unfold openingBlocks FiniteAlphabetDelimitedBlockJoin.blocks openingBlock
  rw [List.flatMap_map]

@[simp] theorem trailingBlocks_eq_blocks (frames : List Frame) :
    trailingBlocks frames =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (frames.map trailingBody) := by
  unfold trailingBlocks FiniteAlphabetDelimitedBlockJoin.blocks trailingBlock
  rw [List.flatMap_map]

/-- On explicitly paired endpoint frames and route bodies, the two joins
produce exactly one complete occurrence request per pair. -/
@[simp] theorem output_paired
    (pairs : List (Frame × List RouteToken)) :
    output (pairs.map Prod.fst)
        (routedSourceBlocks (pairs.map Prod.snd)) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (pairs.map fun pair =>
          openingBody pair.1 ++ routedBody pair.2 ++
            trailingBody pair.1) := by
  have openedEq :
      opened (pairs.map Prod.fst)
          (routedSourceBlocks (pairs.map Prod.snd)) =
        FiniteAlphabetDelimitedBlockJoin.blocks
          (pairs.map fun pair =>
            openingBody pair.1 ++ routedBody pair.2) := by
    unfold opened
    rw [openingBlocks_eq_blocks, routedBlocks_routedSourceBlocks]
    simpa [List.map_map, Function.comp_def] using
      FiniteAlphabetDelimitedBlockJoin.joined_pairedBlocks
        (pairs.map fun pair =>
          (openingBody pair.1, routedBody pair.2))
  unfold output
  rw [openedEq, trailingBlocks_eq_blocks]
  simpa [List.map_map, Function.comp_def, List.append_assoc] using
    FiniteAlphabetDelimitedBlockJoin.joined_pairedBlocks
      (pairs.map fun pair =>
        (openingBody pair.1 ++ routedBody pair.2,
          trailingBody pair.1))

/-- With a canonical routed block, the aligned body is exactly the established
compact occurrence-request input. -/
@[simp] theorem output_canonicalPairs
    (pairs : List (Frame × HorizontalRoutedRouteDirectionBlock)) :
    output (pairs.map Prod.fst)
        (routedSourceBlocks
          (pairs.map fun pair =>
            HorizontalRoutedRouteDirectionRequest.tokens pair.2)) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (pairs.map fun pair =>
          DirectFinalOccurrenceEndpointFrame.routedTokens
            pair.1 pair.2) := by
  have expanded := output_paired
    (pairs.map fun pair =>
      (pair.1, HorizontalRoutedRouteDirectionRequest.tokens pair.2))
  simpa [List.map_map, Function.comp_def,
    openingBody, routedBody, trailingBody,
    DirectFinalOccurrenceEndpointFrame.routedTokens,
    HorizontalOccurrenceRoutedRequest.tokens] using expanded

end DirectFinalColoredOccurrenceRequest
end LeanTrominoes.PeriodicCNFStripReduction

end
