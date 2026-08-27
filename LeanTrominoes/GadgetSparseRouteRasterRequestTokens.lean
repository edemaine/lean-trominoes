/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRasterRequestTokenData

/-! # Finite tokens for compact raster route requests

Three fixed factor-twelve transductions expand compact coordinate units into
ordinary unary units.  All finite metadata and direction-normalization tokens
pass through unchanged.
-/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseRouteRasterRequestTokens

open PeriodicCNFStripReduction.RouteRasterRequest

@[simp] theorem firstExpand_append (first second : List Token) :
    firstExpand (first ++ second) =
      firstExpand first ++ firstExpand second := by
  simp [firstExpand]

@[simp] theorem secondExpand_append
    (first second : List IntermediateToken) :
    secondExpand (first ++ second) =
      secondExpand first ++ secondExpand second := by
  simp [secondExpand]

@[simp] theorem thirdExpand_append
    (first second : List PreparedToken) :
    thirdExpand (first ++ second) =
      thirdExpand first ++ thirdExpand second := by
  simp [thirdExpand]

@[simp] theorem expand_append (first second : List Token) :
    expand (first ++ second) = expand first ++ expand second := by
  simp [expand]

@[simp] theorem secondExpand_replicate_scale144Unit (count : Nat) :
    secondExpand (List.replicate count .scale144Unit) =
      List.replicate (12 * count) .scale12Unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change List.replicate 12 .scale12Unit ++
          secondExpand (List.replicate count .scale144Unit) = _
      rw [induction, ← List.replicate_add]
      congr 1
      omega

@[simp] theorem secondExpand_replicate_scale12Unit (count : Nat) :
    secondExpand (List.replicate count .scale12Unit) =
      List.replicate count .scale12Unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change .scale12Unit ::
        secondExpand (List.replicate count .scale12Unit) = _
      rw [induction, List.replicate_succ]

@[simp] theorem secondExpand_replicate_unit (count : Nat) :
    secondExpand (List.replicate count .unit) =
      List.replicate count .unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change .unit :: secondExpand (List.replicate count .unit) = _
      rw [induction, List.replicate_succ]

@[simp] theorem thirdExpand_replicate_scale12Unit (count : Nat) :
    thirdExpand (List.replicate count .scale12Unit) =
      List.replicate (12 * count) .unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change List.replicate 12 .unit ++
          thirdExpand (List.replicate count .scale12Unit) = _
      rw [induction, ← List.replicate_add]
      congr 1
      omega

@[simp] theorem thirdExpand_replicate_unit (count : Nat) :
    thirdExpand (List.replicate count .unit) =
      List.replicate count .unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      change .unit :: thirdExpand (List.replicate count .unit) = _
      rw [induction, List.replicate_succ]

@[simp] theorem expand_singleton_scaledUnit :
    expand [.scaledUnit] = List.replicate 1728 .unit := by
  change thirdExpand
    (secondExpand (List.replicate 12 .scale144Unit)) = _
  rw [secondExpand_replicate_scale144Unit,
    thirdExpand_replicate_scale12Unit]

@[simp] theorem expand_singleton_horizontalOffset :
    expand [.horizontalOffset] = List.replicate 471 .unit := by
  change thirdExpand (secondExpand
    (List.replicate 3 .scale144Unit ++
      List.replicate 3 .scale12Unit ++ List.replicate 3 .unit)) = _
  rw [secondExpand_append, secondExpand_append,
    secondExpand_replicate_scale144Unit,
    secondExpand_replicate_scale12Unit,
    secondExpand_replicate_unit,
    thirdExpand_append, thirdExpand_append,
    thirdExpand_replicate_scale12Unit,
    thirdExpand_replicate_scale12Unit,
    thirdExpand_replicate_unit,
    ← List.replicate_add, ← List.replicate_add]

@[simp] theorem expand_singleton_verticalOffset :
    expand [.verticalOffset] = List.replicate 1257 .unit := by
  change thirdExpand (secondExpand
    (List.replicate 8 .scale144Unit ++
      List.replicate 8 .scale12Unit ++ List.replicate 9 .unit)) = _
  rw [secondExpand_append, secondExpand_append,
    secondExpand_replicate_scale144Unit,
    secondExpand_replicate_scale12Unit,
    secondExpand_replicate_unit,
    thirdExpand_append, thirdExpand_append,
    thirdExpand_replicate_scale12Unit,
    thirdExpand_replicate_scale12Unit,
    thirdExpand_replicate_unit,
    ← List.replicate_add, ← List.replicate_add]

theorem expand_cons (token : Token) (tokens : List Token) :
    expand (token :: tokens) = expand [token] ++ expand tokens := by
  change expand ([token] ++ tokens) = _
  rw [expand_append]

@[simp] theorem expand_replicate_scaledUnit (count : Nat) :
    expand (List.replicate count .scaledUnit) =
      List.replicate (1728 * count) .unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, expand_cons,
        expand_singleton_scaledUnit, induction, ← List.replicate_add]
      congr 1
      omega

@[simp] theorem expand_singleton_periodEnd :
    expand [.periodEnd] = [.periodEnd] := rfl

@[simp] theorem expand_singleton_horizontalEnd :
    expand [.horizontalEnd] = [.horizontalEnd] := rfl

@[simp] theorem expand_singleton_verticalEnd :
    expand [.verticalEnd] = [.verticalEnd] := rfl

@[simp] theorem expand_singleton_color (color : Gadget.WireColor) :
    expand [.color color] = [.color color] := rfl

@[simp] theorem expand_singleton_normalization
    (token : NormalizationToken) :
    expand [.normalization token] = [.normalization token] := rfl

@[simp] theorem expand_singleton_requestEnd :
    expand [.requestEnd] = [.requestEnd] := rfl

@[simp] theorem expand_map_normalization (tokens : List NormalizationToken) :
    expand (tokens.map .normalization) =
      tokens.map .normalization := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      rw [List.map_cons, expand_cons,
        expand_singleton_normalization, induction]
      rfl

@[simp] theorem expand_metadataTokens (metadata : Metadata) :
    expand (metadataTokens metadata) = expandedMetadataTokens metadata := by
  unfold metadataTokens expandedMetadataTokens Metadata.period
  simp only [expand_append, expand_replicate_scaledUnit,
    expand_singleton_periodEnd, expand_singleton_horizontalOffset,
    expand_singleton_horizontalEnd, expand_singleton_verticalOffset,
    expand_singleton_verticalEnd, expand_singleton_color]
  simp only [← List.replicate_add, List.append_assoc]

@[simp] theorem expand_requestBlock (request : Request) :
    expand (requestBlock request) = expandedRequestBlock request := by
  unfold requestBlock requestTokens expandedRequestBlock
  simp

@[simp] theorem expand_tokens (requests : List Request) :
    expand (tokens requests) = expandedTokens requests := by
  unfold tokens expandedTokens
  induction requests with
  | nil => rfl
  | cons request requests induction =>
      rw [List.flatMap_cons, List.flatMap_cons, expand_append,
        expand_requestBlock, induction]

end GadgetSparseRouteRasterRequestTokens
end LeanTrominoes

end
