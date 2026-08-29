/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordProfileFramingCompiler
import LeanTrominoes.DelimitedRouteJoinSemantics
import LeanTrominoes.FiniteRoleSlotUnaryDecoderArithmetic

/-! # Semantics of profile-framed aligned four-route streams -/

noncomputable section

namespace LeanTrominoes
namespace BinaryRouteTailRecordProfileFraming

open FiniteStateTransducer
open PeriodicThreeDM.NormalizationDirectionRequest.Batch

@[simp] theorem prefixOutput_eq_profilePrefixes
    (profiles : List Profile) :
    prefixOutput profiles = profilePrefixes profiles := by
  unfold prefixOutput FiniteStateTransducer.output
  change
    (scan prefixTransition .empty profiles).2 ++
        prefixFinish (scan prefixTransition .empty profiles).1 =
      profilePrefixes profiles
  simp only [prefixFinish, List.append_nil]
  induction profiles using List.twoStepInduction with
  | nil | singleton => rfl
  | cons_cons first second profiles induction _ =>
      simp only [scan, prefixTransition, profilePrefixes,
        List.nil_append]
      rw [induction]

private theorem scan_firstCode_north
    (code : CodeControl) (count : Nat) :
    scan decodeTransition (.firstCode code)
        (List.replicate count (.direction .north)) =
      (.firstCode (FiniteRoleSlotUnaryDecoder.advance code count), []) := by
  induction count generalizing code with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp only [scan, decodeTransition]
      rw [induction (FiniteRoleSlotUnaryDecoder.increment code)]
      simp [FiniteRoleSlotUnaryDecoder.advance_succ]

private theorem scan_secondCode_north
    (code : CodeControl) (count : Nat) :
    scan decodeTransition (.secondCode code)
        (List.replicate count (.direction .north)) =
      (.secondCode (FiniteRoleSlotUnaryDecoder.advance code count), []) := by
  induction count generalizing code with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp only [scan, decodeTransition]
      rw [induction (FiniteRoleSlotUnaryDecoder.increment code)]
      simp [FiniteRoleSlotUnaryDecoder.advance_succ]

private theorem decodedProfile_advance_profileCode
    (profile : Profile) :
    decodedProfile
        (FiniteRoleSlotUnaryDecoder.advance
          FiniteRoleSlotUnaryDecoder.zero (profileCode profile)) =
      profile := by
  have advanceEq :
      FiniteRoleSlotUnaryDecoder.advance
          (FiniteRoleSlotUnaryDecoder.zero (Role := Profile))
          (profileCode profile) =
        FiniteRoleSlotUnaryDecoder.boundedCode (profileCode profile) := by
    simpa [FiniteRoleSlotUnaryDecoder.zero] using
      (FiniteRoleSlotUnaryDecoder.advance_boundedCode
        (Role := Profile) 0 (profileCode profile))
  rw [advanceEq]
  have decoded := FiniteRoleSlotUnaryDecoder.decode_role_slot_index
    profile ⟨0, by omega⟩
  change
    (FiniteRoleSlotUnaryDecoder.decode
      (FiniteRoleSlotUnaryDecoder.boundedCode
        (profileCode profile))).1 = profile
  simpa [profileCode] using congrArg Prod.fst decoded

private theorem scan_profilePairDirections
    (first second : Profile) :
    scan decodeTransition decodeInitial
        ((profilePairDirections first second).map .direction) =
      (.firstRoute, [.firstProfile first, .secondProfile second]) := by
  unfold profilePairDirections profileCodeDirections decodeInitial
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil, scan_append]
  rw [scan_firstCode_north]
  simp only [scan, decodeTransition]
  rw [decodedProfile_advance_profileCode]
  simp only [List.nil_append]
  rw [scan_secondCode_north]
  simp only [scan, decodeTransition]
  rw [decodedProfile_advance_profileCode]
  rfl

private theorem scan_firstRoute_delimited
    (directions : List AxisDirection) :
    scan decodeTransition .firstRoute (delimited directions) =
      (.secondRoute, (delimited directions).map .source) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change
        scan decodeTransition .firstRoute
            (.direction direction :: delimited directions) =
          (.secondRoute,
            .source (.direction direction) ::
              (delimited directions).map .source)
      simp only [scan, decodeTransition]
      rw [induction]
      rfl

private theorem scan_secondRoute_delimited
    (directions : List AxisDirection) :
    scan decodeTransition .secondRoute (delimited directions) =
      (.thirdRoute, (delimited directions).map .source) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change
        scan decodeTransition .secondRoute
            (.direction direction :: delimited directions) =
          (.thirdRoute,
            .source (.direction direction) ::
              (delimited directions).map .source)
      simp only [scan, decodeTransition]
      rw [induction]
      rfl

private theorem scan_thirdRoute_delimited
    (directions : List AxisDirection) :
    scan decodeTransition .thirdRoute (delimited directions) =
      (.fourthRoute, (delimited directions).map .source) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change
        scan decodeTransition .thirdRoute
            (.direction direction :: delimited directions) =
          (.fourthRoute,
            .source (.direction direction) ::
              (delimited directions).map .source)
      simp only [scan, decodeTransition]
      rw [induction]
      rfl

private theorem scan_fourthRoute_delimited
    (directions : List AxisDirection) :
    scan decodeTransition .fourthRoute (delimited directions) =
      (decodeInitial, (delimited directions).map .source) := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      change
        scan decodeTransition .fourthRoute
            (.direction direction :: delimited directions) =
          (decodeInitial,
            .source (.direction direction) ::
              (delimited directions).map .source)
      simp only [scan, decodeTransition]
      rw [induction]
      rfl

private def encodedBlock
    (block : BinaryRouteTailRecordBatchFormatter.Block) : List RouteToken :=
  delimited
      (profilePairDirections block.firstProfile block.secondProfile ++
        block.first) ++
    delimited block.second ++ delimited block.third ++
      delimited block.fourth

private theorem profilePairPrefixBlock_eq
    (first second : Profile) :
    profilePairPrefixBlock first second =
      DelimitedRouteJoin.delimited (profilePairDirections first second) ++
        (DelimitedRouteJoin.delimited [] ++
          (DelimitedRouteJoin.delimited [] ++
            DelimitedRouteJoin.delimited [])) := by
  simp [profilePairPrefixBlock, delimited,
    DelimitedRouteJoin.delimited]

private theorem map_source_delimited
    (directions : List AxisDirection) :
    (delimited directions).map
        BinaryRouteTailRecordBatchFormatter.Token.source =
      BinaryRouteTailRecordBatchFormatter.sourceTokens directions := by
  simp [delimited, DelimitedRouteJoin.delimited,
    BinaryRouteTailRecordBatchFormatter.sourceTokens,
    PeriodicOrthocrossing.CarrierSpanRouteDirections.delimitedDirections,
    PeriodicOrthocrossing.CarrierSpanRouteDirections.directionTokens,
    List.map_append, List.map_map, Function.comp_def]

private theorem joined_profilePrefixes_blockRoutes
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    DelimitedRouteJoin.joined
        (profilePrefixes (blockProfiles blocks)) (blockRoutes blocks) =
      blocks.flatMap encodedBlock := by
  induction blocks with
  | nil =>
      simp [blockProfiles, blockRoutes, profilePrefixes,
        DelimitedRouteJoin.joined, DelimitedRouteJoin.joinedAux,
        DelimitedRouteJoin.resultAux]
  | cons block blocks induction =>
      change
        DelimitedRouteJoin.joined
            (profilePairPrefixBlock
                block.firstProfile block.secondProfile ++
              profilePrefixes (blockProfiles blocks))
            (delimited block.first ++ delimited block.second ++
              delimited block.third ++ delimited block.fourth ++
                blockRoutes blocks) =
          encodedBlock block ++ blocks.flatMap encodedBlock
      rw [profilePairPrefixBlock_eq]
      simp only [List.append_assoc]
      rw [DelimitedRouteJoin.joined_delimited_append,
        DelimitedRouteJoin.joined_delimited_append,
        DelimitedRouteJoin.joined_delimited_append,
        DelimitedRouteJoin.joined_delimited_append,
        induction]
      simp [encodedBlock, delimited, DelimitedRouteJoin.delimited]

private theorem scan_encodedBlock
    (block : BinaryRouteTailRecordBatchFormatter.Block) :
    scan decodeTransition decodeInitial (encodedBlock block) =
      (decodeInitial,
        BinaryRouteTailRecordBatchFormatter.blockTokens block) := by
  unfold encodedBlock
  rw [show
    delimited
        (profilePairDirections block.firstProfile block.secondProfile ++
          block.first) =
      (profilePairDirections
        block.firstProfile block.secondProfile).map .direction ++
        delimited block.first by
      simp [delimited, DelimitedRouteJoin.delimited, List.map_append]]
  simp only [List.append_assoc]
  rw [scan_append, scan_profilePairDirections]
  dsimp only
  rw [scan_append, scan_firstRoute_delimited]
  dsimp only
  rw [scan_append, scan_secondRoute_delimited]
  dsimp only
  rw [scan_append, scan_thirdRoute_delimited]
  dsimp only
  rw [scan_fourthRoute_delimited]
  rw [map_source_delimited, map_source_delimited,
    map_source_delimited, map_source_delimited]
  simp [BinaryRouteTailRecordBatchFormatter.blockTokens,
    List.append_assoc]

private theorem scan_encodedBlocks
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    scan decodeTransition decodeInitial (blocks.flatMap encodedBlock) =
      (decodeInitial, BinaryRouteTailRecordBatchFormatter.tokens blocks) := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.flatMap_cons,
        BinaryRouteTailRecordBatchFormatter.tokens, scan_append]
      rw [scan_encodedBlock]
      dsimp only
      rw [induction]
      rfl

/-- On canonical profile pairs and their aligned four-route blocks, the
compiled framing path reconstructs exactly the declarative batch tokens. -/
@[simp] theorem framed_blockProfiles_blockRoutes
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    framed (blockProfiles blocks) (blockRoutes blocks) =
      BinaryRouteTailRecordBatchFormatter.tokens blocks := by
  unfold framed decodeOutput FiniteStateTransducer.output
  rw [prefixOutput_eq_profilePrefixes,
    joined_profilePrefixes_blockRoutes, scan_encodedBlocks]
  simp [decodeFinish]

end BinaryRouteTailRecordProfileFraming
end LeanTrominoes

end
