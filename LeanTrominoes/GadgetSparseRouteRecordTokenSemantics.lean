/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteComplementRequest
import LeanTrominoes.GadgetSparseRouteRasterNormalizedTokenSemantics

/-! # Semantics of normalized route-record tokens

The executable route machine consumes one delimiter-terminated normalized
request at a time.  This file fixes its total behavior independently of the
machine implementation: malformed metadata produces no records, while a
well-formed prefix is interpreted by complementary horizontal counters.
-/

namespace LeanTrominoes
namespace GadgetSparseRouteRecordTokens

open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.RouteRasterRequest
open GadgetSparseRouteRasterNormalizedTokens

abbrev InputToken := GadgetSparseRouteRasterNormalizedTokens.Token
abbrev OutputToken := GadgetSparseAssignmentTokens.Token

/-- Count a leading unary field, retaining the first non-unit token. -/
def readUnits : Nat → List InputToken → Nat × List InputToken
  | count, .unit :: tokens => readUnits (count + 1) tokens
  | count, tokens => (count, tokens)
termination_by _ tokens => tokens.length

@[simp] theorem readUnits_periodEnd (count : Nat)
    (tokens : List InputToken) :
    readUnits count (.periodEnd :: tokens) =
      (count, .periodEnd :: tokens) := by
  simp [readUnits]

@[simp] theorem readUnits_horizontalEnd (count : Nat)
    (tokens : List InputToken) :
    readUnits count (.horizontalEnd :: tokens) =
      (count, .horizontalEnd :: tokens) := by
  simp [readUnits]

@[simp] theorem readUnits_verticalEnd (count : Nat)
    (tokens : List InputToken) :
    readUnits count (.verticalEnd :: tokens) =
      (count, .verticalEnd :: tokens) := by
  simp [readUnits]

theorem readUnits_replicate_periodEnd (initial count : Nat)
    (tokens : List InputToken) :
    readUnits initial
        (List.replicate count Token.unit ++ (.periodEnd :: tokens)) =
      (initial + count, .periodEnd :: tokens) := by
  induction count generalizing initial with
  | zero => simp
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [readUnits]
      rw [induction]
      congr 1
      omega

theorem readUnits_replicate_horizontalEnd (initial count : Nat)
    (tokens : List InputToken) :
    readUnits initial
        (List.replicate count Token.unit ++ (.horizontalEnd :: tokens)) =
      (initial + count, .horizontalEnd :: tokens) := by
  induction count generalizing initial with
  | zero => simp
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [readUnits]
      rw [induction]
      congr 1
      omega

theorem readUnits_replicate_verticalEnd (initial count : Nat)
    (tokens : List InputToken) :
    readUnits initial
        (List.replicate count Token.unit ++ (.verticalEnd :: tokens)) =
      (initial + count, .verticalEnd :: tokens) := by
  induction count generalizing initial with
  | zero => simp
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append]
      simp only [readUnits]
      rw [induction]
      congr 1
      omega

/-- Maximal leading finite-direction word. -/
def readDirections : List InputToken → List AxisDirection
  | .direction direction :: tokens => direction :: readDirections tokens
  | _ => []

@[simp] theorem readDirections_map_routeEnd
    (directions : List AxisDirection) :
    readDirections
        (directions.map Token.direction ++ [.routeEnd]) =
      directions := by
  induction directions with
  | nil => rfl
  | cons direction directions induction =>
      simp [readDirections, induction]

/-- Successfully decoded machine state at the start of a route. -/
structure ParsedRequest where
  location : ComplementLocation
  color : Gadget.WireColor
  directions : List AxisDirection
  deriving DecidableEq, Repr

/-- Total one-block parser.  The strict horizontal bound is exactly what is
needed to reserve the missing `+ 1` position in the complement counter. -/
def parse? (tokens : List InputToken) : Option ParsedRequest :=
  let (period, afterPeriod) := readUnits 0 tokens
  match afterPeriod with
  | .periodEnd :: horizontalTokens =>
      let (horizontal, afterHorizontal) :=
        readUnits 0 horizontalTokens
      match afterHorizontal with
      | .horizontalEnd :: verticalTokens =>
          let (vertical, afterVertical) := readUnits 0 verticalTokens
          match afterVertical with
          | .verticalEnd :: .color color :: directions =>
              if horizontal < period then
                some
                  { location :=
                      ⟨horizontal, period - horizontal - 1, vertical⟩
                    color := color
                    directions := readDirections directions }
              else
                none
          | _ => none
      | _ => none
  | _ => none

/-- Canonical assignment-token word denoted by an arbitrary normalized
one-request block. -/
def output (tokens : List InputToken) : List OutputToken :=
  match parse? tokens with
  | none => []
  | some request =>
      sparseRouteRecordBlocksFromComplementDirections request.color
        request.location request.directions

@[simp] theorem metadataOutput_replicate_unit (count : Nat) :
    metadataOutput
        (List.replicate count
          GadgetSparseRouteRasterRequestTokens.ExpandedToken.unit) =
      List.replicate count Token.unit := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.replicate_succ]
      change [Token.unit] ++ metadataOutput
          (List.replicate count
            GadgetSparseRouteRasterRequestTokens.ExpandedToken.unit) =
        Token.unit :: List.replicate count Token.unit
      rw [induction]
      rfl

theorem metadataOutput_expandedMetadataTokens_eq (metadata : Metadata) :
    metadataOutput
        (GadgetSparseRouteRasterRequestTokens.expandedMetadataTokens
          metadata) =
      List.replicate metadata.period .unit ++ [.periodEnd] ++
        List.replicate metadata.cursorHorizontal .unit ++
          [.horizontalEnd] ++
        List.replicate metadata.cursorVertical .unit ++
          [.verticalEnd] ++ [.color metadata.color] := by
  unfold GadgetSparseRouteRasterRequestTokens.expandedMetadataTokens
    Metadata.cursorHorizontal Metadata.cursorVertical
  simp only [metadataOutput_append, metadataOutput_replicate_unit]
  simp [metadataOutput, metadataBlock]

theorem normalizedRequestBlock_eq (request : Request) :
    normalizedRequestBlock request =
      List.replicate request.metadata.period .unit ++
        .periodEnd ::
          (List.replicate request.metadata.cursorHorizontal .unit ++
            .horizontalEnd ::
              (List.replicate request.metadata.cursorVertical .unit ++
                .verticalEnd :: .color request.metadata.color ::
                  ((PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
                    request.normalization).directions.map .direction ++
                      [.routeEnd]))) := by
  unfold normalizedRequestBlock directionOutput
  rw [metadataOutput_expandedMetadataTokens_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Every valid canonical block decodes to exactly its certified
complement-counter request. -/
@[simp] theorem parse_normalizedRequestBlock
    (request : Request) (valid : request.metadata.CursorValid) :
    parse? (normalizedRequestBlock request) =
      some
        { location := request.metadata.complementLocation
          color := request.metadata.color
          directions :=
            (PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
              request.normalization).directions } := by
  rw [normalizedRequestBlock_eq]
  unfold parse?
  rw [readUnits_replicate_periodEnd 0 request.metadata.period
    (List.replicate request.metadata.cursorHorizontal Token.unit ++
      (Token.horizontalEnd ::
        (List.replicate request.metadata.cursorVertical Token.unit ++
          (Token.verticalEnd :: Token.color request.metadata.color ::
            ((PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
              request.normalization).directions.map Token.direction ++
                [Token.routeEnd])))))]
  simp only [Nat.zero_add]
  rw [readUnits_replicate_horizontalEnd 0
    request.metadata.cursorHorizontal
    (List.replicate request.metadata.cursorVertical Token.unit ++
      (Token.verticalEnd :: Token.color request.metadata.color ::
        ((PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
          request.normalization).directions.map Token.direction ++
            [Token.routeEnd])))]
  simp only [Nat.zero_add]
  rw [readUnits_replicate_verticalEnd 0 request.metadata.cursorVertical
    (Token.color request.metadata.color ::
      ((PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
        request.normalization).directions.map Token.direction ++
          [Token.routeEnd]))]
  simp only [Nat.zero_add]
  unfold Metadata.CursorValid at valid
  rw [if_pos valid]
  rw [readDirections_map_routeEnd]
  rfl

/-- The pure parser target agrees with the previously certified complement
semantics on every canonical valid request. -/
@[simp] theorem output_normalizedRequestBlock
    (request : Request) (valid : request.metadata.CursorValid) :
    output (normalizedRequestBlock request) =
      complementRecordBlock request := by
  unfold output complementRecordBlock
  rw [parse_normalizedRequestBlock request valid]

end GadgetSparseRouteRecordTokens
end LeanTrominoes
