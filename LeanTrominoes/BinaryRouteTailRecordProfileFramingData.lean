/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterData
import LeanTrominoes.DelimitedRouteJoinSemantics
import LeanTrominoes.FiniteRoleSlotUnaryDecoderData
import LeanTrominoes.FiniteStateTransducerSemantics

/-! # Profile framing for aligned four-route streams -/

noncomputable section

namespace LeanTrominoes
namespace BinaryRouteTailRecordProfileFraming

open PeriodicThreeDM.NormalizationDirectionRequest.Batch

abbrev Profile := BinaryRouteTailRecordBatchFormatter.Profile
abbrev RouteToken := NormalizedToken
abbrev Token := BinaryRouteTailRecordBatchFormatter.Token
abbrev CodeControl := FiniteRoleSlotUnaryDecoder.Control Profile

/-- A profile is represented by a bounded unary code.  Multiplication by
eight leaves the slot component of the generic finite decoder at zero. -/
def profileCode (profile : Profile) : Nat :=
  8 * (Fintype.equivFin Profile profile).val

def profileCodeDirections (profile : Profile) : List AxisDirection :=
  List.replicate (profileCode profile) .north

/-- Two profile codes, each terminated by `south`, occupy the prefix of the
first route in one four-route block. -/
def profilePairDirections (first second : Profile) : List AxisDirection :=
  profileCodeDirections first ++ [.south] ++
    profileCodeDirections second ++ [.south]

abbrev delimited := DelimitedRouteJoin.delimited

/-- Four delimited prefix words for a profile pair: the codes occur in the
first word and the remaining three prefixes are empty. -/
def profilePairPrefixBlock (first second : Profile) : List RouteToken :=
  delimited (profilePairDirections first second) ++
    [.routeEnd, .routeEnd, .routeEnd]

/-- Pair consecutive profiles and produce four aligned prefix words per
pair.  An unmatched final profile is deliberately ignored. -/
def profilePrefixes : List Profile → List RouteToken
  | first :: second :: profiles =>
      profilePairPrefixBlock first second ++ profilePrefixes profiles
  | _ => []

inductive PrefixControl
  | empty
  | first (profile : Profile)
  deriving DecidableEq, Fintype, Inhabited

def prefixTransition : PrefixControl → Profile →
    PrefixControl × List RouteToken
  | .empty, profile => (.first profile, [])
  | .first first, second =>
      (.empty, profilePairPrefixBlock first second)

def prefixFinish (_ : PrefixControl) : List RouteToken := []

def prefixOutput (profiles : List Profile) : List RouteToken :=
  FiniteStateTransducer.output .empty
    prefixTransition prefixFinish profiles

inductive DecodeControl
  | firstCode (code : CodeControl)
  | secondCode (code : CodeControl)
  | firstRoute
  | secondRoute
  | thirdRoute
  | fourthRoute
  deriving DecidableEq, Fintype

instance : Inhabited DecodeControl :=
  ⟨.firstCode (FiniteRoleSlotUnaryDecoder.zero)⟩

def decodeInitial : DecodeControl :=
  .firstCode FiniteRoleSlotUnaryDecoder.zero

def decodedProfile (code : CodeControl) : Profile :=
  (FiniteRoleSlotUnaryDecoder.decode code).1

/-- Decode the bounded profile prefix, then pass the four complete route
words through under the batch formatter's `source` constructor. -/
def decodeTransition : DecodeControl → RouteToken →
    DecodeControl × List Token
  | .firstCode code, .direction .north =>
      (.firstCode (FiniteRoleSlotUnaryDecoder.increment code), [])
  | .firstCode code, .direction .south =>
      (.secondCode FiniteRoleSlotUnaryDecoder.zero,
        [.firstProfile (decodedProfile code)])
  | .firstCode code, .direction _ => (.firstCode code, [])
  | .firstCode _, .routeEnd => (decodeInitial, [])
  | .secondCode code, .direction .north =>
      (.secondCode (FiniteRoleSlotUnaryDecoder.increment code), [])
  | .secondCode code, .direction .south =>
      (.firstRoute, [.secondProfile (decodedProfile code)])
  | .secondCode code, .direction _ => (.secondCode code, [])
  | .secondCode _, .routeEnd => (decodeInitial, [])
  | .firstRoute, token =>
      match token with
      | .routeEnd => (.secondRoute, [.source .routeEnd])
      | _ => (.firstRoute, [.source token])
  | .secondRoute, token =>
      match token with
      | .routeEnd => (.thirdRoute, [.source .routeEnd])
      | _ => (.secondRoute, [.source token])
  | .thirdRoute, token =>
      match token with
      | .routeEnd => (.fourthRoute, [.source .routeEnd])
      | _ => (.thirdRoute, [.source token])
  | .fourthRoute, token =>
      match token with
      | .routeEnd => (decodeInitial, [.source .routeEnd])
      | _ => (.fourthRoute, [.source token])

def decodeFinish (_ : DecodeControl) : List Token := []

def decodeOutput (input : List RouteToken) : List Token :=
  FiniteStateTransducer.output decodeInitial
    decodeTransition decodeFinish input

/-- Profile pairs and aligned complete routes are combined into the exact
input alphabet of the batched binary route-tail record formatter. -/
def framed (profiles : List Profile) (routes : List RouteToken) :
    List Token :=
  decodeOutput
    (DelimitedRouteJoin.joined (prefixOutput profiles) routes)

/-- The two clause profiles of every semantic binary record block. -/
def blockProfiles
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    List Profile :=
  blocks.flatMap fun block => [block.firstProfile, block.secondProfile]

/-- The four complete route words of every semantic binary record block. -/
def blockRoutes
    (blocks : List BinaryRouteTailRecordBatchFormatter.Block) :
    List RouteToken :=
  blocks.flatMap fun block =>
    delimited block.first ++ delimited block.second ++
      delimited block.third ++ delimited block.fourth

end BinaryRouteTailRecordProfileFraming
end LeanTrominoes

end
