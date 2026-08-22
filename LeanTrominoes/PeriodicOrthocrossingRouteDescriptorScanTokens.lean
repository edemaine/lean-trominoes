/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTokensData

/-! # Normalized finite tokens for route-descriptor scans -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorScanTokens

/-- Minimal alphabet consumed by later descriptor geometry machines. -/
inductive Token
  | recordStart
  | unit
  | fieldEnd
  deriving DecidableEq, Fintype, Inhabited

/-- One delimiter-terminated unary field. -/
def field (number : Nat) : List Token :=
  List.replicate number .unit ++ [.fieldEnd]

/-- Eleven unary fields in their descriptor order. -/
def fields (numbers : List Nat) : List Token :=
  numbers.flatMap field

/-- Canonical normalized encoding of one route descriptor. -/
def record (descriptor : RouteDescriptor) : List Token :=
  .recordStart :: fields descriptor.unaryFields

/-- Canonical normalized encoding of a descriptor list. -/
def encode (descriptors : List RouteDescriptor) : List Token :=
  descriptors.flatMap record

/-- Fixed block map erasing every source-token constructor that cannot occur
in counted route-descriptor fields. -/
def normalizeBlock : PeriodicCNF.UnaryProgramTokens.Token → List Token
  | .clauseMarker => [.recordStart]
  | .atomUnit => [.unit]
  | .atomEnd => [.fieldEnd]
  | _ => []

/-- Normalize an arbitrary unary-program token stream. -/
def normalize (tokens : List PeriodicCNF.UnaryProgramTokens.Token) :
    List Token :=
  tokens.flatMap normalizeBlock

end RouteDescriptorScanTokens
end PeriodicOrthocrossing
end LeanTrominoes
