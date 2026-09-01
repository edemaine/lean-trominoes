/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinData
import LeanTrominoes.FiniteIndexSlotUnaryDecoderCompiler

/-! # Delimited joining over an arbitrary finite alphabet -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetDelimitedBlockJoin

open LeanTrominoes

/-- A payload token or the end of its current block. -/
inductive Token (Alphabet : Type)
  | value (value : Alphabet)
  | blockEnd
  deriving DecidableEq, Fintype

instance {Alphabet : Type} : Inhabited (Token Alphabet) :=
  ⟨.blockEnd⟩

instance tokenCardNeZero {Alphabet : Type} [Fintype Alphabet] :
    NeZero (Fintype.card (Token Alphabet)) :=
  ⟨Fintype.card_ne_zero⟩

abbrev RoutedToken := DelimitedRouteJoin.Token
abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol

/-- Mixed-radix code reserving slot zero for one finite payload token. -/
def code {Alphabet : Type} [Fintype Alphabet]
    (token : Token Alphabet) : Nat :=
  8 * (Fintype.equivFin (Token Alphabet) token).val

/-- Interpret the two canonical unary symbols as harmless route directions. -/
def unaryDirection : UnarySymbol → AxisDirection
  | .unit => .east
  | .delimiter => .north

/-- Encode a payload token as a unary direction word. -/
def valueDirections {Alphabet : Type} [Fintype Alphabet]
    (value : Alphabet) : List AxisDirection :=
  (UnaryFieldEncoderMachine.unaryField (code (.value value))).map
    unaryDirection

/-- Encode one abstract token for the established delimited-route joiner.
Only the abstract block end becomes the joiner's physical route delimiter. -/
def encodedToken {Alphabet : Type} [Fintype Alphabet] :
    Token Alphabet → List RoutedToken
  | .value value =>
      (valueDirections value).map fun direction =>
        (.direction direction : RoutedToken)
  | .blockEnd => [.routeEnd]

def encoded {Alphabet : Type} [Fintype Alphabet]
    (tokens : List (Token Alphabet)) : List RoutedToken :=
  tokens.flatMap encodedToken

/-- Turn joined route directions back into unary fields.  The physical route
delimiter is expanded to the reserved code for the abstract block end. -/
def routeUnaryBlock {Alphabet : Type} [Fintype Alphabet] :
    RoutedToken → List UnarySymbol
  | .direction .east => [.unit]
  | .direction .north => [.delimiter]
  | .direction _ => []
  | .routeEnd =>
      UnaryFieldEncoderMachine.unaryField
        (code (Token.blockEnd : Token Alphabet))

def routeUnary {Alphabet : Type} [Fintype Alphabet]
    (tokens : List RoutedToken) : List UnarySymbol :=
  tokens.flatMap (routeUnaryBlock (Alphabet := Alphabet))

abbrev Pair (Alphabet : Type) [Fintype Alphabet] :=
  FiniteIndexSlotUnaryDecoder.Pair (Fintype.card (Token Alphabet))

/-- Decode the unary fields to finite indices. -/
def rawPairs {Alphabet : Type} [Fintype Alphabet]
    (tokens : List RoutedToken) : List (Pair Alphabet) :=
  FiniteStateTransducer.output
    (FiniteIndexSlotUnaryDecoder.zero (Fintype.card (Token Alphabet)))
    (FiniteIndexSlotUnaryDecoder.transition
      (count := Fintype.card (Token Alphabet)))
    (FiniteIndexSlotUnaryDecoder.finish
      (count := Fintype.card (Token Alphabet)))
    (routeUnary (Alphabet := Alphabet) tokens)

/-- Forget the reserved zero slot and recover the indexed abstract token. -/
def pairToken {Alphabet : Type} [Fintype Alphabet]
    (pair : Pair Alphabet) : Token Alphabet :=
  (Fintype.equivFin (Token Alphabet)).symm pair.1

def decoded {Alphabet : Type} [Fintype Alphabet]
    (tokens : List RoutedToken) : List (Token Alphabet) :=
  (rawPairs tokens).map pairToken

/-- Join corresponding abstract blocks by encoding them through the existing
verified delimited-route joiner and decoding its result. -/
def joined {Alphabet : Type} [Fintype Alphabet]
    (prefixes suffixes : List (Token Alphabet)) :
    List (Token Alphabet) :=
  decoded (DelimitedRouteJoin.joined
    (encoded prefixes) (encoded suffixes))

def block {Alphabet : Type} (body : List Alphabet) :
    List (Token Alphabet) :=
  body.map .value ++ [.blockEnd]

def blocks {Alphabet : Type} (bodies : List (List Alphabet)) :
    List (Token Alphabet) :=
  bodies.flatMap block

end LeanTrominoes.FiniteAlphabetDelimitedBlockJoin

end
