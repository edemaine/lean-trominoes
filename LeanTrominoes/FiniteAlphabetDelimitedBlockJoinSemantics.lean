/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinSemantics
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinData

/-! # Semantics of finite-alphabet delimited joining -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetDelimitedBlockJoin

open LeanTrominoes

variable {Alphabet : Type} [Fintype Alphabet]

@[simp] theorem routeUnaryBlock_direction_unaryDirection
    (symbol : UnarySymbol) :
    routeUnaryBlock (Alphabet := Alphabet)
        (.direction (unaryDirection symbol) : RoutedToken) = [symbol] := by
  cases symbol <;> rfl

@[simp] theorem routeUnary_map_unaryDirection
    (symbols : List UnarySymbol) :
    routeUnary (Alphabet := Alphabet)
        (symbols.map fun symbol =>
          (.direction (unaryDirection symbol) : RoutedToken)) =
      symbols := by
  unfold routeUnary
  rw [List.flatMap_map]
  simp only [routeUnaryBlock_direction_unaryDirection]
  rw [← List.map_eq_flatMap]
  exact List.map_id symbols

@[simp] theorem routeUnary_encodedToken (token : Token Alphabet) :
    routeUnary (Alphabet := Alphabet)
        (encodedToken (Alphabet := Alphabet) token) =
      UnaryFieldEncoderMachine.unaryField
        (code (Alphabet := Alphabet) token) := by
  cases token with
  | value value =>
      simp only [encodedToken, valueDirections]
      rw [List.map_map]
      exact routeUnary_map_unaryDirection (Alphabet := Alphabet)
        (UnaryFieldEncoderMachine.unaryField
          (code (Token.value value : Token Alphabet)))
  | blockEnd =>
      simp [encodedToken, routeUnary, routeUnaryBlock]

@[simp] theorem routeUnary_append
    (first second : List RoutedToken) :
    routeUnary (Alphabet := Alphabet) (first ++ second) =
      routeUnary (Alphabet := Alphabet) first ++
        routeUnary (Alphabet := Alphabet) second := by
  simp [routeUnary]

@[simp] theorem routeUnary_encoded (tokens : List (Token Alphabet)) :
    routeUnary (Alphabet := Alphabet)
        (encoded (Alphabet := Alphabet) tokens) =
      UnaryFieldEncoderMachine.unaryFields
        (tokens.map (code (Alphabet := Alphabet))) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      rw [show encoded (Alphabet := Alphabet) (token :: tokens) =
          encodedToken (Alphabet := Alphabet) token ++
            encoded (Alphabet := Alphabet) tokens by rfl,
        routeUnary_append, routeUnary_encodedToken, induction,
        List.map_cons,
        UnaryFieldEncoderMachine.unaryFields_cons]

@[simp] theorem rawPairs_encoded (tokens : List (Token Alphabet)) :
    rawPairs (Alphabet := Alphabet)
        (encoded (Alphabet := Alphabet) tokens) =
      FiniteIndexSlotUnaryDecoder.pairs
        (Fintype.card (Token Alphabet))
        (tokens.map (code (Alphabet := Alphabet))) := by
  unfold rawPairs
  rw [routeUnary_encoded,
    FiniteIndexSlotUnaryDecoder.output_unaryFields]

@[simp] theorem pairToken_boundedCode (token : Token Alphabet) :
    pairToken (Alphabet := Alphabet)
        (FiniteIndexSlotUnaryDecoder.boundedCode
          (Fintype.card (Token Alphabet))
          (code (Alphabet := Alphabet) token)) =
      token := by
  let index := Fintype.equivFin (Token Alphabet) token
  have decoded :=
    FiniteIndexSlotUnaryDecoder.boundedCode_index_slot
      index (0 : Fin 8)
  change pairToken (Alphabet := Alphabet)
      (FiniteIndexSlotUnaryDecoder.boundedCode
        (Fintype.card (Token Alphabet))
        (8 * index.val + (0 : Fin 8).val)) = token
  rw [decoded]
  exact (Fintype.equivFin (Token Alphabet)).symm_apply_apply token

/-- The finite unary codec is an exact left inverse on every abstract token
stream, including its block delimiters. -/
@[simp] theorem decoded_encoded (tokens : List (Token Alphabet)) :
    decoded (Alphabet := Alphabet)
        (encoded (Alphabet := Alphabet) tokens) = tokens := by
  unfold decoded
  rw [rawPairs_encoded]
  unfold FiniteIndexSlotUnaryDecoder.pairs
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp only [List.map_cons]
      rw [pairToken_boundedCode]
      exact congrArg (List.cons token) induction

@[simp] theorem encoded_append
    (first second : List (Token Alphabet)) :
    encoded (Alphabet := Alphabet) (first ++ second) =
      encoded (Alphabet := Alphabet) first ++
        encoded (Alphabet := Alphabet) second := by
  simp [encoded]

@[simp] theorem encoded_block (body : List Alphabet) :
    encoded (Alphabet := Alphabet) (block body) =
      DelimitedRouteJoin.delimited
        (body.flatMap (valueDirections (Alphabet := Alphabet))) := by
  induction body with
  | nil => rfl
  | cons value body induction =>
      rw [show block (value :: body) =
          [.value value] ++ block body by rfl,
        encoded_append, induction]
      simp [encoded, encodedToken, DelimitedRouteJoin.delimited,
        List.map_append, List.append_assoc]

@[simp] theorem encoded_blocks (bodies : List (List Alphabet)) :
    encoded (Alphabet := Alphabet) (blocks bodies) =
      bodies.flatMap fun body =>
        DelimitedRouteJoin.delimited
          (body.flatMap (valueDirections (Alphabet := Alphabet))) := by
  induction bodies with
  | nil => rfl
  | cons body bodies induction =>
      rw [show blocks (body :: bodies) = block body ++ blocks bodies by rfl,
        encoded_append, encoded_block, induction]
      rfl

/-- Corresponding complete blocks are concatenated pointwise.  Presenting
the alignment as a list of pairs makes equal block counts explicit. -/
@[simp] theorem joined_pairedBlocks
    (pairs : List (List Alphabet × List Alphabet)) :
    joined
        (blocks (pairs.map Prod.fst))
        (blocks (pairs.map Prod.snd)) =
      blocks (pairs.map fun pair => pair.1 ++ pair.2) := by
  have encodedJoin :
      DelimitedRouteJoin.joined
          (encoded (Alphabet := Alphabet)
            (blocks (pairs.map Prod.fst)))
          (encoded (Alphabet := Alphabet)
            (blocks (pairs.map Prod.snd))) =
        encoded (Alphabet := Alphabet)
          (blocks (pairs.map fun pair => pair.1 ++ pair.2)) := by
    rw [encoded_blocks, encoded_blocks, encoded_blocks]
    simpa only [List.flatMap_map, List.flatMap_append] using
      DelimitedRouteJoin.joined_flatMap_delimited
        (pairs.map fun pair =>
          (pair.1.flatMap (valueDirections (Alphabet := Alphabet)),
            pair.2.flatMap (valueDirections (Alphabet := Alphabet))))
  unfold joined
  rw [encodedJoin, decoded_encoded]

/-- Corresponding complete blocks can equivalently be presented as two
aligned body lists and joined pointwise with `List.zipWith`. -/
@[simp] theorem joined_blocks_zipWith
    (firsts seconds : List (List Alphabet))
    (aligned : firsts.length = seconds.length) :
    joined (blocks firsts) (blocks seconds) =
      blocks (List.zipWith (fun first second => first ++ second)
        firsts seconds) := by
  let pairs := firsts.zip seconds
  have firstProjection : pairs.map Prod.fst = firsts := by
    exact List.map_fst_zip (by omega)
  have secondProjection : pairs.map Prod.snd = seconds := by
    exact List.map_snd_zip (by omega)
  have combined :
      pairs.map (fun pair => pair.1 ++ pair.2) =
        List.zipWith (fun first second => first ++ second)
          firsts seconds := by
    unfold pairs
    rw [show
      (fun pair : List Alphabet × List Alphabet => pair.1 ++ pair.2) =
        Function.uncurry
          (fun first second : List Alphabet => first ++ second) by
      funext pair
      cases pair
      rfl]
    exact List.map_uncurry_zip_eq_zipWith
  have joinedPairs := joined_pairedBlocks (Alphabet := Alphabet) pairs
  rw [firstProjection, secondProjection, combined] at joinedPairs
  exact joinedPairs

end LeanTrominoes.FiniteAlphabetDelimitedBlockJoin

end
