/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryAlignedAddTime
import LeanTrominoes.UnaryAlignedAddValidity
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Pointwise addition of compiled unary columns on native list inputs -/

noncomputable section

namespace LeanTrominoes.UnaryAlignedAddMachine

open Turing

/-- Compose two aligned column compilers with unary addition, including when
there are no input symbols. -/
noncomputable def nativeListComputableInPolyTime {Symbol : Type} [Fintype Symbol]
    (firsts seconds : List Symbol → List Nat)
    (aligned : ∀ symbols, (firsts symbols).length = (seconds symbols).length)
    (firstCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields firsts)
    (secondCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields seconds) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => sums (firsts symbols) (seconds symbols)) := by
  classical
  exact if nonemptyAlphabet : Nonempty Symbol then by
    letI : Inhabited Symbol := ⟨Classical.choice nonemptyAlphabet⟩
    let input : List Symbol → Input := fun symbols =>
      ⟨firsts symbols, seconds symbols, Valid.of_length_eq (aligned symbols)⟩
    let paired := TM2ForkMachine.computableInPolyTime firstCompiler secondCompiler
    let prepared : TM2ComputableInPolyTime id encode input :=
      TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired (fun _ => rfl)
    let added := TM2CompositionMachine.computableInPolyTime prepared computableInPolyTime
    exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq added (fun _ => rfl)
  else by
    letI : IsEmpty Symbol := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

/-- Two columns mapped over one index list add in that same order. -/
theorem sums_map {Index : Type} (indices : List Index) (first second : Index → Nat) :
    sums (indices.map first) (indices.map second) =
      indices.map (fun index => first index + second index) := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.map_cons, sums, induction]

end LeanTrominoes.UnaryAlignedAddMachine

end
