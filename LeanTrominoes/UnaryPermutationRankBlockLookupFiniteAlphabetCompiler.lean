/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetCase
import LeanTrominoes.TM2SubsingletonInputCompiler
import LeanTrominoes.UnaryPermutationRankBlockLookupCompiler

/-! # Fixed-width permutation-rank lookup over any finite alphabet -/

noncomputable section

namespace LeanTrominoes
namespace UnaryPermutationRankBlockLookup

open Computability Turing

private noncomputable abbrev listSubsingletonOfIsEmpty
    {Symbol : Type} (empty : IsEmpty Symbol) :
    Subsingleton (List Symbol) :=
  ⟨fun first second => by
    cases first with
    | nil =>
        cases second with
        | nil => rfl
        | cons symbol tail => exact (empty.false symbol).elim
    | cons symbol tail => exact (empty.false symbol).elim⟩

/-- Fixed-width permutation-rank lookup is polynomial-time computable on
lists over every finite alphabet.  For a nonempty alphabet this is the usual
lookup compiler; for an empty alphabet the list input type is subsingleton. -/
noncomputable def valuesComputableInPolyTimeOnSymbolLists
    {InputSymbol : Type} [Fintype InputSymbol]
    (width : Nat)
    (ranks fieldValues : List InputSymbol → List Nat)
    (aligned : ∀ source,
      (fieldValues source).length = (ranks source).length * width)
    (rankCompiler : TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields ranks)
    (fieldCompiler : TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields fieldValues) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => values width (ranks source) (fieldValues source)) :=
  FiniteAlphabetCase.choose
    (Result :=
      TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
        (fun source => values width (ranks source) (fieldValues source)))
    (fun empty =>
      letI : IsEmpty InputSymbol := empty
      letI : Subsingleton (List InputSymbol) :=
        listSubsingletonOfIsEmpty empty
      TM2SubsingletonInputCompiler.computableInPolyTime id
        UnaryFieldEncoderMachine.unaryFields
        (fun source => values width (ranks source) (fieldValues source)))
    (fun nonempty =>
      letI : Inhabited InputSymbol := ⟨Classical.choice nonempty⟩
      valuesComputableInPolyTime id width ranks fieldValues aligned
        rankCompiler fieldCompiler)

end UnaryPermutationRankBlockLookup
end LeanTrominoes

end
