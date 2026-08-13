/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecEvaluatorSpaceRefinement
import LeanTrominoes.PeriodicCNFFlatEncoding

/-!
# PSPACE certificates for evaluator-native flat field encodings

The earlier evaluator packaging accepted one `Primcodable` natural as input.
This module gives the same finite-machine construction a list of natural fields
directly.  Because `finEncodingOfFields` is exactly Mathlib's evaluator-native
`trList` representation, finite-evaluator correctness and the reachable-space
simulation apply without an encoding-conversion machine.
-/

noncomputable section

namespace Turing
namespace PartrecToTM2

open Computability
open Relation

/-- Package a total Boolean evaluator on flat natural fields as the explicit
finite-machine PSPACE certificate used by the project. -/
noncomputable def deciderInPolySpace_of_flatEvaluatorRunFits
    {α : Type} {language : α → Prop}
    (fields : α → List Nat) (decodeFields : List Nat → Option α)
    (decode_encode : ∀ input, decodeFields (fields input) = some input)
    (code : ToPartrec.Code) (result : α → Bool)
    (correct : ∀ input, result input = true ↔ language input)
    (evaluates : ∀ input,
      [Encodable.encode (result input)] ∈ code.eval (fields input))
    (space : Polynomial Nat)
    (fits : ∀ input,
      EvaluatorRunFits code (fields input)
        (space.eval
          ((LeanTrominoes.PeriodicCNFFlatEncoding.finEncodingOfFields
            fields decodeFields decode_encode).encode input).length)) :
    LeanTrominoes.Complexity.DeciderInPolySpace
      (LeanTrominoes.PeriodicCNFFlatEncoding.finEncodingOfFields
        fields decodeFields decode_encode)
      language := by
  let encoding :=
    LeanTrominoes.PeriodicCNFFlatEncoding.finEncodingOfFields
      fields decodeFields decode_encode
  refine
    { tm := finiteEvaluator code
      inputAlphabet := finiteEvaluatorInputAlphabet code
      outputAlphabet := finiteEvaluatorOutputAlphabet code
      stackAlphabetFinite := ?_
      result := result
      correct := correct
      outputs := ?_
      space := space
      space_le := ?_ }
  · intro stackIndex
    change Fintype Γ'
    infer_instance
  · intro input
    simp only [LeanTrominoes.PeriodicCNFFlatEncoding.finEncodingOfFields,
      map_finiteEvaluatorInputAlphabet_symm,
      map_finiteEvaluatorOutputAlphabet_symm,
      LeanTrominoes.PeriodicCNFFlatEncoding.encodeNatFields_eq_trList,
      LeanTrominoes.Complexity.primcodableFinEncoding]
    simpa only [finiteEvaluator, FinTM2.ofSupported] using
      finiteEvaluator_outputs (evaluates input)
  · intro input configuration reaches
    have ambientReaches := erase_finiteEvaluator_reaches code reaches
    have inputTape :
        List.map (finiteEvaluatorInputAlphabet code).invFun
            (encoding.encode input) =
          trList (fields input) := by
      simp [encoding,
        LeanTrominoes.PeriodicCNFFlatEncoding.finEncodingOfFields,
        LeanTrominoes.PeriodicCNFFlatEncoding.encodeNatFields_eq_trList]
      exact map_finiteEvaluatorInputAlphabet_symm code _
    have ambientFromInit :
        ReflTransGen (fun before after => after ∈ TM2.step tr before)
          (init code (fields input))
          (TM2.eraseRestrictedCfg configuration) := by
      have erasedInit :
          TM2.eraseRestrictedCfg
              (initList (finiteEvaluator code)
                (List.map (finiteEvaluatorInputAlphabet code).invFun
                  (encoding.encode input))) =
            init code (fields input) := by
        rw [inputTape]
        exact erase_finiteEvaluator_init _ _
      convert ambientReaches using 1
      exact erasedInit.symm
    letI : Fintype (finiteEvaluator code).K :=
      (finiteEvaluator code).kFin
    calc
      LeanTrominoes.Complexity.configurationSpace
          (finiteEvaluator code) configuration =
          TM2.stackSpace configuration := rfl
      _ = TM2.stackSpace (TM2.eraseRestrictedCfg configuration) :=
        (TM2.stackSpace_eraseRestrictedCfg configuration).symm
      _ ≤ space.eval (encoding.encode input).length :=
        evaluator_reachable_space_le code
          (fields input) [Encodable.encode (result input)]
          (space.eval (encoding.encode input).length)
          (fits input) (evaluates input) ambientFromInit

/-- Proposition-level PSPACE membership from a run-level evaluator certificate
on native flat fields. -/
theorem inPSPACE_of_flatEvaluatorRunFits
    {α : Type} {language : α → Prop}
    (fields : α → List Nat) (decodeFields : List Nat → Option α)
    (decode_encode : ∀ input, decodeFields (fields input) = some input)
    (code : ToPartrec.Code) (result : α → Bool)
    (correct : ∀ input, result input = true ↔ language input)
    (evaluates : ∀ input,
      [Encodable.encode (result input)] ∈ code.eval (fields input))
    (space : Polynomial Nat)
    (fits : ∀ input,
      EvaluatorRunFits code (fields input)
        (space.eval
          ((LeanTrominoes.PeriodicCNFFlatEncoding.finEncodingOfFields
            fields decodeFields decode_encode).encode input).length)) :
    LeanTrominoes.Complexity.InPSPACE
      (LeanTrominoes.PeriodicCNFFlatEncoding.finEncodingOfFields
        fields decodeFields decode_encode)
      language :=
  ⟨deciderInPolySpace_of_flatEvaluatorRunFits fields decodeFields
    decode_encode code result correct evaluates space fits⟩

end PartrecToTM2
end Turing
