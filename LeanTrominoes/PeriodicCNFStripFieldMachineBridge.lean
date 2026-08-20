/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripFieldCompiler

/-! # Canonical-input bridge for native-field compiler machines -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

/-- A native-field machine need only agree with the semantic compiler on
canonical source field lists.  Its behavior on malformed lists is irrelevant
to the encoded many-one reduction. -/
def compiledTrominoStripPolyTimeOfFieldFunction
    (tromino : Tromino)
    (fieldFunction : List Nat → List Nat)
    (correct : ∀ source : PeriodicCNF Nat,
      fieldFunction (PeriodicCNFFlatEncoding.formulaFields source) =
        PeriodicStripFlatEncoding.stripFields
          (compiledTrominoStrip tromino source))
    (compiler :
      TM2ComputableInPolyTime PartrecToTM2.trList PartrecToTM2.trList
        fieldFunction) :
    TM2ComputableInPolyTime
      PeriodicCNFFlatEncoding.finEncoding.encode
      PeriodicStripFlatEncoding.finEncoding.encode
      (compiledTrominoStrip tromino) where
  tm := compiler.tm
  inputAlphabet := compiler.inputAlphabet
  outputAlphabet := compiler.outputAlphabet
  time := compiler.time
  outputsFun source := by
    rw [sourceFlatEncoding_eq_trList_formulaFields,
      targetFlatEncoding_eq_trList_stripFields, ← correct source]
    exact compiler.outputsFun
      (PeriodicCNFFlatEncoding.formulaFields source)

/-- Canonically correct native-field machines for both trominoes discharge
the exact encoded compiler-time obligation. -/
theorem compiledTrominoStripPolyTime_of_fieldFunctions
    (fieldFunction : Tromino → List Nat → List Nat)
    (correct : ∀ (tromino : Tromino) (source : PeriodicCNF Nat),
      fieldFunction tromino
          (PeriodicCNFFlatEncoding.formulaFields source) =
        PeriodicStripFlatEncoding.stripFields
          (compiledTrominoStrip tromino source))
    (compilers : ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime PartrecToTM2.trList PartrecToTM2.trList
          (fieldFunction tromino))) :
    ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime
          PeriodicCNFFlatEncoding.finEncoding.encode
          PeriodicStripFlatEncoding.finEncoding.encode
          (compiledTrominoStrip tromino)) := by
  intro tromino
  exact (compilers tromino).map
    (compiledTrominoStripPolyTimeOfFieldFunction tromino
      (fieldFunction tromino) (correct tromino))

end PeriodicCNFStripReduction
end LeanTrominoes
