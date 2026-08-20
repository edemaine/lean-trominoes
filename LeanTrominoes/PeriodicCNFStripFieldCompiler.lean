/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripFlatCompiler

/-! # Natural-field interface to the CNF-to-strip compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

/-- Parse source natural fields and emit the target strip's natural fields.
Both lists use Mathlib's native delimiter-terminated `trList` encoding at the
machine boundary. -/
def compiledTrominoStripFieldCompiler (tromino : Tromino) :
    List Nat → List Nat :=
  fun fields =>
    match PeriodicCNFFlatEncoding.decodeFormulaFields fields with
    | some source =>
        PeriodicStripFlatEncoding.stripFields
          (compiledTrominoStrip tromino source)
    | none => []

@[simp] theorem compiledTrominoStripFieldCompiler_formulaFields
    (tromino : Tromino) (source : PeriodicCNF Nat) :
    compiledTrominoStripFieldCompiler tromino
        (PeriodicCNFFlatEncoding.formulaFields source) =
      PeriodicStripFlatEncoding.stripFields
        (compiledTrominoStrip tromino source) := by
  simp [compiledTrominoStripFieldCompiler]

theorem sourceFlatEncoding_eq_trList_formulaFields
    (source : PeriodicCNF Nat) :
    PeriodicCNFFlatEncoding.finEncoding.encode source =
      PartrecToTM2.trList
        (PeriodicCNFFlatEncoding.formulaFields source) := by
  exact PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _

theorem targetFlatEncoding_eq_trList_stripFields
    (strip : PeriodicStrip) :
    PeriodicStripFlatEncoding.finEncoding.encode strip =
      PartrecToTM2.trList
        (PeriodicStripFlatEncoding.stripFields strip) := by
  exact PeriodicCNFFlatEncoding.encodeNatFields_eq_trList _

/-- Reinterpret a polynomial-time native-field transformer as the exact
semantic compiler required by the reduction. -/
def compiledTrominoStripPolyTimeOfFieldCompiler
    (tromino : Tromino)
    (compiler :
      TM2ComputableInPolyTime PartrecToTM2.trList PartrecToTM2.trList
        (compiledTrominoStripFieldCompiler tromino)) :
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
      targetFlatEncoding_eq_trList_stripFields,
      ← compiledTrominoStripFieldCompiler_formulaFields]
    exact compiler.outputsFun
      (PeriodicCNFFlatEncoding.formulaFields source)

/-- It remains enough to construct a native-field transformer for each fixed
tromino. -/
theorem compiledTrominoStripPolyTime_of_fieldCompilers
    (compilers : ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime PartrecToTM2.trList PartrecToTM2.trList
          (compiledTrominoStripFieldCompiler tromino))) :
    ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime
          PeriodicCNFFlatEncoding.finEncoding.encode
          PeriodicStripFlatEncoding.finEncoding.encode
          (compiledTrominoStrip tromino)) := by
  intro tromino
  exact (compilers tromino).map
    (compiledTrominoStripPolyTimeOfFieldCompiler tromino)

/-- Native-field compiler machines, together with strip membership, discharge
the complete 1.5D statement. -/
theorem theorem52_stripStatement_of_fieldCompilers
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (compilers : ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime PartrecToTM2.trList PartrecToTM2.trList
          (compiledTrominoStripFieldCompiler tromino))) :
    Theorem52.stripStatement :=
  theorem52_stripStatement_of_compiledTrominoStripPolyTime membership
    (compiledTrominoStripPolyTime_of_fieldCompilers compilers)

end PeriodicCNFStripReduction
end LeanTrominoes
