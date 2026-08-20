/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripReductionPackaging

/-! # Raw flat-stream interface to the CNF-to-strip compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

/-- Parse a raw source-alphabet stream and emit the canonical flat encoding
of the compiled tromino strip.  Invalid streams have the harmless empty
fallback; the reduction machine is only required on canonical source
encodings. -/
def compiledTrominoStripFlatCompiler (tromino : Tromino) :
    List PeriodicCNFFlatEncoding.Symbol →
      List PeriodicStripFlatEncoding.Symbol :=
  fun symbols =>
    match PeriodicCNFFlatEncoding.finEncoding.decode symbols with
    | some source =>
        PeriodicStripFlatEncoding.finEncoding.encode
          (compiledTrominoStrip tromino source)
    | none => []

@[simp] theorem compiledTrominoStripFlatCompiler_encode
    (tromino : Tromino) (source : PeriodicCNF Nat) :
    compiledTrominoStripFlatCompiler tromino
        (PeriodicCNFFlatEncoding.finEncoding.encode source) =
      PeriodicStripFlatEncoding.finEncoding.encode
        (compiledTrominoStrip tromino source) := by
  simp [compiledTrominoStripFlatCompiler]

/-- Reinterpret a raw-stream polynomial-time machine as the encoded semantic
compiler required by the many-one reduction. -/
def compiledTrominoStripPolyTimeOfFlatCompiler
    (tromino : Tromino)
    (compiler :
      TM2ComputableInPolyTime id id
        (compiledTrominoStripFlatCompiler tromino)) :
    TM2ComputableInPolyTime
      PeriodicCNFFlatEncoding.finEncoding.encode
      PeriodicStripFlatEncoding.finEncoding.encode
      (compiledTrominoStrip tromino) where
  tm := compiler.tm
  inputAlphabet := compiler.inputAlphabet
  outputAlphabet := compiler.outputAlphabet
  time := compiler.time
  outputsFun source := by
    rw [← compiledTrominoStripFlatCompiler_encode tromino source]
    exact compiler.outputsFun
      (PeriodicCNFFlatEncoding.finEncoding.encode source)

/-- It is therefore enough to construct one raw flat-stream compiler machine
for each of the two fixed trominoes. -/
theorem compiledTrominoStripPolyTime_of_flatCompilers
    (compilers : ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime id id
          (compiledTrominoStripFlatCompiler tromino))) :
    ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime
          PeriodicCNFFlatEncoding.finEncoding.encode
          PeriodicStripFlatEncoding.finEncoding.encode
          (compiledTrominoStrip tromino)) := by
  intro tromino
  exact (compilers tromino).map
    (compiledTrominoStripPolyTimeOfFlatCompiler tromino)

/-- Raw-stream compiler machines, together with the established membership
result, discharge the complete strip half of Theorem 5.2. -/
theorem theorem52_stripStatement_of_flatCompilers
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (compilers : ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime id id
          (compiledTrominoStripFlatCompiler tromino))) :
    Theorem52.stripStatement :=
  theorem52_stripStatement_of_compiledTrominoStripPolyTime membership
    (compiledTrominoStripPolyTime_of_flatCompilers compilers)

end PeriodicCNFStripReduction
end LeanTrominoes
