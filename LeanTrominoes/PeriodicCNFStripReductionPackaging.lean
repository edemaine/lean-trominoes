/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetStripReduction
import LeanTrominoes.PeriodicCNFStripCompiledTrominoComputability

/-! # Packaging the concrete local-CNF strip reduction -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

/-- Once the exact compiled target function has its machine-level running-time
certificate, all geometric and semantic fields of the local-CNF strip
reduction are already discharged. -/
def localPeriodicCNF1DStripReductionOfPolyTime
    (polyTime : ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime
          PeriodicCNFFlatEncoding.finEncoding.encode
          PeriodicStripFlatEncoding.finEncoding.encode
          (compiledTrominoStrip tromino))) :
    Gadget.LocalPeriodicCNF1DStripReduction where
  drawing := compiledStripDrawing
  stripComputableInPolyTime tromino := by
    change Nonempty
      (TM2ComputableInPolyTime
        PeriodicCNFFlatEncoding.finEncoding.encode
        PeriodicStripFlatEncoding.finEncoding.encode
        (compiledTrominoStrip tromino))
    exact polyTime tromino
  wellFormed := compiledStripDrawing_isWellFormed
  verticesSeparated := compiledStripDrawing_verticesSeparated
  blankVerticalBoundary :=
    compiledStripDrawing_hasBlankVerticalBoundary
  correct := compiledStripDrawing_correct

/-- The full 1.5D statement now reduces to the one remaining machine-level
polynomial-time certificate for the concrete compiler. -/
theorem theorem52_stripStatement_of_compiledTrominoStripPolyTime
    (membership : ∀ tromino : Tromino,
      Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
        (PeriodicStripTrominoTiling tromino))
    (polyTime : ∀ tromino : Tromino,
      Nonempty
        (TM2ComputableInPolyTime
          PeriodicCNFFlatEncoding.finEncoding.encode
          PeriodicStripFlatEncoding.finEncoding.encode
          (compiledTrominoStrip tromino))) :
    Theorem52.stripStatement :=
  Gadget.theorem52_stripStatement_of_localPeriodicCNFReduction
    membership
    (localPeriodicCNF1DStripReductionOfPolyTime polyTime)

end PeriodicCNFStripReduction
end LeanTrominoes
