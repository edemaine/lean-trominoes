/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCompiledTromino
import LeanTrominoes.PeriodicCNFStripNormalizationPeriodSize
import LeanTrominoes.PeriodicThreeDMNormalizationStripFlatEncodingMonotone

/-!
# Flat output size of the concrete tromino-strip compiler
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Explicit flat-output budget as a function of source flat length. -/
def compiledTrominoStripFlatEncodingBudget
    (sourceFlatLength : Nat) : Nat :=
  PeriodicThreeDM.NormalizationCompiler.stripFlatEncodingBudget
    (normalizationPeriodBudget sourceFlatLength)

/-- The concrete target's complete flat binary representation has the
explicit source-length bound above, for either tromino. -/
theorem compiledTrominoStrip_flatEncoding_length_le
    (tromino : Tromino) (source : PeriodicCNF Nat) :
    (PeriodicStripFlatEncoding.finEncoding.encode
      (compiledTrominoStrip tromino source)).length ≤
        compiledTrominoStripFlatEncodingBudget
          (PeriodicCNFFlatEncoding.finEncoding.encode source).length := by
  have target :=
    PeriodicThreeDM.NormalizationCompiler.compileStrip_periodicStrip_flatEncoding_length_le
      tromino (normalizationInput source)
  have period := normalizationInput_finalNormalizationPeriod_le_flatLength source
  exact target.trans
    (PeriodicThreeDM.NormalizationCompiler.stripFlatEncodingBudget_monotone
      period)

end PeriodicCNFStripReduction
end LeanTrominoes
