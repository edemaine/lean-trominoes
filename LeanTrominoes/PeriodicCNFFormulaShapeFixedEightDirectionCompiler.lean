/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionData

/-! # Polynomial-time fixed-eight direction descriptors -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FormulaShapeFixedEightDirection

/-- The one-pass fixed-eight descriptor expansion is a fixed finite block
transduction. -/
noncomputable def streamDescriptorsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List FormulaShapeDirectionOrdering.Token)
      (List FormulaShapeDirectionOrdering.Token)
      FormulaShapeDirectionOrdering.Token
      FormulaShapeDirectionOrdering.Token
      id id streamDescriptors :=
  FiniteBlockTransducer.computableInPolyTime streamBlock

end FormulaShapeFixedEightDirection
end PeriodicCNF
end LeanTrominoes
