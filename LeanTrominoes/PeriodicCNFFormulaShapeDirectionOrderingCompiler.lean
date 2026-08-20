/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData

/-! # Polynomial-time finite direction-aware shape ordering -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

/-- Sorting a width-three direction-annotated profile is a fixed finite
lookup, so the complete annotated shape is a finite block transduction. -/
noncomputable def shapeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List Token) (List FormulaShape.Token)
      Token FormulaShape.Token id id shape :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes

