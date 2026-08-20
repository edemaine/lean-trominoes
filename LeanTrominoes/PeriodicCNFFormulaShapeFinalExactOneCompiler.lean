/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFFormulaShapeFinalExactOneData

/-! # Polynomial-time final exact-one formula shapes -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FormulaShapeFinalExactOne

noncomputable def shapeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List FormulaShape.Token) (List FormulaShape.Token)
      FormulaShape.Token FormulaShape.Token id id shape :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

end FormulaShapeFinalExactOne
end PeriodicCNF
end LeanTrominoes
