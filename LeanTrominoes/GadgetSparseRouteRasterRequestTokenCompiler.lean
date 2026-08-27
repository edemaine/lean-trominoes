/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.GadgetSparseRouteRasterRequestTokens
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for compact raster route request expansion -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseRouteRasterRequestTokens

open Computability Turing

noncomputable def firstComputableInPolyTime :
    TM2ComputableInPolyTime id id firstExpand :=
  FiniteBlockTransducer.computableInPolyTime firstBlock

noncomputable def secondComputableInPolyTime :
    TM2ComputableInPolyTime id id secondExpand :=
  FiniteBlockTransducer.computableInPolyTime secondBlock

noncomputable def thirdComputableInPolyTime :
    TM2ComputableInPolyTime id id thirdExpand :=
  FiniteBlockTransducer.computableInPolyTime thirdBlock

/-- Fixed affine request expansion is polynomial-time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id expand := by
  let firstTwo := TM2CompositionMachine.computableInPolyTime
    firstComputableInPolyTime secondComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime
    firstTwo thirdComputableInPolyTime
  exact complete

end GadgetSparseRouteRasterRequestTokens
end LeanTrominoes

end
