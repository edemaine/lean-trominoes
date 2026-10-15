/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceNormalizedTailData

/-! # Compiler for complete normalized direct-source tails -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

local instance : Inhabited AxisDirection := ⟨.invalid⟩

/-- Elementwise expansion of finite direct-atlas queries into their exact
normalized source-tail words is polynomial-time. -/
noncomputable def retainedDirectSourceNormalizedTailsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun queries : List RetainedDirectSourceNormalizedTailQuery =>
        queries.flatMap retainedDirectSourceNormalizedTailOfQuery) :=
  FiniteBlockTransducer.computableInPolyTime
    retainedDirectSourceNormalizedTailOfQuery

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
