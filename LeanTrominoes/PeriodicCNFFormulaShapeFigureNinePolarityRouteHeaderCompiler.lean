/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderData

/-! # Compiler for finite Figure 9 and polarity route headers -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FormulaShapeFigureNinePolarityRouteHeader

/-- A fixed block scan compiles every directed source clause to all final
polarity-operation/Figure-9-prefix headers. -/
noncomputable def sourceHeadersComputableInPolyTime :
    TM2ComputableInPolyTime id id sourceHeaders :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

end FormulaShapeFigureNinePolarityRouteHeader
end PeriodicCNF
end LeanTrominoes

end
