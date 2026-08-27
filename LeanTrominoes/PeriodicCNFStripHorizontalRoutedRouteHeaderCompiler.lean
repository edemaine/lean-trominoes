/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderData

/-! # Compiler for horizontal routed-request headers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeader

open Computability Turing
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader

/-- Every finite routed header expands to its compact request prefix by a
fixed block transducer. -/
noncomputable def streamComputableInPolyTime :
    TM2ComputableInPolyTime id id stream :=
  FiniteBlockTransducer.computableInPolyTime tokens

end HorizontalRoutedRouteHeader
end PeriodicCNFStripReduction
end LeanTrominoes

end
