/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixData

/-! # Compiler for finite Figure 9 route-prefix descriptors -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

/-- A fixed block scan expands every directed clause profile to all of its
finite local or inherited-prefix queries. -/
noncomputable def descriptorsComputableInPolyTime :
    TM2ComputableInPolyTime id id descriptors :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes

end
