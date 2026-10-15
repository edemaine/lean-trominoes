/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificateData

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem sourcePrefixRoundtripCheck_case6_second2 :
    FormulaShapeDirectionOrdering.secondDirectedProfileCheck sourcePrefixRoundtripCheck
      ⟨false, true⟩ .north ⟨true, false⟩ = true := by
  decide +kernel

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
