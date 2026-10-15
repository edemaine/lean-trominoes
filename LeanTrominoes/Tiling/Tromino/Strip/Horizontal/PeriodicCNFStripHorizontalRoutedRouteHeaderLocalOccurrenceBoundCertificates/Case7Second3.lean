/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificateData
import LeanTrominoes.SAT.Planar.DirectedClauseProfileSecondLiteralCheck

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem localOccurrenceBoundsCheck_case7_second3 :
    secondDirectedProfileCheck localOccurrenceBoundsCheck
      ⟨false, true⟩ .west ⟨true, true⟩ = true := by
  decide +kernel

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
