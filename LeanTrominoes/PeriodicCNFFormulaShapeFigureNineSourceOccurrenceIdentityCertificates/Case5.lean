/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case5Second0
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case5Second1
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case5Second2
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case5Second3

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeDirectionOrdering

theorem sourcePrefixRoundtripCheck_case5 :
    firstDirectedProfileCheck sourcePrefixRoundtripCheck ⟨false, true⟩ .east = true := by
  apply firstDirectedProfileCheck_of_second
  intro second
  rcases second with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value
  · exact sourcePrefixRoundtripCheck_case5_second0
  · exact sourcePrefixRoundtripCheck_case5_second1
  · exact sourcePrefixRoundtripCheck_case5_second2
  · exact sourcePrefixRoundtripCheck_case5_second3

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
