/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case12Second0
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case12Second1
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case12Second2
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case12Second3

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeDirectionOrdering

theorem sourcePrefixRoundtripCheck_case12 :
    firstDirectedProfileCheck sourcePrefixRoundtripCheck ⟨true, false⟩ .west = true := by
  apply firstDirectedProfileCheck_of_second
  intro second
  rcases second with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value
  · exact sourcePrefixRoundtripCheck_case12_second0
  · exact sourcePrefixRoundtripCheck_case12_second1
  · exact sourcePrefixRoundtripCheck_case12_second2
  · exact sourcePrefixRoundtripCheck_case12_second3

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
