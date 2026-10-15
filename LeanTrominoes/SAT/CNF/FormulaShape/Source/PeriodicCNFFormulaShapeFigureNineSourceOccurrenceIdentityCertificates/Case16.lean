/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case16Second0
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case16Second1
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case16Second2
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case16Second3

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeDirectionOrdering

theorem sourcePrefixRoundtripCheck_case16 :
    firstDirectedProfileCheck sourcePrefixRoundtripCheck ⟨true, true⟩ .north = true := by
  apply firstDirectedProfileCheck_of_second
  intro second
  rcases second with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value
  · exact sourcePrefixRoundtripCheck_case16_second0
  · exact sourcePrefixRoundtripCheck_case16_second1
  · exact sourcePrefixRoundtripCheck_case16_second2
  · exact sourcePrefixRoundtripCheck_case16_second3

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
