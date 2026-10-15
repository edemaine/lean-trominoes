/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case7Second0
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case7Second1
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case7Second2
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case7Second3

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

theorem localOccurrenceBoundsCheck_case7 :
    firstDirectedProfileCheck localOccurrenceBoundsCheck ⟨false, true⟩ .west = true := by
  apply firstDirectedProfileCheck_of_second
  intro second
  rcases second with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value
  · exact localOccurrenceBoundsCheck_case7_second0
  · exact localOccurrenceBoundsCheck_case7_second1
  · exact localOccurrenceBoundsCheck_case7_second2
  · exact localOccurrenceBoundsCheck_case7_second3

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
