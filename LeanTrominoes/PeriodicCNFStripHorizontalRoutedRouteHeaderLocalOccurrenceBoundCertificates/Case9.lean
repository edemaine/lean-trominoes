/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case9Second0
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case9Second1
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case9Second2
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case9Second3

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

theorem localOccurrenceBoundsCheck_case9 :
    firstDirectedProfileCheck localOccurrenceBoundsCheck ⟨false, true⟩ .invalid = true := by
  apply firstDirectedProfileCheck_of_second
  intro second
  rcases second with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value
  · exact localOccurrenceBoundsCheck_case9_second0
  · exact localOccurrenceBoundsCheck_case9_second1
  · exact localOccurrenceBoundsCheck_case9_second2
  · exact localOccurrenceBoundsCheck_case9_second3

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
