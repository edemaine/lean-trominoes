/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case6Second0
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case6Second1
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case6Second2
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case6Second3

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

theorem localOccurrenceBoundsCheck_case6 :
    firstDirectedProfileCheck localOccurrenceBoundsCheck ⟨false, true⟩ .north = true := by
  apply firstDirectedProfileCheck_of_second
  intro second
  rcases second with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value
  · exact localOccurrenceBoundsCheck_case6_second0
  · exact localOccurrenceBoundsCheck_case6_second1
  · exact localOccurrenceBoundsCheck_case6_second2
  · exact localOccurrenceBoundsCheck_case6_second3

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
