/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case18Second0
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case18Second1
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case18Second2
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case18Second3

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

theorem localOccurrenceBoundsCheck_case18 :
    firstDirectedProfileCheck localOccurrenceBoundsCheck ⟨true, true⟩ .south = true := by
  apply firstDirectedProfileCheck_of_second
  intro second
  rcases second with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value
  · exact localOccurrenceBoundsCheck_case18_second0
  · exact localOccurrenceBoundsCheck_case18_second1
  · exact localOccurrenceBoundsCheck_case18_second2
  · exact localOccurrenceBoundsCheck_case18_second3

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderPresentationAtomScope
