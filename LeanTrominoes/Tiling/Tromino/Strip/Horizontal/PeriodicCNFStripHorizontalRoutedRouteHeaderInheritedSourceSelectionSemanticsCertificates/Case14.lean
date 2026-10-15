/- Kernel certificate for one directed-profile block. -/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderInheritedSourceSelectionSemanticsCertificateData

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderInheritedSourceSelection
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem inheritedSourceSelectionCheck_case14 :
    firstDirectedProfileCheck inheritedSourceSelectionCheck ⟨true, false⟩ .invalid = true := by
  decide +kernel

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderInheritedSourceSelection
