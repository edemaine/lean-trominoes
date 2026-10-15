/- Kernel certificate for one directed-profile block. -/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderFinalClauseParentIndexCompilerCertificateData

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderFinalClauseParentIndex
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem finalClauseParentMarkersCheck_case14 :
    firstDirectedProfileCheck finalClauseParentMarkersCheck ⟨true, false⟩ .invalid = true := by
  decide +kernel

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderFinalClauseParentIndex
