/- Kernel certificate for one directed-profile block. -/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedClauseDegreePatternCertificateData

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderClauseFrame
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem routedClauseDegreeCheck_case13 :
    firstDirectedProfileCheck routedClauseDegreeCheck ⟨true, false⟩ .south = true := by
  decide +kernel

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeaderClauseFrame
