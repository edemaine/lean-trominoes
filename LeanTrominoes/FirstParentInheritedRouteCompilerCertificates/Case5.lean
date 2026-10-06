/- Kernel certificate for one directed-profile block. -/
import LeanTrominoes.FirstParentInheritedRouteCompilerCertificateData

namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem firstParentSelectorCheck_case5 :
    firstDirectedProfileCheck firstParentSelectorCheck ⟨false, true⟩ .east = true := by
  decide +kernel

end LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
