/- Kernel certificate for one directed-profile block. -/
import LeanTrominoes.FirstParentInheritedRouteCompilerCertificateData

namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem firstParentSelectorCheck_case15 :
    firstDirectedProfileCheck firstParentSelectorCheck ⟨true, true⟩ .east = true := by
  decide +kernel

end LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
