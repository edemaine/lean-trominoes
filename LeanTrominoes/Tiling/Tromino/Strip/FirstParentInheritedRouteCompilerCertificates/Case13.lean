/- Kernel certificate for one directed-profile block. -/
import LeanTrominoes.Tiling.Tromino.Strip.FirstParentInheritedRouteCompilerCertificateData

namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem firstParentSelectorCheck_case13 :
    firstDirectedProfileCheck firstParentSelectorCheck ⟨true, false⟩ .south = true := by
  decide +kernel

end LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
