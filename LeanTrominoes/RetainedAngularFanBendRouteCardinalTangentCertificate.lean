/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanBendRouteCardinalTangentEastCertificate
import LeanTrominoes.RetainedAngularFanBendRouteCardinalTangentNorthCertificate
import LeanTrominoes.RetainedAngularFanBendRouteCardinalTangentSouthCertificate
import LeanTrominoes.RetainedAngularFanBendRouteCardinalTangentWestCertificate

/-! # Complete finite cardinal tangent certificate for bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- Every in-range route at a genuine ordered pair of distinct corner ports
has the cardinal tangent certificate selected by the finite orientation
table. -/
theorem bendRouteCardinalTangentCertificate_of_ne
    (firstPort secondPort : CornerPort)
    (different : firstPort ≠ secondPort)
    (localClauseIndex literalIndex : Nat)
    (clauseLt : localClauseIndex < 2)
    (literalLt : literalIndex < 2) :
    BendRouteCardinalTangentCertificate firstPort secondPort
      localClauseIndex literalIndex := by
  cases firstPort with
  | west =>
      exact bendRouteCardinalTangentCertificate_west secondPort
        different localClauseIndex literalIndex clauseLt literalLt
  | east =>
      exact bendRouteCardinalTangentCertificate_east secondPort
        different localClauseIndex literalIndex clauseLt literalLt
  | south =>
      exact bendRouteCardinalTangentCertificate_south secondPort
        different localClauseIndex literalIndex clauseLt literalLt
  | north =>
      exact bendRouteCardinalTangentCertificate_north secondPort
        different localClauseIndex literalIndex clauseLt literalLt

end PeriodicEightOccurrenceSplit
end LeanTrominoes
