/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanBendRouteCardinalTangentData

/-! # Cardinal tangent certificates for west-first bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- Every genuine west-first entry of the finite corner table has the
advertised cardinal tangent geometry. -/
theorem bendRouteCardinalTangentCertificate_west
    (secondPort : CornerPort)
    (different : CornerPort.west ≠ secondPort)
    (localClauseIndex literalIndex : Nat)
    (clauseLt : localClauseIndex < 2)
    (literalLt : literalIndex < 2) :
    BendRouteCardinalTangentCertificate .west secondPort
      localClauseIndex literalIndex := by
  cases secondPort with
  | west => exact (different rfl).elim
  | east =>
      interval_cases localClauseIndex <;>
        interval_cases literalIndex <;>
        constructor <;> native_decide
  | south =>
      interval_cases localClauseIndex <;>
        interval_cases literalIndex <;>
        constructor <;> native_decide
  | north =>
      interval_cases localClauseIndex <;>
        interval_cases literalIndex <;>
        constructor <;> native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
