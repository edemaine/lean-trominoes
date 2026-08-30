/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanBendRouteCardinalTangentData

/-! # Cardinal tangent certificates for east-first bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- Every genuine east-first entry of the finite corner table has the
advertised cardinal tangent geometry. -/
theorem bendRouteCardinalTangentCertificate_east
    (secondPort : CornerPort)
    (different : CornerPort.east ≠ secondPort)
    (localClauseIndex literalIndex : Nat)
    (clauseLt : localClauseIndex < 2)
    (literalLt : literalIndex < 2) :
    BendRouteCardinalTangentCertificate .east secondPort
      localClauseIndex literalIndex := by
  cases secondPort with
  | west =>
      interval_cases localClauseIndex <;>
        interval_cases literalIndex <;>
        constructor <;> native_decide
  | east => exact (different rfl).elim
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
