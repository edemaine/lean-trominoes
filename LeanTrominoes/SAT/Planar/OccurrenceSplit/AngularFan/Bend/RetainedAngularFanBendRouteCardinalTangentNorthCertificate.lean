/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Bend.RetainedAngularFanBendRouteCardinalTangentData

/-! # Cardinal tangent certificates for north-first bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- Every genuine north-first entry of the finite corner table has the
advertised cardinal tangent geometry. -/
theorem bendRouteCardinalTangentCertificate_north
    (secondPort : CornerPort)
    (different : CornerPort.north ≠ secondPort)
    (localClauseIndex literalIndex : Nat)
    (clauseLt : localClauseIndex < 2)
    (literalLt : literalIndex < 2) :
    BendRouteCardinalTangentCertificate .north secondPort
      localClauseIndex literalIndex := by
  cases secondPort with
  | west =>
      interval_cases localClauseIndex <;>
        interval_cases literalIndex <;>
        constructor <;> decide +kernel
  | east =>
      interval_cases localClauseIndex <;>
        interval_cases literalIndex <;>
        constructor <;> decide +kernel
  | south =>
      interval_cases localClauseIndex <;>
        interval_cases literalIndex <;>
        constructor <;> decide +kernel
  | north => exact (different rfl).elim

end PeriodicEightOccurrenceSplit
end LeanTrominoes
