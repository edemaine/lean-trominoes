/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionSemantics

/-! # Finite fallback-policy tables for retained carriers and bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing PlanarThreeSAT

/-- The public router uses the escaped policy exactly when deleting the old
endpoint leaves a singleton point prefix. -/
def retainedFallbackFanKindOfRoute
    (route : List Cell) : RetainedFallbackFanKind :=
  if route.dropLast.length = 1 then .escaped else .ordinary

/-- Clause-major fallback policies for one four-incidence carrier lens. -/
def carrierFallbackFanKindBlock : List RetainedFallbackFanKind :=
  [.escaped, .ordinary, .ordinary, .escaped]

/-- Every route of a retained bend uses the ordinary fallback policy. -/
def bendFallbackFanKindBlock : List RetainedFallbackFanKind :=
  List.replicate 4 .ordinary

/-- The two straight carrier routes have singleton retained prefixes; the
two routed carrier incidences do not. -/
theorem carrierFallbackFanKindBlock_eq
    (span : Int) :
    [retainedFallbackFanKindOfRoute
        (horizontalEqualityLensRoutes span 0 0),
      retainedFallbackFanKindOfRoute
        (horizontalEqualityLensRoutes span 0 1),
      retainedFallbackFanKindOfRoute
        (horizontalEqualityLensRoutes span 1 0),
      retainedFallbackFanKindOfRoute
        (horizontalEqualityLensRoutes span 1 1)] =
      carrierFallbackFanKindBlock := by
  rfl

/-- Every genuine entry of every corner table has a nonsingleton retained
prefix; equal-port totalization is empty and therefore ordinary as well. -/
theorem bendFallbackFanKindBlock_eq
    (firstPort secondPort : CornerPort) :
    [retainedFallbackFanKindOfRoute
        (cornerEqualityRoutes firstPort secondPort 0 0),
      retainedFallbackFanKindOfRoute
        (cornerEqualityRoutes firstPort secondPort 0 1),
      retainedFallbackFanKindOfRoute
        (cornerEqualityRoutes firstPort secondPort 1 0),
      retainedFallbackFanKindOfRoute
        (cornerEqualityRoutes firstPort secondPort 1 1)] =
      bendFallbackFanKindBlock := by
  cases firstPort <;> cases secondPort <;> native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
