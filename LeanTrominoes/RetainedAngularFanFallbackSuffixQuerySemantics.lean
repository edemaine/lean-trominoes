/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryData

/-! # Geometric semantics of carrier and bend suffix-query blocks -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixQueries

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open FallbackSuffixDirectionCompiler.Batch

/-- Compiling a valid four-route carrier query block gives the geometric
suffixes selected by the public route policy. -/
theorem carrierDirections_eq_routeSuffixes
    (horizontal : Bool) (span : Int) (large : 6 < span)
    (first second third fourth : RetainedTerminalSlot) :
    directions
        (carrierQueries horizontal span [first, second, third, fourth]) =
      retainedDirections
        [routeQuery (horizontalEqualityLensRoutes span 0 0)
            (carrierLensRouteTerminalData horizontal span 0 0) first,
          routeQuery (horizontalEqualityLensRoutes span 0 1)
            (carrierLensRouteTerminalData horizontal span 0 1) second,
          routeQuery (horizontalEqualityLensRoutes span 1 0)
            (carrierLensRouteTerminalData horizontal span 1 0) third,
          routeQuery (horizontalEqualityLensRoutes span 1 1)
            (carrierLensRouteTerminalData horizontal span 1 1) fourth] := by
  calc
    _ = retainedDirections
          (carrierQueries horizontal span
            [first, second, third, fourth]) :=
      directions_eq_retainedDirections _
        (carrierQueries_lengthPositive horizontal span large _)
    _ = _ := congrArg retainedDirections
      (carrierQueries_eq_routeQueries horizontal span
        first second third fourth)

/-- Compiling a four-route bend query block gives the ordinary geometric
suffixes selected by the public route policy. -/
theorem bendDirections_eq_routeSuffixes
    (firstPort secondPort : CornerPort)
    (first second third fourth : RetainedTerminalSlot) :
    directions
        (bendQueries firstPort secondPort
          [first, second, third, fourth]) =
      retainedDirections
        [routeQuery (cornerEqualityRoutes firstPort secondPort 0 0)
            (bendRouteTerminalData firstPort secondPort 0 0) first,
          routeQuery (cornerEqualityRoutes firstPort secondPort 0 1)
            (bendRouteTerminalData firstPort secondPort 0 1) second,
          routeQuery (cornerEqualityRoutes firstPort secondPort 1 0)
            (bendRouteTerminalData firstPort secondPort 1 0) third,
          routeQuery (cornerEqualityRoutes firstPort secondPort 1 1)
            (bendRouteTerminalData firstPort secondPort 1 1) fourth] := by
  calc
    _ = retainedDirections
          (bendQueries firstPort secondPort
            [first, second, third, fourth]) :=
      directions_eq_retainedDirections _
        (bendQueries_lengthPositive firstPort secondPort _)
    _ = _ := congrArg retainedDirections
      (bendQueries_eq_routeQueries firstPort secondPort
        first second third fourth)

end FallbackSuffixQueries
end PeriodicEightOccurrenceSplit
end LeanTrominoes
