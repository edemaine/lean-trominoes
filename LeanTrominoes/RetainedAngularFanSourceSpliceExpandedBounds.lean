import LeanTrominoes.RetainedAngularFanSourceSpliceBounds
import LeanTrominoes.RetainedRayRasterizationRadiusBounds

/-!
# Expanded-period bounds for retained angular-fan source splices

A raw retained source route lies in the open neighboring-period square.
The fixed-eight construction first applies a large integral refinement, then
replaces the old variable endpoint by an outer fan and rasterizes the result.
Integral scaling turns the raw strict one-cell margin into enough room for
both the radius-288 fan replacement and the radius-nine rasterization error.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- A source-first retained angular-fan boundary splice remains in the open
neighboring-period square whenever its combined refinement exceeds the
fan-and-raster margin `288 + 9`. -/
theorem
    retainedAngularFanSourceScaledSplicedBoundaryRoute_point_inExpanded
    {factor period : Nat}
    (factorPositive : 0 < factor)
    (marginFits :
      297 < retainedTerminalFanTotalRefinement * factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (retained : RetainedRayPolyline route)
    (routeBounded :
      ∀ point ∈ route,
        let sourcePeriod : Int := period
        -sourcePeriod < point.1 ∧
          point.1 < 2 * sourcePeriod ∧
          -sourcePeriod < point.2 ∧
          point.2 < 2 * sourcePeriod)
    {point : Cell}
    (pointMember :
      point ∈
        retainedAngularFanSplicedBoundaryRoute
          (scalePolyline factor route)
          (scaleRetainedTerminalData factor terminal)
          slot) :
    let refinedPeriod : Int :=
      (retainedTerminalFanTotalRefinement * factor) * period
    -refinedPeriod < point.1 ∧
      point.1 < 2 * refinedPeriod ∧
      -refinedPeriod < point.2 ∧
      point.2 < 2 * refinedPeriod := by
  let lower : Cell :=
    (1 - (period : Int), 1 - (period : Int))
  let upper : Cell :=
    (2 * (period : Int) - 1,
      2 * (period : Int) - 1)
  have sourceInRectangle :
      ∀ sourcePoint ∈ route,
        InClosedGridRectangle lower upper sourcePoint := by
    intro sourcePoint sourcePointMember
    have bounded :=
      routeBounded sourcePoint sourcePointMember
    rcases sourcePoint with ⟨sourceX, sourceY⟩
    simpa [lower, upper, InClosedGridRectangle] using
      (show
        1 - (period : Int) ≤ sourceX ∧
          sourceX ≤ 2 * (period : Int) - 1 ∧
          1 - (period : Int) ≤ sourceY ∧
          sourceY ≤ 2 * (period : Int) - 1 by
        omega)
  let scaledRoute := scalePolyline factor route
  let scaledTerminal :=
    scaleRetainedTerminalData factor terminal
  let splicedPolyline :=
    retainedAngularFanSplicedBoundaryPolyline
      scaledRoute scaledTerminal slot
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified
        factorPositive classified
  have scaledRetained : RetainedRayPolyline scaledRoute :=
    retained.scale factorPositive
  have splicedRetained :
      RetainedRayPolyline splicedPolyline := by
    simpa [splicedPolyline] using
      retainedAngularFanSplicedBoundaryPolyline_retained
        scaledRoute scaledTerminal slot scaledLength
        scaledClassified scaledRetained
  have splicedBounded :
      ∀ splicedPoint ∈ splicedPolyline,
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              lower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              upper))
          splicedPoint := by
    intro splicedPoint splicedPointMember
    exact
      retainedAngularFanSourceScaledSplicedBoundaryPolyline_point_in_routeRectangle
        factorPositive route terminal slot routeLength classified
        lower upper sourceInRectangle
        (by simpa [splicedPolyline, scaledRoute, scaledTerminal]
          using splicedPointMember)
  have rasterBounded :=
    rasterizeRetainedPolyline_point_in_expandedRectangle
      splicedRetained splicedBounded
      (by simpa [retainedAngularFanSplicedBoundaryRoute,
        splicedPolyline, scaledRoute, scaledTerminal]
        using pointMember)
  have marginFitsInt :
      (297 : Int) <
        retainedTerminalFanTotalRefinement * factor := by
    exact_mod_cast marginFits
  rcases point with ⟨pointX, pointY⟩
  simp only [InClosedGridRectangle,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.scale] at rasterBounded
  dsimp only [lower, upper] at rasterBounded
  dsimp only
  norm_num [Nat.cast_mul] at rasterBounded marginFitsInt ⊢
  omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
