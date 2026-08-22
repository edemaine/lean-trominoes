/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelection

/-! # Exactness and uniqueness of finite affine route-shape selection -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

@[simp] theorem mem_allFanoutShapes (shape : FanoutShape) :
    shape ∈ allFanoutShapes := by
  cases shape <;> simp [allFanoutShapes]

@[simp] theorem mem_allCoreShapes (shape : CoreShape) :
    shape ∈ allCoreShapes := by
  cases shape <;> simp [allCoreShapes]

@[simp] theorem mem_allRouteShapes (shape : RouteShape) :
    shape ∈ allRouteShapes := by
  rcases shape with ⟨source, core, target⟩
  cases source <;> cases core <;> cases target <;>
    simp [allRouteShapes, allFanoutShapes, allCoreShapes]

theorem allRouteShapes_length : allRouteShapes.length = 28 := by
  decide

theorem allRouteShapes_nodup : allRouteShapes.Nodup := by
  decide

/-- Any matching fanout shape is exactly the finite selector result. -/
theorem FanoutShape.select_eq_of_matches
    (shape : FanoutShape) (endpoint : Endpoint)
    (descriptor : RouteDescriptor) (shapeMatches : shape.Matches endpoint descriptor) :
    FanoutShape.select endpoint descriptor = shape := by
  cases shape <;>
    simpa [FanoutShape.select, FanoutShape.Matches] using shapeMatches

/-- Two fanout shapes cannot both match one endpoint unless they are equal. -/
theorem FanoutShape.eq_of_matches
    {first second : FanoutShape} {endpoint : Endpoint}
    {descriptor : RouteDescriptor}
    (firstMatches : first.Matches endpoint descriptor)
    (secondMatches : second.Matches endpoint descriptor) :
    first = second := by
  rw [← first.select_eq_of_matches endpoint descriptor firstMatches,
    ← second.select_eq_of_matches endpoint descriptor secondMatches]

/-- Any matching core shape is exactly the partial finite selector result. -/
theorem CoreShape.select?_eq_some_of_matches
    (shape : CoreShape) (descriptor : RouteDescriptor)
    (shapeMatches : shape.Matches descriptor) :
    CoreShape.select? descriptor = some shape := by
  cases shape with
  | zero =>
      simp [CoreShape.Matches] at shapeMatches
      simp [CoreShape.select?, shapeMatches]
  | positiveHorizontalDirect =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.select?, offset, order]
  | positiveHorizontalBent =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.select?, offset, order]
  | negativeHorizontalDirect =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.select?, offset, order]
  | negativeHorizontalBent =>
      rcases shapeMatches with ⟨offset, order⟩
      simp [CoreShape.select?, offset, order]
  | positiveVertical =>
      simp [CoreShape.Matches] at shapeMatches
      simp [CoreShape.select?, shapeMatches]
  | negativeVertical =>
      simp [CoreShape.Matches] at shapeMatches
      simp [CoreShape.select?, shapeMatches]

/-- Two core shapes cannot both match one descriptor unless they are equal. -/
theorem CoreShape.eq_of_matches
    {first second : CoreShape} {descriptor : RouteDescriptor}
    (firstMatches : first.Matches descriptor)
    (secondMatches : second.Matches descriptor) :
    first = second := by
  have firstEq := first.select?_eq_some_of_matches descriptor firstMatches
  have secondEq := second.select?_eq_some_of_matches descriptor secondMatches
  rw [secondEq] at firstEq
  exact Option.some.inj firstEq.symm

/-- Any matching complete route shape is exactly the partial selector result. -/
theorem RouteShape.select?_eq_some_of_matches
    (shape : RouteShape) (descriptor : RouteDescriptor)
    (shapeMatches : shape.Matches descriptor) :
    RouteShape.select? descriptor = some shape := by
  rcases shape with ⟨source, core, target⟩
  rcases shapeMatches with ⟨sourceMatches, coreMatches, targetMatches⟩
  unfold RouteShape.select?
  rw [core.select?_eq_some_of_matches descriptor coreMatches]
  simp [source.select_eq_of_matches .source descriptor sourceMatches,
    target.select_eq_of_matches .target descriptor targetMatches]

/-- Exactly one of the twenty-eight complete route shapes can match a local
descriptor. -/
theorem RouteShape.eq_of_matches
    {first second : RouteShape} {descriptor : RouteDescriptor}
    (firstMatches : first.Matches descriptor)
    (secondMatches : second.Matches descriptor) :
    first = second := by
  have firstEq := first.select?_eq_some_of_matches descriptor firstMatches
  have secondEq := second.select?_eq_some_of_matches descriptor secondMatches
  rw [secondEq] at firstEq
  exact Option.some.inj firstEq.symm

/-- A locally shaped descriptor's selector returns its unique matching shape. -/
theorem RouteDescriptor.exists_selectedShape
    {descriptor : RouteDescriptor}
    (hasLocalShape :
      RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape descriptor) :
    ∃ shape, RouteShape.select? descriptor = some shape ∧
      shape.Matches descriptor := by
  rcases hasLocalShape with ⟨shape, shapeMatches⟩
  exact ⟨shape, shape.select?_eq_some_of_matches descriptor shapeMatches,
    shapeMatches⟩

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
