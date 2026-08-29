/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Equality-implementation irrelevance of final route data -/

namespace LeanTrominoes

/-- Any result computed from a decidable equality is independent of the
propositionally unique implementation supplied to the computation. -/
theorem decidableEq_application_irrel
    {Variable Output : Type*}
    (family : DecidableEq Variable → Output)
    (first second : DecidableEq Variable) :
    family first = family second := by
  exact congrArg family (Subsingleton.elim _ _)

/-- Numeric route descriptors do not depend on which propositionally unique
decidable equality implementation is supplied. -/
theorem numericRouteDescriptors_decidableEq_irrel
    {Variable : Type*}
    (first second : DecidableEq Variable)
    (source : PeriodicCNF Variable) :
    @PeriodicCNF.numericRouteDescriptors Variable first source =
      @PeriodicCNF.numericRouteDescriptors Variable second source := by
  have instancesEq : first = second := Subsingleton.elim _ _
  subst second
  rfl

/-- The final coordinated route table likewise does not depend on the chosen
decidable equality implementation. -/
theorem finalCoordinatedSourceRoutes_decidableEq_irrel
    {Variable : Type*}
    (first second : DecidableEq Variable)
    (source : PeriodicCNF Variable) :
    @PeriodicOrthocrossing.finalCoordinatedSourceRoutes
        Variable first source =
      @PeriodicOrthocrossing.finalCoordinatedSourceRoutes
        Variable second source := by
  have instancesEq : first = second := Subsingleton.elim _ _
  subst second
  rfl

end LeanTrominoes
