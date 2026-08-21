/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData

/-! # Equality-instance independence of numeric route enumeration -/

namespace LeanTrominoes.PeriodicCNF

/-- Numeric route enumeration is independent of which decision procedure is
used for equality. -/
theorem numericRouteDescriptors_congr_decidableEq
    {Variable : Type*}
    (first second : DecidableEq Variable)
    (formula : PeriodicCNF Variable) :
    @numericRouteDescriptors Variable first formula =
      @numericRouteDescriptors Variable second formula := by
  have equal : first = second := Subsingleton.elim _ _
  cases equal
  rfl

end LeanTrominoes.PeriodicCNF
