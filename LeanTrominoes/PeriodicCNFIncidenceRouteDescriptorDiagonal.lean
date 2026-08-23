/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapUnique
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorNodup

/-! # Diagonal scans of numeric incidence descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- A function that vanishes when stored edge indices differ reduces the
canonical numeric descriptor square to its diagonal. -/
theorem numericRouteDescriptorSquare_flatMap_eq_diagonal
    {Variable Output : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (function : RouteDescriptor × RouteDescriptor → List Output)
    (offDiagonal :
      ∀ first ∈ numericRouteDescriptors formula,
        ∀ second ∈ numericRouteDescriptors formula,
          first.edgeIndex ≠ second.edgeIndex →
            function (first, second) = []) :
    ((numericRouteDescriptors formula) ×ˢ
        (numericRouteDescriptors formula)).flatMap function =
      (numericRouteDescriptors formula).flatMap fun descriptor =>
        function (descriptor, descriptor) := by
  change
    ((numericRouteDescriptors formula).flatMap fun first =>
      (numericRouteDescriptors formula).map fun second =>
        (first, second)).flatMap function = _
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro first firstMember
  rw [List.flatMap_map]
  rw [List.flatMap_eq_selected_of_unique
    (numericRouteDescriptors formula)
    (fun second => function (first, second)) first
    (numericRouteDescriptors_nodup formula)
    firstMember]
  intro second secondMember secondNe
  apply offDiagonal first firstMember second secondMember
  intro edgeIndexEq
  exact secondNe
    (numericRouteDescriptors_eq_of_edgeIndex_eq
      formula secondMember firstMember edgeIndexEq.symm)

end PeriodicCNF
end LeanTrominoes
