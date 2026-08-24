/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorNodup

/-! # Diagonal reduction of numeric route-descriptor squares -/

namespace LeanTrominoes.PeriodicCNF

open PeriodicOrthocrossing

/-- A flat map with one potentially nonempty value reduces to its unique
selected branch. -/
private theorem routeDescriptorFlatMap_eq_of_unique
    {Index Output : Type}
    (indices : List Index) (function : Index → List Output)
    (selected : Index)
    (nodup : indices.Nodup)
    (selectedMember : selected ∈ indices)
    (othersEmpty :
      ∀ index ∈ indices, index ≠ selected → function index = []) :
    indices.flatMap function = function selected := by
  induction indices with
  | nil => simp at selectedMember
  | cons index indices induction =>
      rw [List.nodup_cons] at nodup
      rcases List.mem_cons.mp selectedMember with selectedHead | selectedTail
      · subst index
        rw [List.flatMap_cons]
        have tailEmpty : indices.flatMap function = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro other otherMember
          exact othersEmpty other (by simp [otherMember]) fun otherEq =>
            nodup.1 (otherEq ▸ otherMember)
        rw [tailEmpty, List.append_nil]
      · have headNe : index ≠ selected := by
          intro headEq
          exact nodup.1 (headEq ▸ selectedTail)
        rw [List.flatMap_cons,
          othersEmpty index (by simp) headNe,
          List.nil_append]
        exact induction nodup.2 selectedTail fun other otherMember otherNe =>
          othersEmpty other (by simp [otherMember]) otherNe

/-- Any block scan that is empty for unequal edge indices reduces the
row-major numeric descriptor square to its diagonal, preserving route order. -/
theorem numericRouteDescriptorSquare_flatMap_diagonal_of_offDiagonal
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
  rw [routeDescriptorFlatMap_eq_of_unique
    (numericRouteDescriptors formula)
    (fun second => function (first, second)) first
    (numericRouteDescriptors_nodup formula) firstMember]
  intro second secondMember secondNe
  apply offDiagonal first firstMember second secondMember
  intro edgeIndexEq
  exact secondNe
    (numericRouteDescriptors_eq_of_edgeIndex_eq
      formula secondMember firstMember edgeIndexEq.symm)

end LeanTrominoes.PeriodicCNF
