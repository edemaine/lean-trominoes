/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceGraphRenaming
import LeanTrominoes.PeriodicPlanarSATOneDimensional
import LeanTrominoes.PeriodicExactOneInjectiveRenaming

/-! # All four planar 1D languages preserve injective atom renaming -/
namespace LeanTrominoes.PeriodicCNF
variable {V W : Type} [DecidableEq V] [DecidableEq W]

theorem occurrences_rename_iff (g : V → W) (hg : Function.Injective g) (f : PeriodicCNF V) (bound : Nat) :
    (f.rename g).OccurrencesAtMost bound ↔ f.OccurrencesAtMost bound := by
  constructor
  · intro result a
    have h := result (g a)
    rw [variableOccurrences_rename,List.count_map_of_injective _ _ hg] at h
    exact h
  · exact occurrences_rename g f hg bound

theorem local_rename (g : V → W) (f : PeriodicCNF V) : (f.rename g).IsLocal ↔ f.IsLocal := by
  simp [rename,renameClause,IsLocal,PeriodicClause.IsLocal,PeriodicClause.offsetDistance,PeriodicLiteral.rename]

theorem presentationSize_rename (g : V → W) (f : PeriodicCNF V) :
    (f.rename g).presentationSize=f.presentationSize := by
  simp [presentationSize,presentationLiteralCount,rename,renameClause,List.length_flatten,List.map_map,Function.comp_def]

end LeanTrominoes.PeriodicCNF

namespace LeanTrominoes.PeriodicPlanarSAT
variable {V W : Type} [Primcodable V] [Primcodable W] [DecidableEq V] [DecidableEq W]

def renameInput (g : V → W) (input : Input V) : Input W := (input.1.rename g,input.2)

theorem gridBound_rename (g : V → W) (input : Input V) (coefficient : Nat) :
    GridBound coefficient (renameInput g input) ↔ GridBound coefficient input := by
  simp only [GridBound,renameInput,PeriodicCNF.presentationSize_rename]

theorem ordinary_rename (g : V → W) (hg : Function.Injective g) (input : Input V) :
    Orbit.LocalOneDimensionalProblem (renameInput g input) ↔ Orbit.LocalOneDimensionalProblem input := by
  simp only [Orbit.LocalOneDimensionalProblem,Orbit.BoundedLocalProblem,Orbit.LocalProblem,Orbit.Problem,Orbit.Valid,
    GridBound,renameInput,PeriodicCNF.presentationSize_rename,PeriodicCNF.oneDimensional_rename,PeriodicCNF.local_rename,
    PeriodicCNF.width_rename,PeriodicCNF.orbitCompatible_rename g hg,PeriodicCNF.satisfiable_rename_iff g _ hg]

theorem ordinaryThree_rename (g : V → W) (hg : Function.Injective g) (input : Input V) :
    Orbit.LocalOneDimensionalThreeOccurrenceProblem (renameInput g input) ↔ Orbit.LocalOneDimensionalThreeOccurrenceProblem input := by
  simp only [Orbit.LocalOneDimensionalThreeOccurrenceProblem,Orbit.BoundedLocalThreeOccurrenceProblem,
    Orbit.LocalThreeOccurrenceProblem,Orbit.ThreeOccurrenceProblem,Orbit.Problem,Orbit.Valid,
    GridBound,renameInput,PeriodicCNF.presentationSize_rename,PeriodicCNF.oneDimensional_rename,PeriodicCNF.local_rename,
    PeriodicCNF.width_rename,PeriodicCNF.orbitCompatible_rename g hg,PeriodicCNF.satisfiable_rename_iff g _ hg,
    PeriodicCNF.occurrences_rename_iff g hg]

theorem exactOne_rename (g : V → W) (hg : Function.Injective g) (input : Input V) :
    Unbounded.LocalOneDimensionalExactOneProblem (renameInput g input) ↔ Unbounded.LocalOneDimensionalExactOneProblem input := by
  simp only [Unbounded.LocalOneDimensionalExactOneProblem,Unbounded.BoundedLocalExactOneProblem,Unbounded.LocalExactOneProblem,
    Unbounded.ExactOneProblem,Unbounded.Valid,GridBound,renameInput,PeriodicCNF.presentationSize_rename,PeriodicCNF.oneDimensional_rename,
    PeriodicCNF.local_rename,PeriodicCNF.width_rename,PeriodicCNF.finiteCompatible_rename g hg,
    PeriodicOneInThree.satisfiable_rename_iff g _ hg]

theorem exactOneThree_rename (g : V → W) (hg : Function.Injective g) (input : Input V) :
    Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem (renameInput g input) ↔ Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem input := by
  simp only [Unbounded.LocalOneDimensionalExactOneThreeOccurrenceProblem,Unbounded.BoundedLocalExactOneThreeOccurrenceProblem,
    Unbounded.LocalExactOneThreeOccurrenceProblem,Unbounded.ExactOneThreeOccurrenceProblem,Unbounded.ExactOneProblem,
    Unbounded.Valid,GridBound,renameInput,PeriodicCNF.presentationSize_rename,PeriodicCNF.oneDimensional_rename,PeriodicCNF.local_rename,
    PeriodicCNF.width_rename,PeriodicCNF.finiteCompatible_rename g hg,PeriodicOneInThree.satisfiable_rename_iff g _ hg,
    PeriodicCNF.occurrences_rename_iff g hg]

end LeanTrominoes.PeriodicPlanarSAT
