/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineCycleDirectionSemantics

/-! # Finite retained Figure 9 cycle descriptor suffix -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open PeriodicThreeSATThree

/-- Stable zero-based index tags do not affect a constant flat-map block. -/
theorem zipIdx_flatMap_const
    {Value Output : Type} (values : List Value) (block : List Output) :
    values.zipIdx.flatMap (fun _ => block) =
      values.flatMap (fun _ => block) := by
  have eraseTags := congrArg
    (fun taggedValues => taggedValues.flatMap fun _ => block)
    (List.zipIdx_map_fst 0 values)
  simpa only [List.flatMap_map, Function.comp_apply] using eraseTags

/-- A genuine stable source-variable index selects exactly the finite local
Figure 7 descriptor block. -/
theorem routedCycleClauseDescriptorsAt_eq_cycleClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {atom : PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable}
    {atomIndex : Nat}
    (atomMember :
      (atom, atomIndex) ∈
        (sourceVariables
          (sourceScaledForFigureSeven source).erase).zipIdx) :
    routedCycleClauseDescriptorsAt source atomIndex =
      FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
  rw [routedCycleClauseDescriptorsAt_eq_for source atomMember]
  exact routedCycleClauseDescriptorsFor_eq_cycleClauseDescriptors
    source atom (List.fst_mem_of_mem_zipIdx atomMember)

/-- Concatenating the routed block at every stable indexed source variable is
the same as repeating the finite Figure 7 descriptor block over the untagged
source-variable enumeration. -/
theorem indexedCycleClauseDescriptors_eq_finite
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (sourceVariables
        (sourceScaledForFigureSeven source).erase).zipIdx.flatMap
        (fun taggedAtom =>
          routedCycleClauseDescriptorsAt source taggedAtom.2) =
      (sourceVariables
        (sourceScaledForFigureSeven source).erase).flatMap
        (fun _ =>
          FormulaShapeFixedEightDirection.cycleClauseDescriptors) := by
  let atoms :=
    sourceVariables (sourceScaledForFigureSeven source).erase
  change atoms.zipIdx.flatMap
      (fun taggedAtom =>
        routedCycleClauseDescriptorsAt source taggedAtom.2) =
    atoms.flatMap (fun _ =>
      FormulaShapeFixedEightDirection.cycleClauseDescriptors)
  have blocksEq :
      atoms.zipIdx.flatMap
          (fun taggedAtom =>
            routedCycleClauseDescriptorsAt source taggedAtom.2) =
        atoms.zipIdx.flatMap (fun _ =>
          FormulaShapeFixedEightDirection.cycleClauseDescriptors) := by
    exact List.flatMap_congr
      (l := atoms.zipIdx)
      (f := fun taggedAtom =>
        routedCycleClauseDescriptorsAt source taggedAtom.2)
      (g := fun _ =>
        FormulaShapeFixedEightDirection.cycleClauseDescriptors) (by
        rintro ⟨atom, atomIndex⟩ atomMember
        exact routedCycleClauseDescriptorsAt_eq_cycleClauseDescriptors
          source atomMember)
  exact blocksEq.trans
    (zipIdx_flatMap_const atoms
      FormulaShapeFixedEightDirection.cycleClauseDescriptors)

/-- Every globally indexed routed implication-cycle descriptor is accounted
for by one copy of the finite local Figure 7 descriptor block per retained
source variable. -/
theorem routedCycleClauseDescriptors_eq_finiteCycleClauseDescriptors
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    routedCycleClauseDescriptors source =
      finiteCycleClauseDescriptors source := by
  rw [routedCycleClauseDescriptors_eq_indexedBlocks]
  unfold finiteCycleClauseDescriptors
  exact indexedCycleClauseDescriptors_eq_finite source

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
