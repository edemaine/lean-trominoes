/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarSATClauseKeys

/-!
# Lookup injectivity for geometric-component clause keys

The component/local-clause key list is duplicate-free.  This short adapter
turns that list invariant into the lookup interface used by the assembled
finite incidence drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- In a duplicate-free list, two successful lookups of the same value have
the same natural-number index. -/
theorem List.Nodup.index_eq_of_getElem?_eq_some
    {Value : Type*} {values : List Value}
    (nodup : values.Nodup)
    {firstIndex secondIndex : Nat} {value : Value}
    (firstLookup : values[firstIndex]? = some value)
    (secondLookup : values[secondIndex]? = some value) :
    firstIndex = secondIndex := by
  rcases List.getElem?_eq_some_iff.mp firstLookup with
    ⟨firstIndexLt, firstAt⟩
  rcases List.getElem?_eq_some_iff.mp secondLookup with
    ⟨secondIndexLt, secondAt⟩
  apply (nodup.getElem_inj_iff).mp
  rw [firstAt, secondAt]

/-- Equal component/local-clause keys returned by two metadata lookups force
the global clause indices to be equal. -/
theorem
    drawingPlanarSATClauseMetadata_lookup_componentClauseKey_injective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstMetadata secondMetadata :
      DrawingPlanarSATClauseMetadata Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstLookup :
      (drawingPlanarSATClauseMetadata formula)[firstClauseIndex]? =
        some firstMetadata)
    (secondLookup :
      (drawingPlanarSATClauseMetadata formula)[secondClauseIndex]? =
        some secondMetadata)
    (keysEqual :
      firstMetadata.componentClauseKey =
        secondMetadata.componentClauseKey) :
    firstClauseIndex = secondClauseIndex := by
  let keys :=
    (drawingPlanarSATClauseMetadata formula).map
      DrawingPlanarSATClauseMetadata.componentClauseKey
  have keysNodup : keys.Nodup :=
    drawingPlanarSATClauseMetadata_componentClauseKeys_nodup formula
  have firstKeyLookup :
      keys[firstClauseIndex]? =
        some firstMetadata.componentClauseKey := by
    dsimp [keys]
    rw [List.getElem?_map, firstLookup]
    rfl
  have secondKeyLookup :
      keys[secondClauseIndex]? =
        some secondMetadata.componentClauseKey := by
    dsimp [keys]
    rw [List.getElem?_map, secondLookup]
    rfl
  rw [keysEqual] at firstKeyLookup
  exact List.Nodup.index_eq_of_getElem?_eq_some
    keysNodup firstKeyLookup secondKeyLookup

/-- The complete finite planar-SAT metadata satisfies component/local-clause
key injectivity. -/
theorem drawingPlanarSAT_componentClauseKeysInjective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    DrawingPlanarSATComponentClauseKeysInjective formula := by
  intro firstMetadata secondMetadata
    firstClauseIndex secondClauseIndex
    firstLookup secondLookup
    componentEqual localClauseIndexEqual
  apply
    drawingPlanarSATClauseMetadata_lookup_componentClauseKey_injective
      formula firstLookup secondLookup
  exact Prod.ext componentEqual localClauseIndexEqual

end PeriodicOrthocrossing
end LeanTrominoes
