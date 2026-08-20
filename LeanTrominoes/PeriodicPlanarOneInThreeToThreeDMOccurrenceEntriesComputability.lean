/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumeration

/-! # Computability of planar 3DM occurrence entries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem occurrenceEntries_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (occurrenceEntries :
      PeriodicCNF Variable → List (Variable × OccurrenceSlot)) := by
  have pairSlot : Primrec₂ fun
      (data : PeriodicCNF Variable × Variable) (slot : OccurrenceSlot) =>
        (data.2, slot) :=
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have entriesForAtom : Primrec fun data :
      PeriodicCNF Variable × Variable =>
        (usedSlots data.1 data.2).map fun slot => (data.2, slot) :=
    Primrec.list_map usedSlots_primrec pairSlot
  have entriesForAtom₂ : Primrec₂ fun
      (source : PeriodicCNF Variable) (atom : Variable) =>
        (usedSlots source atom).map fun slot => (atom, slot) :=
    entriesForAtom
  exact (Primrec.list_flatMap
    occurringVariables_primrec entriesForAtom₂).of_eq fun source => by
      rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
