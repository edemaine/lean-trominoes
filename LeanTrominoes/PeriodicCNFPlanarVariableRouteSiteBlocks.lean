/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupDisjointBlocks
import LeanTrominoes.PeriodicCNFPlanarVertexGadgets

/-! # Incidence blocks in the routed-variable site enumeration -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The nine translated variable sites contributed by one incidence atom and
one normalized incidence offset. -/
def variableRouteSiteBlock {Variable : Type*}
    (atom : Variable) (offset : Cell) :
    List (VariableRouteSite Variable) :=
  neighborTranslations.map fun translate =>
    (atom, Cell.add translate offset)

theorem variableRouteSiteBlock_nodup
    {Variable : Type*} (atom : Variable) (offset : Cell) :
    (variableRouteSiteBlock atom offset).Nodup := by
  apply neighborTranslations_nodup.map_on
  intro first _firstMember second _secondMember equality
  have offsetEquality := congrArg Prod.snd equality
  rcases first with ⟨firstHorizontal, firstVertical⟩
  rcases second with ⟨secondHorizontal, secondVertical⟩
  rcases offset with ⟨offsetHorizontal, offsetVertical⟩
  simp only [Cell.add, Prod.mk.injEq] at offsetEquality
  exact Prod.ext (by omega) (by omega)

theorem variableRouteSiteBlock_disjoint_of_ne
    {Variable : Type*} [DecidableEq Variable]
    {first second : Variable} (different : first ≠ second)
    (firstOffset secondOffset : Cell) :
    List.Disjoint
      (variableRouteSiteBlock first firstOffset)
      (variableRouteSiteBlock second secondOffset) := by
  rw [List.disjoint_left]
  intro site firstMember secondMember
  rw [variableRouteSiteBlock, List.mem_map] at firstMember secondMember
  obtain ⟨_, _, rfl⟩ := firstMember
  obtain ⟨_, _, equality⟩ := secondMember
  exact different (congrArg Prod.fst equality.symm)

/-- Before last-occurrence deduplication, the routed-variable site stream is
one nine-site translated block per incidence, in incidence order. -/
theorem drawingVariableRouteSites_eq_dedup_incidenceBlocks
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    drawingVariableRouteSites formula =
      ((PeriodicCNF.incidencesWithMetadata formula).flatMap fun incidence =>
        variableRouteSiteBlock incidence.literal.atom
          incidence.edge.offset).dedup := by
  unfold drawingVariableRouteSites drawingCNFRouteOccurrences
  rw [List.map_flatMap]
  congr 1
  calc
    (PeriodicCNF.incidencesWithMetadata formula).zipIdx.flatMap
          (fun taggedIncidence =>
            (neighborTranslations.map fun translate =>
              CNFRouteOccurrence.mk taggedIncidence.1 taggedIncidence.2
                translate).map
              CNFRouteOccurrence.variableOccurrence) =
        (PeriodicCNF.incidencesWithMetadata formula).zipIdx.flatMap
          (fun taggedIncidence =>
            variableRouteSiteBlock taggedIncidence.1.literal.atom
              taggedIncidence.1.edge.offset) := by
      apply List.flatMap_congr
      intro taggedIncidence _taggedMember
      rfl
    _ = ((PeriodicCNF.incidencesWithMetadata formula).zipIdx.map
          Prod.fst).flatMap fun incidence =>
            variableRouteSiteBlock incidence.literal.atom
              incidence.edge.offset := by
      rw [List.flatMap_map]
    _ = (PeriodicCNF.incidencesWithMetadata formula).flatMap fun incidence =>
          variableRouteSiteBlock incidence.literal.atom
            incidence.edge.offset := by
      rw [List.zipIdx_map_fst]

end PeriodicOrthocrossing
end LeanTrominoes
