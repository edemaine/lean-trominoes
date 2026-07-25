import LeanTrominoes.PeriodicOneInThreeToThreeDMMatching

/-!
# Duplicate-free typed periodic 3DM presentations

The natural-number encoding uses `List.idxOf`, so its semantic faithfulness
requires each declared element and triple prototype to have a unique list
position.  The construction satisfies this invariant because variables and
tagged positions are unique and the relevant inductive constructors have
disjoint images.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Mapping every pair in two duplicate-free lists through an injective
two-argument constructor remains duplicate-free. -/
theorem nodup_flatMap_map {Left Right Output : Type*}
    (lefts : List Left) (rights : List Right)
    (leftNodup : lefts.Nodup) (rightNodup : rights.Nodup)
    (combine : Left → Right → Output)
    (injective :
      ∀ {firstLeft secondLeft firstRight secondRight},
        combine firstLeft firstRight = combine secondLeft secondRight →
          firstLeft = secondLeft ∧ firstRight = secondRight) :
    (lefts.flatMap fun left =>
      rights.map (combine left)).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro left leftMember
    exact rightNodup.map fun firstRight secondRight equal =>
      (injective equal).2
  · exact leftNodup.imp fun {firstLeft secondLeft} different =>
      List.disjoint_left.mpr fun output firstMember secondMember => by
        rcases List.mem_map.mp firstMember with
          ⟨firstRight, firstRightMember, rfl⟩
        rcases List.mem_map.mp secondMember with
          ⟨secondRight, secondRightMember, equal⟩
        exact different (injective equal.symm).1

theorem allVariableTriples_nodup : allVariableTriples.Nodup := by
  decide

theorem allVariableReds_nodup : allVariableReds.Nodup := by
  decide

theorem allVariableGreens_nodup : allVariableGreens.Nodup := by
  decide

theorem occurrenceSlots_nodup : OccurrenceSlot.all.Nodup := by
  decide

/-- The occurring-variable list is duplicate-free by construction. -/
theorem occurringVariables_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (occurringVariables source).Nodup := by
  apply List.nodup_dedup

/-- All six-triple variable blocks have distinct typed triple names. -/
theorem variableTriples_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    (variableTriples source).Nodup := by
  apply nodup_flatMap_map
    (occurringVariables source) allVariableTriples
    (occurringVariables_nodup source) allVariableTriples_nodup
  intro firstAtom secondAtom firstTriple secondTriple equal
  cases equal
  exact ⟨rfl, rfl⟩

/-- Clause-auxiliary triples are unique because tagged clause/literal
positions are unique. -/
theorem clauseAuxiliaryTriples_nodup {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (clauseAuxiliaryTriples source).Nodup := by
  have positions :
      ((PeriodicThreeSATThree.taggedLiterals source).map fun tagged =>
        (tagged.2.1, tagged.2.2)).Nodup := by
    rw [taggedLiterals_positions]
    exact PeriodicThreeSATThree.occurrenceIndicesFrom_nodup
      0 source.clauses
  have mapped := positions.map
    (fun first second equal => by
      cases first
      cases second
      simp only [Triple.clauseAuxiliary.injEq] at equal
      exact Prod.ext equal.1 equal.2 :
      Function.Injective fun position : Nat × Nat =>
        Triple.clauseAuxiliary
          (Variable := Variable) position.1 position.2)
  simpa [clauseAuxiliaryTriples, List.map_map,
    Function.comp_def] using mapped

/-- Variable and auxiliary constructors make the complete triple list
duplicate-free. -/
theorem triples_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (triples source).Nodup := by
  rw [triples, List.nodup_append]
  refine ⟨variableTriples_nodup source,
    clauseAuxiliaryTriples_nodup source, ?_⟩
  intro variableTriple variableMember auxiliaryTriple auxiliaryMember
  rcases List.mem_flatMap.mp variableMember with
    ⟨atom, atomMember, variableMember⟩
  rcases List.mem_map.mp variableMember with
    ⟨sourceTriple, sourceTripleMember, rfl⟩
  rcases List.mem_map.mp auxiliaryMember with
    ⟨tagged, taggedMember, rfl⟩
  intro equal
  cases equal

/-- Variable-internal red elements are pairwise distinct. -/
theorem variableRedElements_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    ((occurringVariables source).flatMap fun atom =>
      allVariableReds.map (RedElement.variable atom)).Nodup := by
  apply nodup_flatMap_map
    (occurringVariables source) allVariableReds
    (occurringVariables_nodup source) allVariableReds_nodup
  intro firstAtom secondAtom firstElement secondElement equal
  cases equal
  exact ⟨rfl, rfl⟩

/-- The complete red-element list is duplicate-free. -/
theorem redElements_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (redElements source).Nodup := by
  rw [redElements, List.nodup_append]
  refine ⟨variableRedElements_nodup source, ?_, ?_⟩
  · exact List.nodup_range.map fun first second equal =>
      RedElement.clause.inj equal
  · intro variableElement variableMember clauseElement clauseMember
    rcases List.mem_flatMap.mp variableMember with
      ⟨atom, atomMember, variableMember⟩
    rcases List.mem_map.mp variableMember with
      ⟨element, elementMember, rfl⟩
    rcases List.mem_map.mp clauseMember with
      ⟨clauseIndex, clauseMember, rfl⟩
    intro equal
    cases equal

/-- Variable-internal green elements are pairwise distinct. -/
theorem variableGreenElements_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    ((occurringVariables source).flatMap fun atom =>
      allVariableGreens.map (GreenElement.variable atom)).Nodup := by
  apply nodup_flatMap_map
    (occurringVariables source) allVariableGreens
    (occurringVariables_nodup source) allVariableGreens_nodup
  intro firstAtom secondAtom firstElement secondElement equal
  cases equal
  exact ⟨rfl, rfl⟩

/-- The complete green-element list is duplicate-free. -/
theorem greenElements_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (greenElements source).Nodup := by
  rw [greenElements, List.nodup_append]
  refine ⟨variableGreenElements_nodup source, ?_, ?_⟩
  · exact List.nodup_range.map fun first second equal =>
      GreenElement.clause.inj equal
  · intro variableElement variableMember clauseElement clauseMember
    rcases List.mem_flatMap.mp variableMember with
      ⟨atom, atomMember, variableMember⟩
    rcases List.mem_map.mp variableMember with
      ⟨element, elementMember, rfl⟩
    rcases List.mem_map.mp clauseMember with
      ⟨clauseIndex, clauseMember, rfl⟩
    intro equal
    cases equal

/-- Each atom's filtered unused slots are duplicate-free. -/
theorem unusedSlotsFor_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) :
    (OccurrenceSlot.all.filterMap fun slot =>
      if (occurrenceAt source atom slot).isNone then
        some (atom, slot)
      else
        none).Nodup := by
  apply occurrenceSlots_nodup.filterMap
  intro firstSlot secondSlot output firstMember secondMember
  simp only [Option.mem_def] at firstMember secondMember
  split at firstMember
  · split at secondMember
    · exact congrArg Prod.snd <|
        Option.some.inj (firstMember.trans secondMember.symm)
    · simp at secondMember
  · simp at firstMember

/-- Unused variable slots are pairwise distinct. -/
theorem unusedSlots_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (unusedSlots source).Nodup := by
  rw [unusedSlots, List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro atom atomMember
    exact unusedSlotsFor_nodup source atom
  · exact (occurringVariables_nodup source).imp
      fun {firstAtom secondAtom} different =>
        List.disjoint_left.mpr
          fun output firstMember secondMember => by
            simp only [List.mem_filterMap] at firstMember secondMember
            rcases firstMember with
              ⟨firstSlot, firstSlotMember, firstProduced⟩
            rcases secondMember with
              ⟨secondSlot, secondSlotMember, secondProduced⟩
            split at firstProduced
            · split at secondProduced
              · exact different <|
                  congrArg Prod.fst
                    (Option.some.inj
                      (firstProduced.trans secondProduced.symm))
              · simp at secondProduced
            · simp at firstProduced

/-- Complementary blue elements are pairwise distinct. -/
theorem complementBlueElements_nodup {Variable : Type*}
    (source : PeriodicCNF Variable) :
    ((PeriodicThreeSATThree.taggedLiterals source).map fun tagged =>
      BlueElement.complement
        (Variable := Variable) tagged.2.1 tagged.2.2).Nodup := by
  have positions :
      ((PeriodicThreeSATThree.taggedLiterals source).map fun tagged =>
        (tagged.2.1, tagged.2.2)).Nodup := by
    rw [taggedLiterals_positions]
    exact PeriodicThreeSATThree.occurrenceIndicesFrom_nodup
      0 source.clauses
  have mapped := positions.map
    (fun first second equal => by
      cases first
      cases second
      simp only [BlueElement.complement.injEq] at equal
      exact Prod.ext equal.1 equal.2 :
      Function.Injective fun position : Nat × Nat =>
        BlueElement.complement
          (Variable := Variable) position.1 position.2)
  simpa [List.map_map, Function.comp_def] using mapped

/-- Private unused-slot blue elements are pairwise distinct. -/
theorem unusedBlueElements_nodup {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    ((unusedSlots source).map fun tagged =>
      BlueElement.unused tagged.1 tagged.2).Nodup := by
  exact (unusedSlots_nodup source).map fun first second equal => by
    cases first
    cases second
    simpa only [BlueElement.unused.injEq, Prod.mk.injEq] using equal

/-- The complete blue-element list is duplicate-free. -/
theorem blueElements_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (blueElements source).Nodup := by
  rw [blueElements, List.nodup_append]
  refine ⟨?_, unusedBlueElements_nodup source, ?_⟩
  · rw [List.nodup_append]
    refine ⟨?_, complementBlueElements_nodup source, ?_⟩
    · exact List.nodup_range.map fun first second equal =>
        BlueElement.clause.inj equal
    · intro clauseElement clauseMember complementElement complementMember
      rcases List.mem_map.mp clauseMember with
        ⟨clauseIndex, clauseMember, rfl⟩
      rcases List.mem_map.mp complementMember with
        ⟨tagged, taggedMember, rfl⟩
      intro equal
      cases equal
  · intro usedElement usedMember unusedElement unusedMember
    rcases List.mem_append.mp usedMember with
      clauseMember | complementMember
    · rcases List.mem_map.mp clauseMember with
        ⟨clauseIndex, clauseMember, rfl⟩
      rcases List.mem_map.mp unusedMember with
        ⟨tagged, taggedMember, rfl⟩
      intro equal
      cases equal
    · rcases List.mem_map.mp complementMember with
        ⟨tagged, taggedMember, rfl⟩
      rcases List.mem_map.mp unusedMember with
        ⟨unused, unusedMember, rfl⟩
      intro equal
      cases equal

/-- All four finite lists of the constructed typed problem are
duplicate-free. -/
theorem problem_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (problem source).redElements.Nodup ∧
      (problem source).greenElements.Nodup ∧
      (problem source).blueElements.Nodup ∧
      (problem source).triples.Nodup :=
  ⟨redElements_nodup source, greenElements_nodup source,
    blueElements_nodup source, triples_nodup source⟩

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
