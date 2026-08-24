/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorData
import LeanTrominoes.PeriodicThreeSATThreeCycleExactOccurrences
import LeanTrominoes.PeriodicThreeSATThreeFormulaVariableOccurrenceSplitLight
import LeanTrominoes.PeriodicThreeSATThreeSize

/-! # Lightweight target-rank formula for cycle-link incidences -/

namespace LeanTrominoes.PeriodicThreeSATThree

private theorem occurrenceVariable_count_eq_decidable'
    {Variable : Type*} [DecidableEq Variable]
    (atom : ThreeOccurrenceVariable Variable)
    (values : List (ThreeOccurrenceVariable Variable)) :
    @List.count (ThreeOccurrenceVariable Variable) instBEqProd atom values =
      @List.count (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq atom values := by
  induction values with
  | nil => rfl
  | cons head values induction =>
      by_cases equal : head = atom
      · subst head
        simp [induction]
      · simp [equal, induction]

private theorem indexedPrefixCount_fiber_eq_range'
    {Value Key : Type*} [DecidableEq Key]
    (seen : List Key) (values : List Value)
    (keyOf : Value → Key) (key : Key) :
    (values.zipIdx.flatMap fun tagged =>
        if keyOf tagged.1 = key then
          [1 + @List.count Key instBEqOfDecidableEq key
            (seen ++ (values.map keyOf).take tagged.2)]
        else []) =
      List.range'
        (1 + @List.count Key instBEqOfDecidableEq key seen)
        (@List.count Key instBEqOfDecidableEq key
          (values.map keyOf)) := by
  induction values generalizing seen with
  | nil => simp
  | cons value values induction =>
      rw [List.zipIdx_cons, List.flatMap_cons,
        List.zipIdx_eq_map_add, List.flatMap_map]
      simp only [Nat.add_comm]
      by_cases valueEq : keyOf value = key
      · simp [valueEq, List.count_append,
          List.range'_succ, Nat.add_assoc]
        convert induction (seen ++ [keyOf value]) using 1
        all_goals simp [List.count_append, valueEq] <;> try omega
      · simp [valueEq, List.count_append]
        convert induction (seen ++ [keyOf value]) using 1
        all_goals simp [List.count_append, valueEq] <;> try omega

private theorem indexedPrefixCount_fiber_eq_one_two
    {Value Key : Type*} [DecidableEq Key]
    (values : List Value) (keyOf : Value → Key) (key : Key)
    (twice : @List.count Key instBEqOfDecidableEq key
      (values.map keyOf) = 2) :
    (values.zipIdx.flatMap fun tagged =>
        if keyOf tagged.1 = key then
          [1 + @List.count Key instBEqOfDecidableEq key
            ((values.map keyOf).take tagged.2)]
        else []) = [1, 2] := by
  calc
    _ = List.range' 1 2 := by
      simpa only [List.nil_append, List.count_nil, Nat.add_zero, twice]
        using indexedPrefixCount_fiber_eq_range'
          ([] : List Key) values keyOf key
    _ = [1, 2] := by rfl

/-- At a fixed copied occurrence, a cycle-link incidence's target rank is
one copied-prefix use plus the number of matching earlier cycle incidences. -/
theorem cycleLinkIncidence_numericTargetRank_eq_one_add_prefixCount
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source)
    (incidence : CNFIncidence (ThreeOccurrenceVariable Variable))
    (localIndex : Nat)
    (incidenceAtom : incidence.literal.atom = atom) :
    (incidence.numericRouteDescriptor (formula source)
        (PeriodicCNF.presentationLiteralCount source + localIndex)).targetPortRank =
      1 + @List.count (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq atom
          (((cycleLinkIncidences source).map
            (fun cycleIncidence => cycleIncidence.literal.atom)).take localIndex) := by
  have copiedLength :
      (allOccurrenceVariables source).length =
        PeriodicCNF.presentationLiteralCount source := by
    simp [allOccurrenceVariables]
  have copiedCount :
      @List.count (ThreeOccurrenceVariable Variable)
        instBEqOfDecidableEq atom
        (allOccurrenceVariables source) = 1 := by
    exact @List.count_eq_one_of_mem
      (ThreeOccurrenceVariable Variable) instBEqOfDecidableEq
      (by infer_instance)
      _ _ (allOccurrenceVariables_nodup source) atomMember
  simp only [CNFIncidence.numericRouteDescriptor]
  rw [incidenceAtom,
    formula_variableOccurrences_eq_copied_append_cycleLinkAtoms,
    ← copiedLength, List.take_length_add_append,
    @List.count_append (ThreeOccurrenceVariable Variable)
      instBEqOfDecidableEq,
    copiedCount]

/-- Filtering the globally indexed cycle-link incidence stream to one copied
occurrence yields numeric target ranks one and two, in that order. -/
theorem cycleLinkIncidenceNumericTargetRanks_fiber_eq_one_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source) :
    (((cycleLinkIncidences source).zipIdx
          (PeriodicCNF.presentationLiteralCount source)).flatMap
        fun taggedIncidence =>
          if taggedIncidence.1.literal.atom = atom then
            [(taggedIncidence.1.numericRouteDescriptor
              (formula source) taggedIncidence.2).targetPortRank]
          else []) = [1, 2] := by
  let incidences := cycleLinkIncidences source
  let atoms := incidences.map
    (fun incidence => incidence.literal.atom)
  have twiceStructural :
      @List.count (ThreeOccurrenceVariable Variable) instBEqProd atom atoms =
        2 := by
    dsimp [atoms, incidences]
    rw [cycleLinkIncidences_atoms_eq_cycleOccurrences]
    exact allCycleClauses_count_eq_two_of_mem_allOccurrenceVariables
      source atom atomMember
  have twice :
      @List.count (ThreeOccurrenceVariable Variable)
          instBEqOfDecidableEq atom atoms = 2 := by
    rw [← occurrenceVariable_count_eq_decidable']
    exact twiceStructural
  rw [List.zipIdx_eq_map_add, List.flatMap_map]
  calc
    _ = (incidences.zipIdx.flatMap fun taggedIncidence =>
          if taggedIncidence.1.literal.atom = atom then
            [1 + @List.count (ThreeOccurrenceVariable Variable)
              instBEqOfDecidableEq atom
                (atoms.take taggedIncidence.2)]
          else []) := by
      apply List.flatMap_congr
      intro taggedIncidence _taggedMember
      by_cases incidenceAtom : taggedIncidence.1.literal.atom = atom
      · rw [if_pos incidenceAtom, if_pos incidenceAtom]
        congr 1
        exact cycleLinkIncidence_numericTargetRank_eq_one_add_prefixCount
          source atom atomMember taggedIncidence.1 taggedIncidence.2
            incidenceAtom
      · simp [incidenceAtom]
    _ = [1, 2] :=
      indexedPrefixCount_fiber_eq_one_two incidences
        (fun incidence => incidence.literal.atom) atom twice

end LeanTrominoes.PeriodicThreeSATThree
