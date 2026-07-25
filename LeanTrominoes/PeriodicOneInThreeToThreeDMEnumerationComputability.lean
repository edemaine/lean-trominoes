import LeanTrominoes.PeriodicOneInThreeToThreeDMTyped
import LeanTrominoes.PeriodicThreeDMComputability
import LeanTrominoes.PeriodicOneInThreeReductionComputability

/-!
# Computability of the typed periodic 3DM enumeration

This file proves primitive recursiveness of the finite color classes and
triple list in the exact-one to periodic 3DM construction.  The reference
calculation and final natural-number encoding are handled separately.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

noncomputable instance : Primcodable OccurrenceSlot :=
  Primcodable.ofEquiv (Fin (Fintype.card OccurrenceSlot))
    (Fintype.equivFin OccurrenceSlot)

noncomputable instance : Primcodable PlanarThreeDM.VariableTriple :=
  Primcodable.ofEquiv
    (Fin (Fintype.card PlanarThreeDM.VariableTriple))
    (Fintype.equivFin PlanarThreeDM.VariableTriple)

noncomputable instance : Primcodable PlanarThreeDM.VariableRed :=
  Primcodable.ofEquiv
    (Fin (Fintype.card PlanarThreeDM.VariableRed))
    (Fintype.equivFin PlanarThreeDM.VariableRed)

noncomputable instance : Primcodable PlanarThreeDM.VariableGreen :=
  Primcodable.ofEquiv
    (Fin (Fintype.card PlanarThreeDM.VariableGreen))
    (Fintype.equivFin PlanarThreeDM.VariableGreen)

/-- Sum representation of typed red elements. -/
def redElementEquivData {Variable : Type*} :
    RedElement Variable ≃
      Sum (Variable × PlanarThreeDM.VariableRed) Nat where
  toFun
    | .variable atom element => .inl (atom, element)
    | .clause clauseIndex => .inr clauseIndex
  invFun
    | .inl data => .variable data.1 data.2
    | .inr clauseIndex => .clause clauseIndex
  left_inv element := by cases element <;> rfl
  right_inv data := by rcases data with data | data <;> rfl

noncomputable instance redElementPrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (RedElement Variable) :=
  Primcodable.ofEquiv
    (Sum (Variable × PlanarThreeDM.VariableRed) Nat)
    redElementEquivData

theorem redElement_variable_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Variable × PlanarThreeDM.VariableRed =>
      RedElement.variable input.1 input.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@redElementEquivData Variable).symm).comp
      Primrec.sumInl

theorem redElement_clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (RedElement.clause :
      Nat → RedElement Variable) :=
  (Primrec.of_equiv_symm :
    Primrec (@redElementEquivData Variable).symm).comp
      Primrec.sumInr

/-- Sum representation of typed green elements. -/
def greenElementEquivData {Variable : Type*} :
    GreenElement Variable ≃
      Sum (Variable × PlanarThreeDM.VariableGreen) Nat where
  toFun
    | .variable atom element => .inl (atom, element)
    | .clause clauseIndex => .inr clauseIndex
  invFun
    | .inl data => .variable data.1 data.2
    | .inr clauseIndex => .clause clauseIndex
  left_inv element := by cases element <;> rfl
  right_inv data := by rcases data with data | data <;> rfl

noncomputable instance greenElementPrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (GreenElement Variable) :=
  Primcodable.ofEquiv
    (Sum (Variable × PlanarThreeDM.VariableGreen) Nat)
    greenElementEquivData

theorem greenElement_variable_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Variable × PlanarThreeDM.VariableGreen =>
      GreenElement.variable input.1 input.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@greenElementEquivData Variable).symm).comp
      Primrec.sumInl

theorem greenElement_clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (GreenElement.clause :
      Nat → GreenElement Variable) :=
  (Primrec.of_equiv_symm :
    Primrec (@greenElementEquivData Variable).symm).comp
      Primrec.sumInr

/-- Nested-sum representation of typed blue elements. -/
def blueElementEquivData {Variable : Type*} :
    BlueElement Variable ≃
      Sum Nat
        (Sum (Nat × Nat) (Variable × OccurrenceSlot)) where
  toFun
    | .clause clauseIndex => .inl clauseIndex
    | .complement clauseIndex literalIndex =>
        .inr (.inl (clauseIndex, literalIndex))
    | .unused atom slot => .inr (.inr (atom, slot))
  invFun
    | .inl clauseIndex => .clause clauseIndex
    | .inr (.inl data) => .complement data.1 data.2
    | .inr (.inr data) => .unused data.1 data.2
  left_inv element := by cases element <;> rfl
  right_inv data := by
    rcases data with data | data
    · rfl
    · rcases data with data | data <;> rfl

noncomputable instance blueElementPrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (BlueElement Variable) :=
  Primcodable.ofEquiv
    (Sum Nat
      (Sum (Nat × Nat) (Variable × OccurrenceSlot)))
    blueElementEquivData

theorem blueElement_clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (BlueElement.clause :
      Nat → BlueElement Variable) :=
  (Primrec.of_equiv_symm :
    Primrec (@blueElementEquivData Variable).symm).comp
      Primrec.sumInl

theorem blueElement_complement_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × Nat =>
      BlueElement.complement (Variable := Variable)
        input.1 input.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@blueElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp Primrec.sumInl)

theorem blueElement_unused_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Variable × OccurrenceSlot =>
      BlueElement.unused input.1 input.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@blueElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp Primrec.sumInr)

/-- Sum representation of typed triples. -/
def tripleEquivData {Variable : Type*} :
    Triple Variable ≃
      Sum (Variable × PlanarThreeDM.VariableTriple)
        (Nat × Nat) where
  toFun
    | .variable atom triple => .inl (atom, triple)
    | .clauseAuxiliary clauseIndex literalIndex =>
        .inr (clauseIndex, literalIndex)
  invFun
    | .inl data => .variable data.1 data.2
    | .inr data => .clauseAuxiliary data.1 data.2
  left_inv triple := by cases triple <;> rfl
  right_inv data := by rcases data with data | data <;> rfl

noncomputable instance triplePrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (Triple Variable) :=
  Primcodable.ofEquiv
    (Sum (Variable × PlanarThreeDM.VariableTriple)
      (Nat × Nat))
    tripleEquivData

theorem triple_variable_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Variable × PlanarThreeDM.VariableTriple =>
      Triple.variable input.1 input.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@tripleEquivData Variable).symm).comp
      Primrec.sumInl

theorem triple_clauseAuxiliary_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Nat × Nat =>
      Triple.clauseAuxiliary (Variable := Variable)
        input.1 input.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@tripleEquivData Variable).symm).comp
      Primrec.sumInr

theorem occurrenceSlot_index_primrec :
    Primrec OccurrenceSlot.index :=
  Primrec.dom_finite OccurrenceSlot.index

theorem occurrencesOf_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable × Variable =>
      occurrencesOf input.1 input.2 := by
  have tagged :
      Primrec fun input : PeriodicCNF Variable × Variable =>
        PeriodicThreeSATThree.taggedLiterals input.1 :=
    PeriodicThreeSATThree.taggedLiterals_primrec.comp
      Primrec.fst
  have keep : Primrec₂ fun
      (input : PeriodicCNF Variable × Variable)
      (item : TaggedOccurrence Variable) =>
      if item.1.atom = input.2 then some item else none := by
    change Primrec fun combined :
        (PeriodicCNF Variable × Variable) ×
          TaggedOccurrence Variable =>
      if combined.2.1.atom = combined.1.2 then
        some combined.2
      else none
    have same : PrimrecPred fun combined :
        (PeriodicCNF Variable × Variable) ×
          TaggedOccurrence Variable =>
        combined.2.1.atom = combined.1.2 :=
      Primrec.eq.comp
        (PeriodicThreeCNF.literal_atom_primrec.comp
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    exact Primrec.ite same
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)
  exact (Primrec.listFilterMap tagged keep).of_eq
    fun input => by
      unfold occurrencesOf
      generalize
        PeriodicThreeSATThree.taggedLiterals input.1 =
          items
      induction items with
      | nil => rfl
      | cons item rest induction =>
          by_cases same : item.1.atom = input.2 <;>
            simp [same, induction]

theorem occurrenceAt_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec fun input :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      occurrenceAt input.1.1 input.1.2 input.2 := by
  exact Primrec.list_getElem?.comp
    (occurrencesOf_primrec.comp Primrec.fst)
    (occurrenceSlot_index_primrec.comp Primrec.snd)

theorem variableOccurrences_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (PeriodicCNF.variableOccurrences :
      PeriodicCNF Variable → List Variable) := by
  have row : Primrec₂ fun (_source : PeriodicCNF Variable)
      (clause : PeriodicClause Variable) =>
      clause.map PeriodicLiteral.atom := by
    change Primrec fun combined :
        PeriodicCNF Variable × PeriodicClause Variable =>
      combined.2.map PeriodicLiteral.atom
    exact Primrec.list_map Primrec.snd
      (PeriodicThreeCNF.literal_atom_primrec.comp
        Primrec.snd).to₂
  exact Primrec.list_flatMap
    PeriodicCNF.equivData_primrec row

theorem occurringVariables_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec (occurringVariables :
      PeriodicCNF Variable → List Variable) :=
  PeriodicThreeSATThree.dedup_primrec.comp
    variableOccurrences_primrec

theorem variableTriples_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec (variableTriples :
      PeriodicCNF Variable → List (Triple Variable)) := by
  have row : Primrec₂ fun (_source : PeriodicCNF Variable)
      (atom : Variable) =>
      allVariableTriples.map (Triple.variable atom) := by
    change Primrec fun combined :
        PeriodicCNF Variable × Variable =>
      allVariableTriples.map
        (Triple.variable combined.2)
    exact Primrec.list_map
      (Primrec.const allVariableTriples)
      (triple_variable_primrec.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          Primrec.snd)).to₂
  exact Primrec.list_flatMap occurringVariables_primrec row

theorem clauseAuxiliaryTriples_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (clauseAuxiliaryTriples :
      PeriodicCNF Variable → List (Triple Variable)) := by
  exact Primrec.list_map
    PeriodicThreeSATThree.taggedLiterals_primrec
    ((triple_clauseAuxiliary_primrec
      (Variable := Variable)).comp
      (Primrec.snd.comp Primrec.snd)).to₂

theorem triples_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec (triples :
      PeriodicCNF Variable → List (Triple Variable)) :=
  Primrec.list_append.comp
    variableTriples_primrec
    clauseAuxiliaryTriples_primrec

theorem redElements_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec (redElements :
      PeriodicCNF Variable → List (RedElement Variable)) := by
  have variablePart :
      Primrec fun source : PeriodicCNF Variable =>
      (occurringVariables source).flatMap fun atom =>
        allVariableReds.map (RedElement.variable atom) := by
    have row : Primrec₂ fun (_source : PeriodicCNF Variable)
        (atom : Variable) =>
        allVariableReds.map (RedElement.variable atom) := by
      change Primrec fun combined :
          PeriodicCNF Variable × Variable =>
        allVariableReds.map
          (RedElement.variable combined.2)
      exact Primrec.list_map
        (Primrec.const allVariableReds)
        (redElement_variable_primrec.comp
          (Primrec.pair
            (Primrec.snd.comp Primrec.fst)
            Primrec.snd)).to₂
    exact Primrec.list_flatMap occurringVariables_primrec row
  have clauseIndices :
      Primrec fun source : PeriodicCNF Variable =>
        List.range source.clauses.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp
        PeriodicCNF.equivData_primrec)
  have clausePart :
      Primrec fun source : PeriodicCNF Variable =>
        (List.range source.clauses.length).map
          RedElement.clause :=
    Primrec.list_map clauseIndices
      ((redElement_clause_primrec
        (Variable := Variable)).comp Primrec.snd).to₂
  exact Primrec.list_append.comp variablePart clausePart

theorem greenElements_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec (greenElements :
      PeriodicCNF Variable → List (GreenElement Variable)) := by
  have variablePart :
      Primrec fun source : PeriodicCNF Variable =>
      (occurringVariables source).flatMap fun atom =>
        allVariableGreens.map
          (GreenElement.variable atom) := by
    have row : Primrec₂ fun (_source : PeriodicCNF Variable)
        (atom : Variable) =>
        allVariableGreens.map
          (GreenElement.variable atom) := by
      change Primrec fun combined :
          PeriodicCNF Variable × Variable =>
        allVariableGreens.map
          (GreenElement.variable combined.2)
      exact Primrec.list_map
        (Primrec.const allVariableGreens)
        (greenElement_variable_primrec.comp
          (Primrec.pair
            (Primrec.snd.comp Primrec.fst)
            Primrec.snd)).to₂
    exact Primrec.list_flatMap occurringVariables_primrec row
  have clauseIndices :
      Primrec fun source : PeriodicCNF Variable =>
        List.range source.clauses.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp
        PeriodicCNF.equivData_primrec)
  have clausePart :
      Primrec fun source : PeriodicCNF Variable =>
        (List.range source.clauses.length).map
          GreenElement.clause :=
    Primrec.list_map clauseIndices
      ((greenElement_clause_primrec
        (Variable := Variable)).comp Primrec.snd).to₂
  exact Primrec.list_append.comp variablePart clausePart

theorem unusedSlots_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec (unusedSlots :
      PeriodicCNF Variable →
        List (Variable × OccurrenceSlot)) := by
  have row : Primrec₂ fun (source : PeriodicCNF Variable)
      (atom : Variable) =>
      OccurrenceSlot.all.filterMap fun slot =>
        if (occurrenceAt source atom slot).isNone then
          some (atom, slot)
        else none := by
    change Primrec fun input :
        PeriodicCNF Variable × Variable =>
      OccurrenceSlot.all.filterMap fun slot =>
        if (occurrenceAt input.1 input.2 slot).isNone then
          some (input.2, slot)
        else none
    have select : Primrec₂ fun
        (input : PeriodicCNF Variable × Variable)
        (slot : OccurrenceSlot) =>
        if (occurrenceAt input.1 input.2 slot).isNone then
          some (input.2, slot)
        else none := by
      change Primrec fun combined :
          (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
        if (occurrenceAt combined.1.1 combined.1.2
          combined.2).isNone then
          some (combined.1.2, combined.2)
        else none
      have occurrence :
          Primrec fun combined :
              (PeriodicCNF Variable × Variable) ×
                OccurrenceSlot =>
            occurrenceAt combined.1.1 combined.1.2
              combined.2 :=
        occurrenceAt_primrec
      have selected :
          Primrec fun combined :
              (PeriodicCNF Variable × Variable) ×
                OccurrenceSlot =>
            some (combined.1.2, combined.2) :=
        Primrec.option_some.comp
          (Primrec.pair
            (Primrec.snd.comp Primrec.fst)
            Primrec.snd)
      exact
        (Primrec.option_casesOn occurrence selected
          (Primrec.const none).to₂).of_eq fun combined => by
            cases occurrenceAt combined.1.1
              combined.1.2 combined.2 <;> rfl
    exact Primrec.listFilterMap
      (Primrec.const OccurrenceSlot.all) select
  exact Primrec.list_flatMap occurringVariables_primrec row

theorem blueElements_primrec
    {Variable : Type*} [Primcodable Variable]
    [DecidableEq Variable] :
    Primrec (blueElements :
      PeriodicCNF Variable → List (BlueElement Variable)) := by
  have clauseIndices :
      Primrec fun source : PeriodicCNF Variable =>
        List.range source.clauses.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp
        PeriodicCNF.equivData_primrec)
  have clauses :
      Primrec fun source : PeriodicCNF Variable =>
        (List.range source.clauses.length).map
          BlueElement.clause :=
    Primrec.list_map clauseIndices
      ((blueElement_clause_primrec
        (Variable := Variable)).comp Primrec.snd).to₂
  have complements :
      Primrec fun source : PeriodicCNF Variable =>
        (PeriodicThreeSATThree.taggedLiterals source).map
          fun tagged =>
            BlueElement.complement tagged.2.1
              tagged.2.2 :=
    Primrec.list_map
      PeriodicThreeSATThree.taggedLiterals_primrec
      ((blueElement_complement_primrec
        (Variable := Variable)).comp
        (Primrec.snd.comp Primrec.snd)).to₂
  have unused :
      Primrec fun source : PeriodicCNF Variable =>
        (unusedSlots source).map fun tagged =>
          BlueElement.unused tagged.1 tagged.2 :=
    Primrec.list_map unusedSlots_primrec
      (blueElement_unused_primrec.comp Primrec.snd).to₂
  exact Primrec.list_append.comp
    (Primrec.list_append.comp clauses complements) unused

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
