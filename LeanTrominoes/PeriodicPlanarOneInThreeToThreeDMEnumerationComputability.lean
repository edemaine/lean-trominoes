import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTyped
import LeanTrominoes.PeriodicOneInThreeToThreeDMEnumerationComputability

/-!
# Computability of the planar exact-one to 3DM enumeration

The Dyer--Frieze planar construction is finite and completely explicit.
This module gives primitive-recursive encodings to its typed elements and
triples, and proves that the finite color classes and triple list can be
computed from the source periodic exact-one formula.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

@[reducible] private noncomputable def finitePrimcodable
    (T : Type*) [Fintype T] :
    Primcodable T :=
  Primcodable.ofEquiv (Fin (Fintype.card T)) (Fintype.equivFin T)

noncomputable instance : Primcodable VariableOccurrenceVariant :=
  finitePrimcodable VariableOccurrenceVariant

noncomputable instance : Primcodable VariableOccurrenceTriple :=
  finitePrimcodable VariableOccurrenceTriple

noncomputable instance : Primcodable VariableOccurrenceElement :=
  finitePrimcodable VariableOccurrenceElement

noncomputable instance : Primcodable VariableConnectorKind :=
  finitePrimcodable VariableConnectorKind

noncomputable instance : Primcodable FixedRedConnectorTriple :=
  finitePrimcodable FixedRedConnectorTriple

noncomputable instance : Primcodable FixedRedConnectorRed :=
  finitePrimcodable FixedRedConnectorRed

noncomputable instance : Primcodable FixedRedConnectorGreen :=
  finitePrimcodable FixedRedConnectorGreen

noncomputable instance : Primcodable FixedRedConnectorBlue :=
  finitePrimcodable FixedRedConnectorBlue

noncomputable instance : Primcodable X3CClauseSet :=
  finitePrimcodable X3CClauseSet

noncomputable instance : Primcodable X3CClauseInternal :=
  finitePrimcodable X3CClauseInternal

noncomputable instance : Primcodable X3CClauseTerminalGroup :=
  finitePrimcodable X3CClauseTerminalGroup

noncomputable instance : Primcodable X3CClauseTerminalSlot :=
  finitePrimcodable X3CClauseTerminalSlot

def x3cClauseTerminalEquivData :
    X3CClauseTerminal ≃
      X3CClauseTerminalGroup × X3CClauseTerminalSlot where
  toFun terminal := (terminal.group, terminal.slot)
  invFun data := ⟨data.1, data.2⟩
  left_inv terminal := by cases terminal; rfl
  right_inv data := by rcases data with ⟨group, slot⟩; rfl

noncomputable instance : Primcodable X3CClauseTerminal :=
  Primcodable.ofEquiv _ x3cClauseTerminalEquivData

def x3cClauseElementEquivData :
    X3CClauseElement ≃ Sum X3CClauseInternal X3CClauseTerminal where
  toFun
    | .internal value => .inl value
    | .terminal value => .inr value
  invFun
    | .inl value => .internal value
    | .inr value => .terminal value
  left_inv element := by cases element <;> rfl
  right_inv data := by rcases data with data | data <;> rfl

noncomputable instance : Primcodable X3CClauseElement :=
  Primcodable.ofEquiv _ x3cClauseElementEquivData

noncomputable instance : Primcodable OrdinaryInternal :=
  finitePrimcodable OrdinaryInternal

noncomputable instance : Primcodable FixedRedInternalRed :=
  finitePrimcodable FixedRedInternalRed

noncomputable instance : Primcodable FixedRedInternalGreen :=
  finitePrimcodable FixedRedInternalGreen

noncomputable instance : Primcodable FixedRedInternalBlue :=
  finitePrimcodable FixedRedInternalBlue

/-! ## Primitive-recursive representations of the typed names -/

def redElementEquivData {Variable : Type*} :
    RedElement Variable ≃
      Sum (Variable × OccurrenceSlot)
        (Sum ((Variable × OccurrenceSlot) × FixedRedInternalRed)
          (Sum Nat (Nat × X3CClauseTerminalGroup))) where
  toFun
    | .cycleLink atom slot => .inl (atom, slot)
    | .fixedRedInternal atom slot element =>
        .inr (.inl ((atom, slot), element))
    | .clauseInternal clauseIndex => .inr (.inr (.inl clauseIndex))
    | .clauseTerminal clauseIndex group =>
        .inr (.inr (.inr (clauseIndex, group)))
  invFun
    | .inl data => .cycleLink data.1 data.2
    | .inr (.inl data) =>
        .fixedRedInternal data.1.1 data.1.2 data.2
    | .inr (.inr (.inl clauseIndex)) => .clauseInternal clauseIndex
    | .inr (.inr (.inr data)) => .clauseTerminal data.1 data.2
  left_inv element := by cases element <;> rfl
  right_inv data := by
    rcases data with data | data
    · rfl
    · rcases data with data | data
      · rfl
      · rcases data with data | data <;> rfl

noncomputable instance redElementPrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (RedElement Variable) :=
  Primcodable.ofEquiv _ redElementEquivData

def greenElementEquivData {Variable : Type*} :
    GreenElement Variable ≃
      Sum ((Variable × OccurrenceSlot) × OrdinaryInternal)
        (Sum ((Variable × OccurrenceSlot) × FixedRedInternalGreen)
          (Sum Nat (Nat × X3CClauseTerminalGroup))) where
  toFun
    | .ordinaryInternal atom slot element =>
        .inl ((atom, slot), element)
    | .fixedRedInternal atom slot element =>
        .inr (.inl ((atom, slot), element))
    | .clauseInternal clauseIndex => .inr (.inr (.inl clauseIndex))
    | .clauseTerminal clauseIndex group =>
        .inr (.inr (.inr (clauseIndex, group)))
  invFun
    | .inl data => .ordinaryInternal data.1.1 data.1.2 data.2
    | .inr (.inl data) =>
        .fixedRedInternal data.1.1 data.1.2 data.2
    | .inr (.inr (.inl clauseIndex)) => .clauseInternal clauseIndex
    | .inr (.inr (.inr data)) => .clauseTerminal data.1 data.2
  left_inv element := by cases element <;> rfl
  right_inv data := by
    rcases data with data | data
    · rfl
    · rcases data with data | data
      · rfl
      · rcases data with data | data <;> rfl

noncomputable instance greenElementPrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (GreenElement Variable) :=
  Primcodable.ofEquiv _ greenElementEquivData

def blueElementEquivData {Variable : Type*} :
    BlueElement Variable ≃
      Sum ((Variable × OccurrenceSlot) × OrdinaryInternal)
        (Sum ((Variable × OccurrenceSlot) × FixedRedInternalBlue)
          (Sum Nat (Nat × X3CClauseTerminalGroup))) where
  toFun
    | .ordinaryInternal atom slot element =>
        .inl ((atom, slot), element)
    | .fixedRedInternal atom slot element =>
        .inr (.inl ((atom, slot), element))
    | .clauseInternal clauseIndex => .inr (.inr (.inl clauseIndex))
    | .clauseTerminal clauseIndex group =>
        .inr (.inr (.inr (clauseIndex, group)))
  invFun
    | .inl data => .ordinaryInternal data.1.1 data.1.2 data.2
    | .inr (.inl data) =>
        .fixedRedInternal data.1.1 data.1.2 data.2
    | .inr (.inr (.inl clauseIndex)) => .clauseInternal clauseIndex
    | .inr (.inr (.inr data)) => .clauseTerminal data.1 data.2
  left_inv element := by cases element <;> rfl
  right_inv data := by
    rcases data with data | data
    · rfl
    · rcases data with data | data
      · rfl
      · rcases data with data | data <;> rfl

noncomputable instance blueElementPrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (BlueElement Variable) :=
  Primcodable.ofEquiv _ blueElementEquivData

def tripleEquivData {Variable : Type*} :
    Triple Variable ≃
      Sum (((Variable × OccurrenceSlot) × VariableOccurrenceVariant) ×
          VariableOccurrenceTriple)
        (Sum ((Variable × OccurrenceSlot) × FixedRedConnectorTriple)
          (Nat × X3CClauseSet)) where
  toFun
    | .ordinary atom slot variant triple =>
        .inl (((atom, slot), variant), triple)
    | .fixedRed atom slot triple => .inr (.inl ((atom, slot), triple))
    | .clause clauseIndex set => .inr (.inr (clauseIndex, set))
  invFun
    | .inl data =>
        .ordinary data.1.1.1 data.1.1.2 data.1.2 data.2
    | .inr (.inl data) => .fixedRed data.1.1 data.1.2 data.2
    | .inr (.inr data) => .clause data.1 data.2
  left_inv triple := by cases triple <;> rfl
  right_inv data := by
    rcases data with data | data
    · rfl
    · rcases data with data | data <;> rfl

noncomputable instance triplePrimcodable
    {Variable : Type*} [Primcodable Variable] :
    Primcodable (Triple Variable) :=
  Primcodable.ofEquiv _ tripleEquivData

theorem redElement_cycleLink_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : Variable × OccurrenceSlot =>
      RedElement.cycleLink data.1 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@redElementEquivData Variable).symm).comp Primrec.sumInl

theorem redElement_fixedRedInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (Variable × OccurrenceSlot) × FixedRedInternalRed =>
      RedElement.fixedRedInternal data.1.1 data.1.2 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@redElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp Primrec.sumInl)

theorem redElement_clauseInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (RedElement.clauseInternal : Nat → RedElement Variable) :=
  (Primrec.of_equiv_symm :
    Primrec (@redElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))

theorem redElement_clauseTerminal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : Nat × X3CClauseTerminalGroup =>
      RedElement.clauseTerminal (Variable := Variable) data.1 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@redElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr))

theorem greenElement_ordinaryInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : (Variable × OccurrenceSlot) × OrdinaryInternal =>
      GreenElement.ordinaryInternal data.1.1 data.1.2 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@greenElementEquivData Variable).symm).comp Primrec.sumInl

theorem greenElement_fixedRedInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (Variable × OccurrenceSlot) × FixedRedInternalGreen =>
      GreenElement.fixedRedInternal data.1.1 data.1.2 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@greenElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp Primrec.sumInl)

theorem greenElement_clauseInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (GreenElement.clauseInternal : Nat → GreenElement Variable) :=
  (Primrec.of_equiv_symm :
    Primrec (@greenElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))

theorem greenElement_clauseTerminal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : Nat × X3CClauseTerminalGroup =>
      GreenElement.clauseTerminal (Variable := Variable) data.1 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@greenElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr))

theorem blueElement_ordinaryInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : (Variable × OccurrenceSlot) × OrdinaryInternal =>
      BlueElement.ordinaryInternal data.1.1 data.1.2 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@blueElementEquivData Variable).symm).comp Primrec.sumInl

theorem blueElement_fixedRedInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (Variable × OccurrenceSlot) × FixedRedInternalBlue =>
      BlueElement.fixedRedInternal data.1.1 data.1.2 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@blueElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp Primrec.sumInl)

theorem blueElement_clauseInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (BlueElement.clauseInternal : Nat → BlueElement Variable) :=
  (Primrec.of_equiv_symm :
    Primrec (@blueElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))

theorem blueElement_clauseTerminal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : Nat × X3CClauseTerminalGroup =>
      BlueElement.clauseTerminal (Variable := Variable) data.1 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@blueElementEquivData Variable).symm).comp
      (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr))

theorem triple_ordinary_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        ((Variable × OccurrenceSlot) × VariableOccurrenceVariant) ×
          VariableOccurrenceTriple =>
      Triple.ordinary data.1.1.1 data.1.1.2 data.1.2 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@tripleEquivData Variable).symm).comp Primrec.sumInl

theorem triple_fixedRed_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (Variable × OccurrenceSlot) × FixedRedConnectorTriple =>
      Triple.fixedRed data.1.1 data.1.2 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@tripleEquivData Variable).symm).comp
      (Primrec.sumInr.comp Primrec.sumInl)

theorem triple_clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : Nat × X3CClauseSet =>
      Triple.clause (Variable := Variable) data.1 data.2 :=
  (Primrec.of_equiv_symm :
    Primrec (@tripleEquivData Variable).symm).comp
      (Primrec.sumInr.comp Primrec.sumInr)

/-! ## Source occurrence operations -/

theorem occurrencesOf_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data : PeriodicCNF Variable × Variable =>
      occurrencesOf data.1 data.2 := by
  simpa only [occurrencesOf] using
    (PeriodicOneInThreeToThreeDM.occurrencesOf_primrec
      (Variable := Variable))

theorem occurrenceAt_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      occurrenceAt data.1.1 data.1.2 data.2 := by
  simpa only [occurrenceAt] using
    (PeriodicOneInThreeToThreeDM.occurrenceAt_primrec
      (Variable := Variable))

theorem occurringVariables_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (occurringVariables :
      PeriodicCNF Variable → List Variable) := by
  exact
    (PeriodicOneInThreeToThreeDM.occurringVariables_primrec
      (Variable := Variable)).of_eq fun _ => rfl

theorem usedSlots_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data : PeriodicCNF Variable × Variable =>
      usedSlots data.1 data.2 := by
  have keep : Primrec₂ fun
      (data : PeriodicCNF Variable × Variable) (slot : OccurrenceSlot) =>
      if (occurrenceAt data.1 data.2 slot).isSome then some slot else none := by
    change Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      if (occurrenceAt data.1.1 data.1.2 data.2).isSome then
        some data.2
      else none
    have selected : PrimrecPred fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      (occurrenceAt data.1.1 data.1.2 data.2).isSome := by
      refine ⟨inferInstance, ?_⟩
      simpa using
        (Primrec.option_isSome.comp occurrenceAt_primrec)
    exact Primrec.ite selected
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.const none)
  exact (Primrec.listFilterMap
    (Primrec.const allOccurrenceSlots) keep).of_eq fun data => by
      unfold usedSlots
      generalize allOccurrenceSlots = slots
      induction slots with
      | nil => rfl
      | cons slot rest induction =>
          by_cases selected :
              (occurrenceAt data.1 data.2 slot).isSome
          · simp [selected, induction]
          · simp [selected, induction]

theorem occurrenceClauseIndex_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      occurrenceClauseIndex data.1.1 data.1.2 data.2 := by
  have someCase : Primrec₂ fun
      (_data : (PeriodicCNF Variable × Variable) × OccurrenceSlot)
      (tagged : TaggedOccurrence Variable) => tagged.2.1 :=
    (Primrec.fst.comp Primrec.snd).comp Primrec.snd
  exact (Primrec.option_casesOn occurrenceAt_primrec
    (Primrec.const 0) someCase).of_eq fun data => by
      generalize found : occurrenceAt data.1.1 data.1.2 data.2 = value
      cases value <;> simp [occurrenceClauseIndex, found]

theorem occurrenceLiteralIndex_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      occurrenceLiteralIndex data.1.1 data.1.2 data.2 := by
  have someCase : Primrec₂ fun
      (_data : (PeriodicCNF Variable × Variable) × OccurrenceSlot)
      (tagged : TaggedOccurrence Variable) => tagged.2.2 :=
    (Primrec.snd.comp Primrec.snd).comp Primrec.snd
  exact (Primrec.option_casesOn occurrenceAt_primrec
    (Primrec.const 0) someCase).of_eq fun data => by
      generalize found : occurrenceAt data.1.1 data.1.2 data.2 = value
      cases value <;> simp [occurrenceLiteralIndex, found]

theorem occurrenceConnectorKind_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      occurrenceConnectorKind data.1.1 data.1.2 data.2 := by
  have zero : PrimrecPred fun n : Nat => n = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  have one : PrimrecPred fun n : Nat => n = 1 :=
    Primrec.eq.comp Primrec.id (Primrec.const 1)
  have finite : Primrec connectorKindOfLiteralIndex :=
    (Primrec.ite zero
      (Primrec.const VariableConnectorKind.fixedRed)
      (Primrec.ite one
        (Primrec.const VariableConnectorKind.fixedBlue)
        (Primrec.const VariableConnectorKind.fixedGreen))).of_eq
      fun n => by
        rcases n with _ | _ | n <;> rfl
  exact (finite.comp occurrenceLiteralIndex_primrec).of_eq
    fun data => rfl

/-! ## Finite triple and color-class enumerations -/

theorem occurrenceTriples_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun data :
        (PeriodicCNF Variable × Variable) × OccurrenceSlot =>
      occurrenceTriples data.1.1 data.1.2 data.2 := by
  let Input :=
    (PeriodicCNF Variable × Variable) × OccurrenceSlot
  have atomSlot : Primrec fun data : Input =>
      (data.1.2, data.2) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  have fixedRed : Primrec fun data : Input =>
      allFixedRedTriples.map
        (Triple.fixedRed data.1.2 data.2) := by
    have row : Primrec₂ fun (data : Input)
        (triple : FixedRedConnectorTriple) =>
        Triple.fixedRed data.1.2 data.2 triple :=
      triple_fixedRed_primrec.comp
        (Primrec.pair (atomSlot.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_map
      (Primrec.const allFixedRedTriples) row
  have ordinary (variant : VariableOccurrenceVariant) :
      Primrec fun data : Input =>
        allOrdinaryTriples.map
          (Triple.ordinary data.1.2 data.2 variant) := by
    have row : Primrec₂ fun (data : Input)
        (triple : VariableOccurrenceTriple) =>
        Triple.ordinary data.1.2 data.2 variant triple :=
      triple_ordinary_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (atomSlot.comp Primrec.fst)
            (Primrec.const variant))
          Primrec.snd)
    exact Primrec.list_map
      (Primrec.const allOrdinaryTriples) row
  have kind : Primrec fun data : Input =>
      occurrenceConnectorKind data.1.1 data.1.2 data.2 :=
    occurrenceConnectorKind_primrec
  have isRed : PrimrecPred fun data : Input =>
      occurrenceConnectorKind data.1.1 data.1.2 data.2 =
        VariableConnectorKind.fixedRed :=
    Primrec.eq.comp kind
      (Primrec.const VariableConnectorKind.fixedRed)
  have isGreen : PrimrecPred fun data : Input =>
      occurrenceConnectorKind data.1.1 data.1.2 data.2 =
        VariableConnectorKind.fixedGreen :=
    Primrec.eq.comp kind
      (Primrec.const VariableConnectorKind.fixedGreen)
  exact (Primrec.ite isRed fixedRed
    (Primrec.ite isGreen (ordinary .fixedGreen)
      (ordinary .fixedBlue))).of_eq fun data => by
        unfold occurrenceTriples
        cases occurrenceConnectorKind data.1.1 data.1.2 data.2 <;>
          rfl

theorem variableTriples_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (variableTriples :
      PeriodicCNF Variable → List (Triple Variable)) := by
  have slots : Primrec fun data : PeriodicCNF Variable × Variable =>
      (usedSlots data.1 data.2).flatMap fun slot =>
        occurrenceTriples data.1 data.2 slot :=
    Primrec.list_flatMap usedSlots_primrec
      occurrenceTriples_primrec.to₂
  exact Primrec.list_flatMap occurringVariables_primrec slots.to₂

theorem clauseTriples_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (clauseTriples :
      PeriodicCNF Variable → List (Triple Variable)) := by
  have indices : Primrec fun source : PeriodicCNF Variable =>
      List.range source.clauses.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp PeriodicCNF.equivData_primrec)
  have row : Primrec₂ fun (_source : PeriodicCNF Variable)
      (clauseIndex : Nat) =>
      allClauseSets.map (Triple.clause (Variable := Variable) clauseIndex) := by
    change Primrec fun data : PeriodicCNF Variable × Nat =>
      allClauseSets.map (Triple.clause (Variable := Variable) data.2)
    have one : Primrec₂ fun
        (data : PeriodicCNF Variable × Nat) (set : X3CClauseSet) =>
        Triple.clause (Variable := Variable) data.2 set :=
      triple_clause_primrec.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_map (Primrec.const allClauseSets) one
  exact Primrec.list_flatMap indices row

theorem triples_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (triples :
      PeriodicCNF Variable → List (Triple Variable)) := by
  exact Primrec.list_append.comp variableTriples_primrec clauseTriples_primrec

theorem redElements_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (redElements :
      PeriodicCNF Variable → List (RedElement Variable)) := by
  let Input :=
    (PeriodicCNF Variable × Variable) × OccurrenceSlot
  have atomSlot : Primrec fun data : Input =>
      (data.1.2, data.2) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  have cycle : Primrec fun data : Input =>
      RedElement.cycleLink data.1.2 data.2 :=
    redElement_cycleLink_primrec.comp atomSlot
  have internals : Primrec fun data : Input =>
      [RedElement.fixedRedInternal data.1.2 data.2
          FixedRedInternalRed.middleRung,
        RedElement.fixedRedInternal data.1.2 data.2
          FixedRedInternalRed.topAuxiliary] := by
    have one : Primrec₂ fun (data : Input)
        (element : FixedRedInternalRed) =>
        RedElement.fixedRedInternal data.1.2 data.2 element :=
      redElement_fixedRedInternal_primrec.comp
        (Primrec.pair (atomSlot.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_map
      (Primrec.const
        [FixedRedInternalRed.middleRung,
          FixedRedInternalRed.topAuxiliary]) one
  have isFixedRed : PrimrecPred fun data : Input =>
      occurrenceConnectorKind data.1.1 data.1.2 data.2 =
        VariableConnectorKind.fixedRed :=
    Primrec.eq.comp occurrenceConnectorKind_primrec
      (Primrec.const VariableConnectorKind.fixedRed)
  have occurrence : Primrec fun data : Input =>
      occurrenceRedElements data.1.1 data.1.2 data.2 :=
    (Primrec.list_cons.comp cycle
      (Primrec.ite isFixedRed internals (Primrec.const []))).of_eq
      fun data => by
        unfold occurrenceRedElements
        cases occurrenceConnectorKind data.1.1 data.1.2 data.2 <;>
          rfl
  have slots : Primrec fun data : PeriodicCNF Variable × Variable =>
      (usedSlots data.1 data.2).flatMap fun slot =>
        occurrenceRedElements data.1 data.2 slot :=
    Primrec.list_flatMap usedSlots_primrec occurrence.to₂
  have variablePart : Primrec fun source : PeriodicCNF Variable =>
      (occurringVariables source).flatMap fun atom =>
        (usedSlots source atom).flatMap fun slot =>
          occurrenceRedElements source atom slot :=
    Primrec.list_flatMap occurringVariables_primrec slots.to₂
  have indices : Primrec fun source : PeriodicCNF Variable =>
      List.range source.clauses.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp PeriodicCNF.equivData_primrec)
  have clauseRow : Primrec₂ fun (_source : PeriodicCNF Variable)
      (clauseIndex : Nat) =>
      [RedElement.clauseInternal (Variable := Variable) clauseIndex] ++
        allTerminalGroups.map
          (RedElement.clauseTerminal (Variable := Variable) clauseIndex) := by
    change Primrec fun data : PeriodicCNF Variable × Nat =>
      [RedElement.clauseInternal (Variable := Variable) data.2] ++
        allTerminalGroups.map
          (RedElement.clauseTerminal (Variable := Variable) data.2)
    have internal : Primrec fun data : PeriodicCNF Variable × Nat =>
        RedElement.clauseInternal (Variable := Variable) data.2 :=
      redElement_clauseInternal_primrec.comp Primrec.snd
    have terminal : Primrec₂ fun (data : PeriodicCNF Variable × Nat)
        (group : X3CClauseTerminalGroup) =>
        RedElement.clauseTerminal (Variable := Variable) data.2 group :=
      redElement_clauseTerminal_primrec.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_append.comp
      (Primrec.list_cons.comp internal (Primrec.const []))
      (Primrec.list_map (Primrec.const allTerminalGroups) terminal)
  exact Primrec.list_append.comp variablePart
    (Primrec.list_flatMap indices clauseRow)

theorem greenElements_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (greenElements :
      PeriodicCNF Variable → List (GreenElement Variable)) := by
  let Input :=
    (PeriodicCNF Variable × Variable) × OccurrenceSlot
  have atomSlot : Primrec fun data : Input =>
      (data.1.2, data.2) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  have ordinary : Primrec fun data : Input =>
      [GreenElement.ordinaryInternal data.1.2 data.2
        OrdinaryInternal.cycleShared] :=
    Primrec.list_cons.comp
      (greenElement_ordinaryInternal_primrec.comp
        (Primrec.pair atomSlot
          (Primrec.const OrdinaryInternal.cycleShared)))
      (Primrec.const [])
  have fixedRed : Primrec fun data : Input =>
      [GreenElement.fixedRedInternal data.1.2 data.2
          FixedRedInternalGreen.leftRung,
        GreenElement.fixedRedInternal data.1.2 data.2
          FixedRedInternalGreen.topRightLink,
        GreenElement.fixedRedInternal data.1.2 data.2
          FixedRedInternalGreen.bottomRightLink] := by
    have one : Primrec₂ fun (data : Input)
        (element : FixedRedInternalGreen) =>
        GreenElement.fixedRedInternal data.1.2 data.2 element :=
      greenElement_fixedRedInternal_primrec.comp
        (Primrec.pair (atomSlot.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_map
      (Primrec.const
        [FixedRedInternalGreen.leftRung,
          FixedRedInternalGreen.topRightLink,
          FixedRedInternalGreen.bottomRightLink]) one
  have isFixedRed : PrimrecPred fun data : Input =>
      occurrenceConnectorKind data.1.1 data.1.2 data.2 =
        VariableConnectorKind.fixedRed :=
    Primrec.eq.comp occurrenceConnectorKind_primrec
      (Primrec.const VariableConnectorKind.fixedRed)
  have occurrence : Primrec fun data : Input =>
      occurrenceGreenElements data.1.1 data.1.2 data.2 :=
    (Primrec.ite isFixedRed fixedRed ordinary).of_eq fun data => by
      unfold occurrenceGreenElements
      cases occurrenceConnectorKind data.1.1 data.1.2 data.2 <;> rfl
  have slots : Primrec fun data : PeriodicCNF Variable × Variable =>
      (usedSlots data.1 data.2).flatMap fun slot =>
        occurrenceGreenElements data.1 data.2 slot :=
    Primrec.list_flatMap usedSlots_primrec occurrence.to₂
  have variablePart : Primrec fun source : PeriodicCNF Variable =>
      (occurringVariables source).flatMap fun atom =>
        (usedSlots source atom).flatMap fun slot =>
          occurrenceGreenElements source atom slot :=
    Primrec.list_flatMap occurringVariables_primrec slots.to₂
  have indices : Primrec fun source : PeriodicCNF Variable =>
      List.range source.clauses.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp PeriodicCNF.equivData_primrec)
  have clauseRow : Primrec₂ fun (_source : PeriodicCNF Variable)
      (clauseIndex : Nat) =>
      [GreenElement.clauseInternal (Variable := Variable) clauseIndex] ++
        allTerminalGroups.map
          (GreenElement.clauseTerminal (Variable := Variable) clauseIndex) := by
    change Primrec fun data : PeriodicCNF Variable × Nat =>
      [GreenElement.clauseInternal (Variable := Variable) data.2] ++
        allTerminalGroups.map
          (GreenElement.clauseTerminal (Variable := Variable) data.2)
    have internal : Primrec fun data : PeriodicCNF Variable × Nat =>
        GreenElement.clauseInternal (Variable := Variable) data.2 :=
      greenElement_clauseInternal_primrec.comp Primrec.snd
    have terminal : Primrec₂ fun (data : PeriodicCNF Variable × Nat)
        (group : X3CClauseTerminalGroup) =>
        GreenElement.clauseTerminal (Variable := Variable) data.2 group :=
      greenElement_clauseTerminal_primrec.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_append.comp
      (Primrec.list_cons.comp internal (Primrec.const []))
      (Primrec.list_map (Primrec.const allTerminalGroups) terminal)
  exact Primrec.list_append.comp variablePart
    (Primrec.list_flatMap indices clauseRow)

theorem blueElements_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (blueElements :
      PeriodicCNF Variable → List (BlueElement Variable)) := by
  let Input :=
    (PeriodicCNF Variable × Variable) × OccurrenceSlot
  have atomSlot : Primrec fun data : Input =>
      (data.1.2, data.2) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd
  have ordinary : Primrec fun data : Input =>
      [BlueElement.ordinaryInternal data.1.2 data.2
        OrdinaryInternal.auxiliaryShared] :=
    Primrec.list_cons.comp
      (blueElement_ordinaryInternal_primrec.comp
        (Primrec.pair atomSlot
          (Primrec.const OrdinaryInternal.auxiliaryShared)))
      (Primrec.const [])
  have fixedRed : Primrec fun data : Input =>
      [BlueElement.fixedRedInternal data.1.2 data.2
          FixedRedInternalBlue.topLeftLink,
        BlueElement.fixedRedInternal data.1.2 data.2
          FixedRedInternalBlue.bottomLeftLink,
        BlueElement.fixedRedInternal data.1.2 data.2
          FixedRedInternalBlue.rightRung] := by
    have one : Primrec₂ fun (data : Input)
        (element : FixedRedInternalBlue) =>
        BlueElement.fixedRedInternal data.1.2 data.2 element :=
      blueElement_fixedRedInternal_primrec.comp
        (Primrec.pair (atomSlot.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_map
      (Primrec.const
        [FixedRedInternalBlue.topLeftLink,
          FixedRedInternalBlue.bottomLeftLink,
          FixedRedInternalBlue.rightRung]) one
  have isFixedRed : PrimrecPred fun data : Input =>
      occurrenceConnectorKind data.1.1 data.1.2 data.2 =
        VariableConnectorKind.fixedRed :=
    Primrec.eq.comp occurrenceConnectorKind_primrec
      (Primrec.const VariableConnectorKind.fixedRed)
  have occurrence : Primrec fun data : Input =>
      occurrenceBlueElements data.1.1 data.1.2 data.2 :=
    (Primrec.ite isFixedRed fixedRed ordinary).of_eq fun data => by
      unfold occurrenceBlueElements
      cases occurrenceConnectorKind data.1.1 data.1.2 data.2 <;> rfl
  have slots : Primrec fun data : PeriodicCNF Variable × Variable =>
      (usedSlots data.1 data.2).flatMap fun slot =>
        occurrenceBlueElements data.1 data.2 slot :=
    Primrec.list_flatMap usedSlots_primrec occurrence.to₂
  have variablePart : Primrec fun source : PeriodicCNF Variable =>
      (occurringVariables source).flatMap fun atom =>
        (usedSlots source atom).flatMap fun slot =>
          occurrenceBlueElements source atom slot :=
    Primrec.list_flatMap occurringVariables_primrec slots.to₂
  have indices : Primrec fun source : PeriodicCNF Variable =>
      List.range source.clauses.length :=
    Primrec.list_range.comp
      (Primrec.list_length.comp PeriodicCNF.equivData_primrec)
  have clauseRow : Primrec₂ fun (_source : PeriodicCNF Variable)
      (clauseIndex : Nat) =>
      [BlueElement.clauseInternal (Variable := Variable) clauseIndex] ++
        allTerminalGroups.map
          (BlueElement.clauseTerminal (Variable := Variable) clauseIndex) := by
    change Primrec fun data : PeriodicCNF Variable × Nat =>
      [BlueElement.clauseInternal (Variable := Variable) data.2] ++
        allTerminalGroups.map
          (BlueElement.clauseTerminal (Variable := Variable) data.2)
    have internal : Primrec fun data : PeriodicCNF Variable × Nat =>
        BlueElement.clauseInternal (Variable := Variable) data.2 :=
      blueElement_clauseInternal_primrec.comp Primrec.snd
    have terminal : Primrec₂ fun (data : PeriodicCNF Variable × Nat)
        (group : X3CClauseTerminalGroup) =>
        BlueElement.clauseTerminal (Variable := Variable) data.2 group :=
      blueElement_clauseTerminal_primrec.comp
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst) Primrec.snd)
    exact Primrec.list_append.comp
      (Primrec.list_cons.comp internal (Primrec.const []))
      (Primrec.list_map (Primrec.const allTerminalGroups) terminal)
  exact Primrec.list_append.comp variablePart
    (Primrec.list_flatMap indices clauseRow)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
