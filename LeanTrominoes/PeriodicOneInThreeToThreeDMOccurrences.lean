import LeanTrominoes.PeriodicOneInThreeToThreeDMSemantics
import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-!
# Occurrence-slot bookkeeping for the periodic 3DM reduction

Each variable gadget exposes three pairs of complementary blue ports.  This
file proves that presentation-order lookup assigns every tagged literal to
exactly one such pair whenever each variable occurs at most three times.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

namespace OccurrenceSlot

/-- The port in a slot that carries the variable's `true` phase. -/
def trueTriple : OccurrenceSlot → PlanarThreeDM.VariableTriple
  | .first => .topLeft
  | .second => .rightMiddle
  | .third => .bottomLeft

/-- The complementary port in a slot, carrying the `false` phase. -/
def falseTriple : OccurrenceSlot → PlanarThreeDM.VariableTriple
  | .first => .topRight
  | .second => .bottomRight
  | .third => .leftMiddle

@[simp]
theorem variableTripleSlot_trueTriple (slot : OccurrenceSlot) :
    variableTripleSlot slot.trueTriple = slot := by
  cases slot <;> rfl

@[simp]
theorem variableTripleSlot_falseTriple (slot : OccurrenceSlot) :
    variableTripleSlot slot.falseTriple = slot := by
  cases slot <;> rfl

@[simp]
theorem variableTripleValue_trueTriple (slot : OccurrenceSlot) :
    variableTripleValue slot.trueTriple = true := by
  cases slot <;> rfl

@[simp]
theorem variableTripleValue_falseTriple (slot : OccurrenceSlot) :
    variableTripleValue slot.falseTriple = false := by
  cases slot <;> rfl

theorem index_injective : Function.Injective OccurrenceSlot.index := by
  intro left right
  cases left <;> cases right <;> simp [index]

end OccurrenceSlot

/-- Forgetting literals and atoms from the tagged presentation leaves the
strictly ordered clause/literal position list. -/
theorem taggedLiterals_positions {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (PeriodicThreeSATThree.taggedLiterals source).map
        (fun tagged => (tagged.2.1, tagged.2.2)) =
      PeriodicThreeSATThree.occurrenceIndicesFrom 0 source.clauses := by
  rw [PeriodicThreeSATThree.occurrenceIndicesFrom_eq]
  simp [PeriodicThreeSATThree.taggedLiterals, List.map_flatMap,
    Function.comp_def]

/-- Tagged occurrences are pairwise distinct because their clause/literal
positions are pairwise distinct. -/
theorem taggedLiterals_nodup {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (PeriodicThreeSATThree.taggedLiterals source).Nodup := by
  apply List.Nodup.of_map (fun tagged => (tagged.2.1, tagged.2.2))
  rw [taggedLiterals_positions]
  exact
    PeriodicThreeSATThree.occurrenceIndicesFrom_nodup 0 source.clauses

/-- Filtering to one atom preserves distinctness of tagged occurrences. -/
theorem occurrencesOf_nodup {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    (occurrencesOf source atom).Nodup := by
  exact (taggedLiterals_nodup source).filter _

/-- The atom projection of tagged literals is the ordinary occurrence list. -/
theorem taggedLiterals_atoms {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (PeriodicThreeSATThree.taggedLiterals source).map
        (fun tagged => tagged.1.atom) =
      PeriodicCNF.variableOccurrences source := by
  have clauseMap (clause : PeriodicClause Variable) :
      (clause.zipIdx.map fun tagged => tagged.1.atom) =
        clause.map PeriodicLiteral.atom := by
    have mapped := congrArg (List.map PeriodicLiteral.atom)
      (List.zipIdx_map_fst 0 clause)
    simpa only [List.map_map, Function.comp_def] using mapped
  have helper (clauses : List (PeriodicClause Variable)) (start : Nat) :
      (((clauses.zipIdx start).flatMap fun taggedClause =>
          taggedClause.1.zipIdx.map fun taggedLiteral =>
            (taggedLiteral.1, taggedClause.2, taggedLiteral.2)).map
          (fun tagged => tagged.1.atom)) =
        clauses.flatMap fun clause =>
          clause.map PeriodicLiteral.atom := by
    induction clauses generalizing start with
    | nil => rfl
    | cons clause rest induction =>
        simp [Function.comp_def, induction, clauseMap]
  exact helper source.clauses 0

/-- Filtering tagged literals to one atom has the expected occurrence count. -/
theorem occurrencesOf_length {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    (occurrencesOf source atom).length =
      (PeriodicCNF.variableOccurrences source).count atom := by
  rw [← taggedLiterals_atoms source]
  unfold occurrencesOf
  generalize
    PeriodicThreeSATThree.taggedLiterals source = taggedOccurrences
  induction taggedOccurrences with
  | nil => rfl
  | cons tagged rest induction =>
      by_cases same : tagged.1.atom = atom
      · simp [same, induction]
      · simp [same, induction]

/-- Reaching the third occurrence slot certifies that the variable really
occurs at least three times. -/
theorem three_le_variableOccurrences_count_of_occurrenceAt_third
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom .third = some tagged) :
    3 ≤ (PeriodicCNF.variableOccurrences source).count atom := by
  rw [occurrenceAt, List.getElem?_eq_some_iff] at lookup
  rcases lookup with ⟨indexLt, _⟩
  rw [← occurrencesOf_length]
  simp only [OccurrenceSlot.index] at indexLt
  omega

/-- Any member of a list of length at most three occupies one of the three
enumerated occurrence slots. -/
theorem exists_slot_getElem?_eq_some {α : Type*} (values : List α)
    (value : α) (member : value ∈ values) (length : values.length ≤ 3) :
    ∃ slot : OccurrenceSlot,
      values[slot.index]? = some value := by
  rcases values with _ | ⟨first, rest⟩
  · simp at member
  · rcases rest with _ | ⟨second, rest⟩
    · simp only [List.mem_singleton] at member
      subst value
      exact ⟨.first, rfl⟩
    · rcases rest with _ | ⟨third, rest⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨.first, rfl⟩
        · exact ⟨.second, rfl⟩
      · have restNil : rest = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [List.length_cons] at length
          omega
        subst rest
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact ⟨.first, rfl⟩
        · exact ⟨.second, rfl⟩
        · exact ⟨.third, rfl⟩

/-- Under the occurrence-three restriction, every tagged literal is assigned
to one of the variable gadget's three occurrence slots. -/
theorem exists_occurrenceSlot {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    ∃ slot : OccurrenceSlot,
      occurrenceAt source tagged.1.atom slot = some tagged := by
  apply exists_slot_getElem?_eq_some
  · exact List.mem_filter.mpr ⟨member, by simp⟩
  · rw [occurrencesOf_length]
    exact occurrences tagged.1.atom

/-- A successful slot lookup came from the tagged presentation and names the
requested atom. -/
theorem occurrenceAt_mem_and_atom {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    tagged ∈ PeriodicThreeSATThree.taggedLiterals source ∧
      tagged.1.atom = atom := by
  have filtered :
      tagged ∈ occurrencesOf source atom :=
    List.mem_iff_getElem?.mpr ⟨slot.index, lookup⟩
  rcases List.mem_filter.mp filtered with ⟨member, atomEq⟩
  exact ⟨member, by simpa using atomEq⟩

/-- A tagged literal cannot occupy two different slots of one variable
gadget. -/
theorem occurrenceAt_slot_unique {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (tagged : TaggedOccurrence Variable)
    (firstSlot secondSlot : OccurrenceSlot)
    (firstAt : occurrenceAt source atom firstSlot = some tagged)
    (secondAt : occurrenceAt source atom secondSlot = some tagged) :
    firstSlot = secondSlot := by
  rw [occurrenceAt, List.getElem?_eq_some_iff] at firstAt secondAt
  rcases firstAt with ⟨firstLt, firstEq⟩
  rcases secondAt with ⟨secondLt, secondEq⟩
  apply OccurrenceSlot.index_injective
  apply
    ((occurrencesOf_nodup source atom).getElem_inj_iff
      (hi := firstLt) (hj := secondLt)).mp
  exact firstEq.trans secondEq.symm

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
