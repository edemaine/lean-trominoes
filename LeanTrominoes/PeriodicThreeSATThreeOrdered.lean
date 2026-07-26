import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-!
# Geometrically ordered periodic occurrence splitting

For a planar embedding, the implication cycle replacing a high-degree
variable must visit its occurrence copies in their cyclic order around the
old variable vertex.  Clause-presentation order need not have that property.

This file parameterizes the standard periodic 3SAT-3 construction by an
arbitrary per-variable permutation of the genuine syntactic occurrences.
The Boolean reduction is insensitive to that permutation: every such order
preserves satisfiability exactly.  A later geometric layer can therefore sort
the copies by their incident edge directions without changing the reduction.
-/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- A chosen ordering of each source variable's genuine occurrence copies. -/
structure OccurrenceOrder {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) where
  copies : Variable → List (ThreeOccurrenceVariable Variable)
  perm : ∀ atom, (copies atom).Perm (occurrenceVariables source atom)

namespace OccurrenceOrder

/-- The original clause-presentation order is one valid occurrence order. -/
def presentation {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : OccurrenceOrder source where
  copies := occurrenceVariables source
  perm := fun _atom => List.Perm.refl _

/-- A chosen order contains exactly the genuine copies of its source atom. -/
theorem mem_iff {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (atom : Variable) (copy : ThreeOccurrenceVariable Variable) :
    copy ∈ order.copies atom ↔
      copy ∈ occurrenceVariables source atom :=
  (order.perm atom).mem_iff

/-- Every copy in a chosen order belongs to the named source variable. -/
theorem copy_fst {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (atom : Variable) {copy : ThreeOccurrenceVariable Variable}
    (member : copy ∈ order.copies atom) :
    copy.1 = atom :=
  occurrenceVariables_fst source atom
    ((order.mem_iff atom copy).mp member)

/-- Chosen occurrence orders remain duplicate-free. -/
theorem copies_nodup {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source) (atom : Variable) :
    (order.copies atom).Nodup :=
  (order.perm atom).nodup_iff.mpr
    (occurrenceVariables_nodup source atom)

end OccurrenceOrder

/-- All implication cycles using a geometry-selected per-variable order. -/
def orderedCycleClauses {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  (sourceVariables source).flatMap fun atom =>
    cycleClauses (order.copies atom)

/-- Occurrence splitting with geometry-selected implication-cycle orders. -/
def orderedFormula {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source) :
    PeriodicCNF (ThreeOccurrenceVariable Variable) where
  clauses := occurrenceClauses source ++
    orderedCycleClauses source order

/-- The ordered construction specializes definitionally to the original
construction when clause-presentation order is selected. -/
@[simp]
theorem orderedFormula_presentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    orderedFormula source (OccurrenceOrder.presentation source) =
      formula source := by
  rfl

/-- Read a source value from the first copy in the geometry-selected order. -/
def orderedRestrictAssignment
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell =>
    ((order.copies atom).head?.map fun occurrence =>
      assignment occurrence cell).getD false

/-- Extending a source assignment satisfies every implication cycle in any
valid occurrence order. -/
theorem orderedCycleClauses_complete
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (atom : Variable) :
    ∀ clause ∈ cycleClauses (order.copies atom),
      clause.Holds (extendAssignment assignment) cell := by
  cases copiesEq : order.copies atom with
  | nil =>
      simp [cycleClauses]
  | cons first rest =>
      have firstOriginal : first.1 = atom :=
        order.copy_fst atom
          (copiesEq ▸ List.mem_cons_self)
      have restOriginal :
          ∀ copy ∈ rest, copy.1 = atom := by
        intro copy copyMem
        exact order.copy_fst atom
          (copiesEq ▸ List.mem_cons_of_mem first copyMem)
      simpa [copiesEq, cycleClauses] using
        cycleFrom_complete assignment cell atom first first rest
          firstOriginal firstOriginal restOriginal

/-- Extending any satisfying source assignment satisfies the fully ordered
occurrence-split formula. -/
theorem orderedFormula_satisfies_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (assignment : Variable → Cell → Bool)
    (satisfies : source.Satisfies assignment) :
    (orderedFormula source order).Satisfies
      (extendAssignment assignment) := by
  intro translate clause clauseMem
  simp only [orderedFormula, List.mem_append] at clauseMem
  rcases clauseMem with sourceMem | cycleMem
  · simp only [occurrenceClauses, List.mem_map] at sourceMem
    rcases sourceMem with
      ⟨taggedClause, taggedClauseMem, rfl⟩
    exact occurrenceClause_complete assignment translate
      taggedClause.2 taggedClause.1
      (satisfies translate taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMem))
  · simp only [orderedCycleClauses,
      List.mem_flatMap] at cycleMem
    rcases cycleMem with ⟨atom, atomMem, cycleMem⟩
    exact orderedCycleClauses_complete
      source order assignment translate atom clause cycleMem

/-- A satisfying ordered cycle makes its first copy agree with every other
copy in the same chosen order. -/
theorem orderedRestrictAssignment_eq_copy
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies : (orderedFormula source order).Satisfies assignment)
    (atom : Variable) (atomMem : atom ∈ sourceVariables source)
    (cell : Cell) (copy : ThreeOccurrenceVariable Variable)
    (copyMem : copy ∈ order.copies atom) :
    orderedRestrictAssignment source order assignment atom cell =
      assignment copy cell := by
  cases copiesEq : order.copies atom with
  | nil =>
      simp [copiesEq] at copyMem
  | cons first rest =>
      have cycleSatisfies :
          ∀ clause ∈ cycleClauses (first :: rest),
            clause.Holds assignment cell := by
        intro clause clauseMem
        apply satisfies cell clause
        simp only [orderedFormula, List.mem_append]
        apply Or.inr
        simp only [orderedCycleClauses, List.mem_flatMap]
        exact ⟨atom, atomMem,
          by simpa [copiesEq] using clauseMem⟩
      have copyEqFirst :=
        cycleClauses_value_eq_first assignment cell first rest
          cycleSatisfies copy
            (by simpa [copiesEq] using copyMem)
      simp only [orderedRestrictAssignment, copiesEq,
        List.head?_cons, Option.map_some, Option.getD_some]
      exact copyEqFirst.symm

/-- A copied literal has the same truth value as its source literal under
restriction through any valid occurrence order. -/
theorem occurrenceLiteral_holds_orderedRestrict
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies : (orderedFormula source order).Satisfies assignment)
    (translate : Cell) (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable)
    (taggedMem : (literal, clauseIndex, literalIndex) ∈
      taggedLiterals source) :
    (occurrenceLiteral clauseIndex literalIndex literal).Holds
        assignment translate ↔
      literal.Holds
        (orderedRestrictAssignment source order assignment)
        translate := by
  have atomMem := sourceVariables_mem source taggedMem
  have originalCopyMem := occurrenceVariables_mem source taggedMem
  have orderedCopyMem :
      (literal.atom, clauseIndex, literalIndex) ∈
        order.copies literal.atom :=
    (order.mem_iff literal.atom
      (literal.atom, clauseIndex, literalIndex)).mpr
      originalCopyMem
  have valuesEq :=
    orderedRestrictAssignment_eq_copy source order assignment
      satisfies literal.atom atomMem
      (Cell.add translate literal.offset)
      (literal.atom, clauseIndex, literalIndex)
      orderedCopyMem
  simp only [PeriodicLiteral.Holds, occurrenceLiteral]
  rw [valuesEq]

/-- Restricting a satisfying assignment of an ordered occurrence split
satisfies the original formula. -/
theorem satisfies_of_orderedFormula_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (assignment : ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies : (orderedFormula source order).Satisfies assignment) :
    source.Satisfies
      (orderedRestrictAssignment source order assignment) := by
  intro translate clause clauseMem
  have mappedMem :
      clause ∈ source.clauses.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using clauseMem
  rcases List.mem_map.mp mappedMem with
    ⟨⟨taggedClause, clauseIndex⟩,
      taggedClauseMem, taggedClauseEq⟩
  simp only at taggedClauseEq
  subst taggedClause
  have occurrenceHolds :
      (occurrenceClause clauseIndex clause).Holds
        assignment translate := by
    apply satisfies translate
      (occurrenceClause clauseIndex clause)
    simp only [orderedFormula, List.mem_append]
    apply Or.inl
    simp only [occurrenceClauses, List.mem_map]
    exact
      ⟨(clause, clauseIndex), taggedClauseMem, rfl⟩
  rcases occurrenceHolds with
    ⟨copiedLiteral, copiedLiteralMem,
      copiedLiteralHolds⟩
  simp only [occurrenceClause, List.mem_map] at copiedLiteralMem
  rcases copiedLiteralMem with
    ⟨⟨literal, literalIndex⟩,
      taggedLiteralMem, rfl⟩
  refine
    ⟨literal,
      List.fst_mem_of_mem_zipIdx taggedLiteralMem, ?_⟩
  apply
    (occurrenceLiteral_holds_orderedRestrict
      source order assignment satisfies translate
      clauseIndex literalIndex literal ?_).mp
  · exact copiedLiteralHolds
  · exact taggedLiterals_mem source
      taggedClauseMem taggedLiteralMem

/-- Every permutation of the genuine occurrence copies gives an equivalent
periodic satisfiability instance. -/
theorem orderedSatisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source) :
    source.Satisfiable ↔
      (orderedFormula source order).Satisfiable := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨extendAssignment assignment,
        orderedFormula_satisfies_of_satisfies
          source order assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨orderedRestrictAssignment source order assignment,
        satisfies_of_orderedFormula_satisfies
          source order assignment satisfies⟩

/-! ## Clause width -/

/-- Geometry-ordered occurrence splitting preserves a width-three bound. -/
theorem orderedFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (order : OccurrenceOrder source)
    (width : source.WidthAtMost 3) :
    (orderedFormula source order).WidthAtMost 3 := by
  intro clause clauseMem
  simp only [orderedFormula, List.mem_append] at clauseMem
  rcases clauseMem with sourceMem | cycleMem
  · simp only [occurrenceClauses, List.mem_map] at sourceMem
    rcases sourceMem with
      ⟨taggedClause, taggedClauseMem, rfl⟩
    rw [PeriodicClause.WidthAtMost, occurrenceClause_length]
    exact width taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMem)
  · simp only [orderedCycleClauses,
      List.mem_flatMap] at cycleMem
    rcases cycleMem with ⟨atom, _atomMem, cycleMem⟩
    exact cycleClauses_widthAtMostThree
      (order.copies atom) clause cycleMem

/-! ## Occurrence bound -/

/-- Every literal in one ordered cycle still belongs to the variable whose
copy list generated that cycle. -/
theorem orderedCycle_occurrences_fst
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (atom : Variable) :
    ∀ copy ∈ PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk
          (cycleClauses (order.copies atom))),
      copy.1 = atom := by
  cases copiesEq : order.copies atom with
  | nil =>
      simp [cycleClauses, PeriodicCNF.variableOccurrences]
  | cons first rest =>
      have firstOriginal : first.1 = atom :=
        order.copy_fst atom
          (copiesEq ▸ List.mem_cons_self)
      have restOriginal :
          ∀ copy ∈ rest, copy.1 = atom := by
        intro copy copyMem
        exact order.copy_fst atom
          (copiesEq ▸ List.mem_cons_of_mem first copyMem)
      simpa [copiesEq, cycleClauses] using
        cycleFrom_occurrences_fst atom first first rest
          firstOriginal firstOriginal restOriginal

/-- A copy whose original variable differs from the cycle owner does not
occur in that ordered cycle. -/
theorem orderedCycle_count_eq_zero_of_fst_ne
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (different : copy.1 ≠ atom) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (cycleClauses (order.copies atom)))).count copy = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro copyMem
  exact different
    (orderedCycle_occurrences_fst
      source order atom copy copyMem)

/-- Ordered cycles generated for an explicit list of source variables. -/
def orderedCyclesFor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (atoms : List Variable) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  atoms.flatMap fun atom =>
    cycleClauses (order.copies atom)

/-- Across an explicit variable list, an occurrence copy appears at most
twice for each appearance of its original variable. -/
theorem orderedCyclesFor_count_le
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (atoms : List Variable)
    (copy : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (orderedCyclesFor source order atoms))).count copy ≤
      2 * atoms.count copy.1 := by
  induction atoms with
  | nil =>
      simp [orderedCyclesFor,
        PeriodicCNF.variableOccurrences]
  | cons atom atoms induction =>
      rw [show orderedCyclesFor source order (atom :: atoms) =
        cycleClauses (order.copies atom) ++
          orderedCyclesFor source order atoms by rfl]
      rw [variableOccurrences_append, List.count_append]
      by_cases same : copy.1 = atom
      · have headLe :
            (PeriodicCNF.variableOccurrences
              (PeriodicCNF.mk
                (cycleClauses
                  (order.copies atom)))).count copy ≤ 2 :=
          cycleClauses_count_le_two
            (order.copies atom)
            (order.copies_nodup atom) copy
        have headCount :
            (atom :: atoms).count copy.1 =
              atoms.count copy.1 + 1 := by
          subst atom
          exact List.count_cons_self
        rw [headCount]
        omega
      · rw [orderedCycle_count_eq_zero_of_fst_ne
          source order atom copy same, zero_add]
        have headCount :
            (atom :: atoms).count copy.1 =
              atoms.count copy.1 :=
          List.count_cons_of_ne
            (fun equal => same equal.symm)
        rw [headCount]
        exact induction

/-- Every copy occurs at most twice among all geometry-ordered implication
cycles. -/
theorem orderedCycleClauses_count_le_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source)
    (copy : ThreeOccurrenceVariable Variable) :
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (orderedCycleClauses source order))).count copy ≤ 2 := by
  have sourceVariablesNodup :
      (sourceVariables source).Nodup :=
    List.nodup_dedup _
  have atomCountLeOne :=
    (List.nodup_iff_count_le_one.mp
      sourceVariablesNodup) copy.1
  have cyclesLe :=
    orderedCyclesFor_count_le source order
      (sourceVariables source) copy
  have actualLe :
      (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk
          (orderedCycleClauses source order))).count copy ≤
        2 * (sourceVariables source).count copy.1 := by
    simpa [orderedCycleClauses,
      orderedCyclesFor] using cyclesLe
  omega

/-- Geometry-ordered occurrence splitting retains the 3SAT-3 occurrence
bound: one copied source literal and at most two implication literals. -/
theorem orderedFormula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (order : OccurrenceOrder source) :
    (orderedFormula source order).OccurrencesAtMost 3 := by
  intro copy
  have sourceLe :=
    occurrenceClauses_count_le_one source copy
  have cyclesLe :=
    orderedCycleClauses_count_le_two
      source order copy
  change
    (PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (occurrenceClauses source ++
          orderedCycleClauses source order))).count copy ≤ 3
  rw [variableOccurrences_append, List.count_append]
  omega

end PeriodicThreeSATThree
end LeanTrominoes
