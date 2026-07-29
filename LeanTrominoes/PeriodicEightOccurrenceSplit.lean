import LeanTrominoes.OccurrenceSplitRingDrawing
import LeanTrominoes.PeriodicThreeSATThreeCorrectness

/-!
# Fixed eight-slot periodic occurrence splitting

The geometric Figure 7 neighborhood has one source copy at every multiple
of 45 degrees, plus one degree-two separator copy.  Real source occurrences
occupy their incident-ray slots; unused slots and the separator remain
harmless degree-two variables on the implication cycle.

Keeping all eight source slots makes the geometry uniform across variable
degrees.  The separator supplies a cut at which the cyclic implications can
be presented linearly without reversing the clockwise occurrence order of
any source copy.
This file proves the semantic part independently of the eventual geometric
slot classifier: every assignment of syntactic occurrences to compass slots
gives an equisatisfiable formula.  The later degree proof will require that
two occurrences of the same source variable never choose the same slot.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

/-- Numeric coordinates for the eight compass slots inside the established
`ThreeOccurrenceVariable` representation. -/
def portIndex : Port → Nat
  | .northwest => 0
  | .north => 1
  | .northeast => 2
  | .east => 3
  | .southeast => 4
  | .south => 5
  | .southwest => 6
  | .west => 7

/-- A syntactic clause/literal occurrence chooses one compass slot. -/
structure OccurrencePorts where
  port : Nat → Nat → Port

/-- The fixed occurrence copy belonging to one atom and compass slot. -/
def copy {Variable : Type*}
    (atom : Variable) (port : Port) :
    ThreeOccurrenceVariable Variable :=
  (atom, portIndex port, 0)

/-- Rename a local ring vertex to its source-port copy or the fresh
degree-two separator copy. -/
def ringCopy {Variable : Type*}
    (atom : Variable) :
    OccurrenceSplitRing.RingVertex →
      ThreeOccurrenceVariable Variable
  | .separator => (atom, 8, 0)
  | .port port => copy atom port

/-- Recover the geometric ring vertex from the numeric copy index.  Indices
outside the eight source ports denote the separator. -/
def ringVertexOfIndex : Nat → OccurrenceSplitRing.RingVertex
  | 0 => .port .northwest
  | 1 => .port .north
  | 2 => .port .northeast
  | 3 => .port .east
  | 4 => .port .southeast
  | 5 => .port .south
  | 6 => .port .southwest
  | 7 => .port .west
  | _ => .separator

@[simp]
theorem ringVertexOfIndex_portIndex (port : Port) :
    ringVertexOfIndex (portIndex port) = .port port := by
  cases port <;> rfl

/-- All nine implication-ring copies in clockwise order, cut at the
separator. -/
def copies {Variable : Type*}
    (atom : Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  OccurrenceSplitRing.cycleVertices.map (ringCopy atom)

/-- Replace one source literal by the copy in its selected compass slot. -/
def occurrenceLiteral {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable) :
    PeriodicLiteral (ThreeOccurrenceVariable Variable) :=
  ⟨copy literal.atom
      (occurrencePorts.port clauseIndex literalIndex),
    literal.offset, literal.value⟩

/-- Replace every literal of one source clause by its selected fixed-slot
copy. -/
def occurrenceClause {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (clauseIndex : Nat)
    (clause : PeriodicClause Variable) :
    PeriodicClause (ThreeOccurrenceVariable Variable) :=
  clause.zipIdx.map fun taggedLiteral =>
    occurrenceLiteral occurrencePorts clauseIndex
      taggedLiteral.2 taggedLiteral.1

/-- All copied source clauses. -/
def occurrenceClauses {Variable : Type*}
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  source.clauses.zipIdx.map fun taggedClause =>
    occurrenceClause occurrencePorts taggedClause.2 taggedClause.1

/-- The full separator implication cycle of one source atom.  Reversing its
clause presentation makes the outgoing clockwise implication precede the
incoming implication at every real source port. -/
def cycleClausesFor {Variable : Type*}
    (atom : Variable) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  (PeriodicThreeSATThree.cycleClauses (copies atom)).reverse

/-- One fixed implication ring for every source atom that occurs. -/
def allCycleClauses {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicClause (ThreeOccurrenceVariable Variable)) :=
  (PeriodicThreeSATThree.sourceVariables source).flatMap cycleClausesFor

/-- Fixed-eight occurrence splitting. -/
def formula {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts) :
    PeriodicCNF (ThreeOccurrenceVariable Variable) where
  clauses :=
    occurrenceClauses source occurrencePorts ++
      allCycleClauses source

theorem occurrenceClause_length
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (clauseIndex : Nat)
    (clause : PeriodicClause Variable) :
    (occurrenceClause occurrencePorts clauseIndex clause).length =
      clause.length := by
  simp [occurrenceClause]

theorem occurrenceLiteral_offsetDistance
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat)
    (first second : PeriodicLiteral Variable) :
    PeriodicClause.offsetDistance
        (occurrenceLiteral occurrencePorts
          firstClauseIndex firstLiteralIndex first)
        (occurrenceLiteral occurrencePorts
          secondClauseIndex secondLiteralIndex second) =
      PeriodicClause.offsetDistance first second := by
  rfl

theorem occurrenceClause_isLocal
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (clauseIndex : Nat)
    {clause : PeriodicClause Variable}
    (sourceLocal : clause.IsLocal) :
    (occurrenceClause occurrencePorts
      clauseIndex clause).IsLocal := by
  intro first firstMember second secondMember
  simp only [occurrenceClause, List.mem_map] at firstMember secondMember
  rcases firstMember with
    ⟨firstTagged, firstTaggedMember, rfl⟩
  rcases secondMember with
    ⟨secondTagged, secondTaggedMember, rfl⟩
  rw [occurrenceLiteral_offsetDistance]
  exact sourceLocal firstTagged.1
    (List.fst_mem_of_mem_zipIdx firstTaggedMember)
    secondTagged.1
    (List.fst_mem_of_mem_zipIdx secondTaggedMember)

theorem cycleClausesFor_areLocal
    {Variable : Type*}
    (atom : Variable) :
    ∀ clause ∈ cycleClausesFor atom, clause.IsLocal :=
    by
  intro clause clauseMember
  exact
    PeriodicThreeSATThree.cycleClauses_areLocal
      (copies atom) clause
      (List.mem_reverse.mp clauseMember)

/-- Fixed-eight occurrence splitting preserves the paper's locality
condition. -/
theorem formula_isLocal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (occurrencePorts : OccurrencePorts)
    (sourceLocal : source.IsLocal) :
    (formula source occurrencePorts).IsLocal := by
  intro clause clauseMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with sourceMember | cycleMember
  · simp only [occurrenceClauses, List.mem_map] at sourceMember
    rcases sourceMember with
      ⟨taggedClause, taggedClauseMember, rfl⟩
    exact occurrenceClause_isLocal occurrencePorts
      taggedClause.2
      (sourceLocal taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMember))
  · simp only [allCycleClauses,
      List.mem_flatMap] at cycleMember
    rcases cycleMember with
      ⟨atom, _atomMember, cycleMember⟩
    exact cycleClausesFor_areLocal atom clause cycleMember

theorem cycleClausesFor_widthAtMostThree
    {Variable : Type*}
    (atom : Variable) :
    ∀ clause ∈ cycleClausesFor atom,
      clause.WidthAtMost 3 :=
    by
  intro clause clauseMember
  exact
    PeriodicThreeSATThree.cycleClauses_widthAtMostThree
      (copies atom) clause
      (List.mem_reverse.mp clauseMember)

/-- Fixed-eight occurrence splitting preserves a width-three bound. -/
theorem formula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (occurrencePorts : OccurrencePorts)
    (sourceWidth : source.WidthAtMost 3) :
    (formula source occurrencePorts).WidthAtMost 3 := by
  intro clause clauseMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with sourceMember | cycleMember
  · simp only [occurrenceClauses, List.mem_map] at sourceMember
    rcases sourceMember with
      ⟨taggedClause, taggedClauseMember, rfl⟩
    rw [PeriodicClause.WidthAtMost,
      occurrenceClause_length]
    exact sourceWidth taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)
  · simp only [allCycleClauses,
      List.mem_flatMap] at cycleMember
    rcases cycleMember with
      ⟨atom, _atomMember, cycleMember⟩
    exact cycleClausesFor_widthAtMostThree
      atom clause cycleMember

/-- Read a source value from the first fixed compass copy. -/
def restrictAssignment {Variable : Type*}
    (assignment :
      ThreeOccurrenceVariable Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell =>
    ((copies atom).head?.map fun occurrence =>
      assignment occurrence cell).getD false

@[simp]
theorem occurrenceLiteral_holds_extend
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable) :
    (occurrenceLiteral occurrencePorts clauseIndex literalIndex literal).Holds
        (PeriodicThreeSATThree.extendAssignment assignment) translate ↔
      literal.Holds assignment translate := by
  rfl

/-- Extending a source assignment satisfies every copied source clause. -/
theorem occurrenceClause_complete
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (sourceHolds : clause.Holds assignment translate) :
    (occurrenceClause occurrencePorts clauseIndex clause).Holds
      (PeriodicThreeSATThree.extendAssignment assignment) translate := by
  rcases sourceHolds with
    ⟨literal, literalMember, literalHolds⟩
  have mappedMember :
      literal ∈ clause.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using literalMember
  rcases List.mem_map.mp mappedMember with
    ⟨⟨taggedLiteral, literalIndex⟩,
      taggedMember, taggedEqual⟩
  simp only at taggedEqual
  subst taggedLiteral
  refine
    ⟨occurrenceLiteral occurrencePorts clauseIndex
        literalIndex literal, ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨(literal, literalIndex), taggedMember, rfl⟩
  · exact
      (occurrenceLiteral_holds_extend occurrencePorts assignment
        translate clauseIndex literalIndex literal).mpr
        literalHolds

/-- Every copy in the fixed ring retains the named source atom. -/
theorem copy_fst
    {Variable : Type*}
    (atom : Variable)
    {occurrence : ThreeOccurrenceVariable Variable}
    (occurrenceMember : occurrence ∈ copies atom) :
    occurrence.1 = atom := by
  rcases List.mem_map.mp occurrenceMember with
    ⟨vertex, vertexMember, occurrenceEqual⟩
  subst occurrence
  cases vertex <;> rfl

/-- Extending a source assignment satisfies the fixed implication ring. -/
theorem cycleClausesFor_complete
    {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (atom : Variable) :
    ∀ clause ∈ cycleClausesFor atom,
      clause.Holds
        (PeriodicThreeSATThree.extendAssignment assignment) cell := by
  cases copiesEqual : copies atom with
  | nil =>
      simp [cycleClausesFor, copiesEqual,
        PeriodicThreeSATThree.cycleClauses]
  | cons first rest =>
      have firstOriginal : first.1 = atom :=
        copy_fst atom (copiesEqual ▸ List.mem_cons_self)
      have restOriginal :
          ∀ occurrence ∈ rest, occurrence.1 = atom := by
        intro occurrence occurrenceMember
        exact copy_fst atom
          (copiesEqual ▸
            List.mem_cons_of_mem first occurrenceMember)
      have complete :=
        PeriodicThreeSATThree.cycleFrom_complete
          assignment cell atom first first rest
          firstOriginal firstOriginal restOriginal
      intro clause clauseMember
      have clauseMember' :
          clause ∈
            (PeriodicThreeSATThree.cycleFrom
              first first rest).reverse := by
        simpa [cycleClausesFor, copiesEqual,
          PeriodicThreeSATThree.cycleClauses] using
          clauseMember
      exact complete clause
        (List.mem_reverse.mp clauseMember')

/-- Extending any satisfying source assignment satisfies the complete
fixed-slot split. -/
theorem formula_satisfies_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (assignment : Variable → Cell → Bool)
    (satisfies : source.Satisfies assignment) :
    (formula source occurrencePorts).Satisfies
      (PeriodicThreeSATThree.extendAssignment assignment) := by
  intro translate clause clauseMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with sourceMember | cycleMember
  · rcases List.mem_map.mp sourceMember with
      ⟨taggedClause, taggedClauseMember, rfl⟩
    exact occurrenceClause_complete occurrencePorts assignment
      translate taggedClause.2 taggedClause.1
      (satisfies translate taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMember))
  · rcases List.mem_flatMap.mp cycleMember with
      ⟨atom, atomMember, clauseMember⟩
    exact cycleClausesFor_complete assignment translate atom
      clause clauseMember

/-- Every selected occurrence copy belongs to its atom's fixed ring. -/
theorem selected_copy_mem_copies
    {Variable : Type*}
    (occurrencePorts : OccurrencePorts)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat) :
    copy literal.atom
        (occurrencePorts.port clauseIndex literalIndex) ∈
      copies literal.atom := by
  apply List.mem_map.mpr
  exact
    ⟨.port (occurrencePorts.port clauseIndex literalIndex),
      by
        cases occurrencePorts.port clauseIndex literalIndex <;>
          simp [OccurrenceSplitRing.cycleVertices],
      rfl⟩

/-- A satisfying fixed ring makes its restriction agree with every selected
copy. -/
theorem restrictAssignment_eq_copy
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (assignment :
      ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies :
      (formula source occurrencePorts).Satisfies assignment)
    (atom : Variable)
    (atomMember :
      atom ∈ PeriodicThreeSATThree.sourceVariables source)
    (cell : Cell)
    (occurrence : ThreeOccurrenceVariable Variable)
    (occurrenceMember : occurrence ∈ copies atom) :
    restrictAssignment assignment atom cell =
      assignment occurrence cell := by
  cases copiesEqual : copies atom with
  | nil =>
      simp [copiesEqual] at occurrenceMember
  | cons first rest =>
      have cycleSatisfies :
          ∀ clause ∈
              PeriodicThreeSATThree.cycleClauses (first :: rest),
            clause.Holds assignment cell := by
        intro clause clauseMember
        apply satisfies cell clause
        change clause ∈
          occurrenceClauses source occurrencePorts ++
            allCycleClauses source
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_flatMap.mpr
        exact
          ⟨atom, atomMember,
            by
              apply List.mem_reverse.mpr
              simpa [copiesEqual] using clauseMember⟩
      have occurrenceEqualFirst :=
        PeriodicThreeSATThree.cycleClauses_value_eq_first
          assignment cell first rest cycleSatisfies
          occurrence
          (by simpa [copiesEqual] using occurrenceMember)
      simp only [restrictAssignment, copiesEqual,
        List.head?_cons, Option.map_some, Option.getD_some]
      exact occurrenceEqualFirst.symm

/-- A copied literal has the value of its source literal under restriction. -/
theorem occurrenceLiteral_holds_restrict
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (assignment :
      ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies :
      (formula source occurrencePorts).Satisfies assignment)
    (translate : Cell) (clauseIndex literalIndex : Nat)
    (literal : PeriodicLiteral Variable)
    (taggedMember :
      (literal, clauseIndex, literalIndex) ∈
        PeriodicThreeSATThree.taggedLiterals source) :
    (occurrenceLiteral occurrencePorts clauseIndex literalIndex literal).Holds
        assignment translate ↔
      literal.Holds (restrictAssignment assignment) translate := by
  have atomMember :=
    PeriodicThreeSATThree.sourceVariables_mem
      source taggedMember
  have valuesEqual :=
    restrictAssignment_eq_copy source occurrencePorts assignment
      satisfies literal.atom atomMember
      (Cell.add translate literal.offset)
      (copy literal.atom
        (occurrencePorts.port clauseIndex literalIndex))
      (selected_copy_mem_copies occurrencePorts literal
        clauseIndex literalIndex)
  simp only [PeriodicLiteral.Holds, occurrenceLiteral]
  rw [valuesEqual]

/-- Restricting any satisfying fixed-slot assignment satisfies the source. -/
theorem satisfies_of_formula_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (assignment :
      ThreeOccurrenceVariable Variable → Cell → Bool)
    (satisfies :
      (formula source occurrencePorts).Satisfies assignment) :
    source.Satisfies (restrictAssignment assignment) := by
  intro translate clause clauseMember
  have mappedMember :
      clause ∈ source.clauses.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using clauseMember
  rcases List.mem_map.mp mappedMember with
    ⟨⟨taggedClause, clauseIndex⟩,
      taggedClauseMember, taggedClauseEqual⟩
  simp only at taggedClauseEqual
  subst taggedClause
  have occurrenceHolds :
      (occurrenceClause occurrencePorts clauseIndex clause).Holds
        assignment translate := by
    apply satisfies translate
      (occurrenceClause occurrencePorts clauseIndex clause)
    change occurrenceClause occurrencePorts clauseIndex clause ∈
      occurrenceClauses source occurrencePorts ++
        allCycleClauses source
    apply List.mem_append.mpr
    apply Or.inl
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), taggedClauseMember, rfl⟩
  rcases occurrenceHolds with
    ⟨copiedLiteral, copiedLiteralMember,
      copiedLiteralHolds⟩
  rcases List.mem_map.mp copiedLiteralMember with
    ⟨⟨literal, literalIndex⟩,
      taggedLiteralMember, rfl⟩
  refine
    ⟨literal,
      List.fst_mem_of_mem_zipIdx taggedLiteralMember, ?_⟩
  apply
    (occurrenceLiteral_holds_restrict source occurrencePorts
      assignment satisfies translate clauseIndex literalIndex
      literal ?_).mp
  · exact copiedLiteralHolds
  · exact PeriodicThreeSATThree.taggedLiterals_mem
      source taggedClauseMember taggedLiteralMember

/-- The fixed-eight compass split preserves periodic satisfiability for
every occurrence-to-slot assignment. -/
theorem satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts) :
    (formula source occurrencePorts).Satisfiable ↔
      source.Satisfiable := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨restrictAssignment assignment,
        satisfies_of_formula_satisfies
          source occurrencePorts assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact
      ⟨PeriodicThreeSATThree.extendAssignment assignment,
        formula_satisfies_of_satisfies
          source occurrencePorts assignment satisfies⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
