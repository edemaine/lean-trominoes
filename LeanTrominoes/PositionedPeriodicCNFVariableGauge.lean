import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes

/-!
# Variable gauges for positioned periodic CNF

A periodic protovariable may be represented in any lattice cell.  Moving its
stored drawing position by a whole period and adding the opposite cell shift
to every occurrence offset leaves every physical literal occurrence
unchanged.  This file packages that per-variable change of gauge and proves
that it preserves both periodic satisfiability and raw incidence-route
endpoints.
-/

namespace LeanTrominoes

namespace PeriodicLiteral

/-- Add a protovariable-specific lattice shift to one literal occurrence. -/
def variableGauge
    {Variable : Type*}
    (gauge : Variable → Cell)
    (literal : PeriodicLiteral Variable) :
    PeriodicLiteral Variable :=
  ⟨literal.atom, Cell.add literal.offset (gauge literal.atom),
    literal.value⟩

@[simp]
theorem variableGauge_atom
    {Variable : Type*}
    (gauge : Variable → Cell)
    (literal : PeriodicLiteral Variable) :
    (literal.variableGauge gauge).atom = literal.atom := rfl

@[simp]
theorem variableGauge_offset
    {Variable : Type*}
    (gauge : Variable → Cell)
    (literal : PeriodicLiteral Variable) :
    (literal.variableGauge gauge).offset =
      Cell.add literal.offset (gauge literal.atom) := rfl

@[simp]
theorem variableGauge_value
    {Variable : Type*}
    (gauge : Variable → Cell)
    (literal : PeriodicLiteral Variable) :
    (literal.variableGauge gauge).value = literal.value := rfl

end PeriodicLiteral

namespace PeriodicClause

/-- Apply one variable gauge to every literal of a periodic clause. -/
def variableGauge
    {Variable : Type*}
    (gauge : Variable → Cell)
    (clause : PeriodicClause Variable) :
    PeriodicClause Variable :=
  clause.map (PeriodicLiteral.variableGauge gauge)

@[simp]
theorem variableGauge_length
    {Variable : Type*}
    (gauge : Variable → Cell)
    (clause : PeriodicClause Variable) :
    (clause.variableGauge gauge).length = clause.length := by
  simp [variableGauge]

end PeriodicClause

namespace PeriodicCNF

/-- Apply one variable gauge throughout a periodic CNF presentation. -/
def variableGauge
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell) :
    PeriodicCNF Variable :=
  ⟨source.clauses.map (PeriodicClause.variableGauge gauge)⟩

/-- Pull an assignment back along a variable gauge. -/
def pullVariableGaugeAssignment
    {Variable : Type*}
    (gauge : Variable → Cell)
    (assignment : Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom translate =>
    assignment atom (Cell.sub translate (gauge atom))

/-- Push an assignment forward along a variable gauge. -/
def pushVariableGaugeAssignment
    {Variable : Type*}
    (gauge : Variable → Cell)
    (assignment : Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom translate =>
    assignment atom (Cell.add translate (gauge atom))

/-- Gauging a literal and pulling its assignment preserve its truth value at
every translate. -/
theorem variableGauge_literal_holds_iff
    {Variable : Type*}
    (gauge : Variable → Cell)
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    (literal : PeriodicLiteral Variable) :
    (literal.variableGauge gauge).Holds
        (pullVariableGaugeAssignment gauge assignment) translate ↔
      literal.Holds assignment translate := by
  rcases translate with ⟨translateX, translateY⟩
  rcases literal with
    ⟨atom, ⟨offsetX, offsetY⟩, value⟩
  cases gaugeEq : gauge atom with
  | mk gaugeX gaugeY =>
      simp only [PeriodicLiteral.variableGauge,
        PeriodicLiteral.Holds,
        pullVariableGaugeAssignment, Cell.add, Cell.sub,
        gaugeEq]
      ring_nf

/-- The inverse assignment transport recovers truth of the ungauged
literal. -/
theorem literal_holds_pushVariableGaugeAssignment_iff
    {Variable : Type*}
    (gauge : Variable → Cell)
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    (literal : PeriodicLiteral Variable) :
    literal.Holds
        (pushVariableGaugeAssignment gauge assignment) translate ↔
      (literal.variableGauge gauge).Holds assignment translate := by
  rcases translate with ⟨translateX, translateY⟩
  rcases literal with
    ⟨atom, ⟨offsetX, offsetY⟩, value⟩
  cases gaugeEq : gauge atom with
  | mk gaugeX gaugeY =>
      simp [PeriodicLiteral.variableGauge,
        PeriodicLiteral.Holds,
        pushVariableGaugeAssignment, Cell.add, gaugeEq, add_assoc]

/-- Per-variable gauge changes preserve periodic satisfiability exactly. -/
theorem variableGauge_satisfiable_iff
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell) :
    (source.variableGauge gauge).Satisfiable ↔ source.Satisfiable := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    refine
      ⟨pushVariableGaugeAssignment gauge assignment, ?_⟩
    intro translate clause clauseMem
    have gaugedHolds :=
      satisfies translate
        (clause.variableGauge gauge)
        (List.mem_map.mpr ⟨clause, clauseMem, rfl⟩)
    rcases gaugedHolds with
      ⟨gaugedLiteral, gaugedLiteralMem, gaugedLiteralHolds⟩
    rcases List.mem_map.mp gaugedLiteralMem with
      ⟨literal, literalMem, gaugedLiteralEq⟩
    subst gaugedLiteral
    exact
      ⟨literal, literalMem,
        (literal_holds_pushVariableGaugeAssignment_iff
          gauge assignment translate literal).mpr
            gaugedLiteralHolds⟩
  · rintro ⟨assignment, satisfies⟩
    refine
      ⟨pullVariableGaugeAssignment gauge assignment, ?_⟩
    intro translate gaugedClause gaugedClauseMem
    rcases List.mem_map.mp gaugedClauseMem with
      ⟨clause, clauseMem, gaugedClauseEq⟩
    subst gaugedClause
    rcases satisfies translate clause clauseMem with
      ⟨literal, literalMem, literalHolds⟩
    exact
      ⟨literal.variableGauge gauge,
        List.mem_map.mpr ⟨literal, literalMem, rfl⟩,
        (variableGauge_literal_holds_iff
          gauge assignment translate literal).mpr literalHolds⟩

end PeriodicCNF

namespace PositionedPeriodicCNF

/-- Gauge all variables while leaving displayed physical clause positions
unchanged. -/
def variableGauge
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (gauge : Variable → Cell) :
    PositionedPeriodicCNF Variable :=
  ⟨source.clauses.map fun clause =>
    ⟨clause.position, clause.literals.variableGauge gauge⟩⟩

@[simp]
theorem erase_variableGauge
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (gauge : Variable → Cell) :
    (source.variableGauge gauge).erase =
      source.erase.variableGauge gauge := by
  simp [variableGauge, PositionedPeriodicCNF.erase,
    PeriodicCNF.variableGauge, List.map_map,
    Function.comp_def]

end PositionedPeriodicCNF

namespace PeriodicVariablePlacement

/-- The lattice cell containing one stored variable position. -/
def canonicalPositionGauge
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (atom : Variable) : Cell :=
  ((placement.position atom).1 / placement.period,
    (placement.position atom).2 / placement.period)

/-- Move every stored variable position by the inverse of its gauge shift. -/
def variableGauge
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell) :
    PeriodicVariablePlacement Variable where
  period := placement.period
  position := fun atom =>
    Cell.sub (placement.position atom)
      (placement.translation (gauge atom))

@[simp]
theorem variableGauge_period
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell) :
    (placement.variableGauge gauge).period = placement.period := rfl

/-- Literal physical positions are invariant under simultaneous source and
placement gauging. -/
theorem variableGauge_literalPosition
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (literal : PeriodicLiteral Variable) :
    (placement.variableGauge gauge).literalPosition
        (literal.variableGauge gauge) =
      placement.literalPosition literal := by
  rcases placement.position literal.atom with
    ⟨positionX, positionY⟩
  rcases literal.offset with ⟨offsetX, offsetY⟩
  rcases gauge literal.atom with ⟨gaugeX, gaugeY⟩
  apply Prod.ext <;>
    simp [variableGauge,
      PeriodicVariablePlacement.literalPosition,
      PeriodicVariablePlacement.translation,
      PeriodicLiteral.variableGauge,
      Cell.add, Cell.sub, Cell.scale] <;>
    ring

/-- Gauging by the position quotient reduces both coordinates to their
Euclidean remainders modulo the physical period. -/
theorem variableGauge_canonicalPositionGauge_position
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (placement.variableGauge
      placement.canonicalPositionGauge).position atom =
      ((placement.position atom).1 % placement.period,
        (placement.position atom).2 % placement.period) := by
  have horizontalDivision :=
    Int.emod_add_mul_ediv
      (placement.position atom).1 (placement.period : Int)
  have verticalDivision :=
    Int.emod_add_mul_ediv
      (placement.position atom).2 (placement.period : Int)
  apply Prod.ext <;>
    simp [variableGauge, canonicalPositionGauge,
      PeriodicVariablePlacement.translation,
      Cell.sub, Cell.scale] <;>
    omega

/-- Canonically gauged variable positions lie in the half-open fundamental
square whenever the period is positive. -/
theorem variableGauge_canonicalPositionGauge_position_halfOpen
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period)
    (atom : Variable) :
    0 ≤
        ((placement.variableGauge
          placement.canonicalPositionGauge).position atom).1 ∧
      ((placement.variableGauge
          placement.canonicalPositionGauge).position atom).1 <
        placement.period ∧
      0 ≤
        ((placement.variableGauge
          placement.canonicalPositionGauge).position atom).2 ∧
      ((placement.variableGauge
          placement.canonicalPositionGauge).position atom).2 <
        placement.period := by
  rw [variableGauge_canonicalPositionGauge_position]
  have periodPositiveInt : (0 : Int) < placement.period := by
    exact_mod_cast periodPositive
  exact
    ⟨Int.emod_nonneg _ (ne_of_gt periodPositiveInt),
      Int.emod_lt_of_pos _ periodPositiveInt,
      Int.emod_nonneg _ (ne_of_gt periodPositiveInt),
      Int.emod_lt_of_pos _ periodPositiveInt⟩

/-- Nonzero coordinate residues upgrade the half-open bounds to the strict
fundamental-square convention used by periodic drawings. -/
theorem variableGauge_canonicalPositionGauge_position_inSquare
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period)
    (atom : Variable)
    (horizontalNonzero :
      (placement.position atom).1 % placement.period ≠ 0)
    (verticalNonzero :
      (placement.position atom).2 % placement.period ≠ 0) :
    0 <
        ((placement.variableGauge
          placement.canonicalPositionGauge).position atom).1 ∧
      ((placement.variableGauge
          placement.canonicalPositionGauge).position atom).1 <
        placement.period ∧
      0 <
        ((placement.variableGauge
          placement.canonicalPositionGauge).position atom).2 ∧
      ((placement.variableGauge
          placement.canonicalPositionGauge).position atom).2 <
        placement.period := by
  have halfOpen :=
    variableGauge_canonicalPositionGauge_position_halfOpen
      placement periodPositive atom
  rw [variableGauge_canonicalPositionGauge_position] at halfOpen ⊢
  exact
    ⟨lt_of_le_of_ne halfOpen.1 (Ne.symm horizontalNonzero),
      halfOpen.2.1,
      lt_of_le_of_ne halfOpen.2.2.1 (Ne.symm verticalNonzero),
      halfOpen.2.2.2⟩

end PeriodicVariablePlacement

namespace PositionedPeriodicCNF

/-- A raw physical route family remains valid under a variable gauge because
displayed clause positions and all physical literal occurrences are
unchanged. -/
theorem PhysicalIncidenceRoutesMatch.variableGauge
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (routesMatch :
      source.PhysicalIncidenceRoutesMatch placement routes) :
    (source.variableGauge gauge).PhysicalIncidenceRoutesMatch
      (placement.variableGauge gauge) routes := by
  intro gaugedClause clauseIndex gaugedClauseMem
    gaugedLiteral literalIndex gaugedLiteralMem
  change
    (gaugedClause, clauseIndex) ∈
      (source.clauses.map fun clause =>
        ⟨clause.position,
          clause.literals.variableGauge gauge⟩).zipIdx
    at gaugedClauseMem
  rw [List.zipIdx_map] at gaugedClauseMem
  rcases List.mem_map.mp gaugedClauseMem with
    ⟨taggedClause, taggedClauseMem, gaugedClauseEq⟩
  have clauseIndexEq :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd gaugedClauseEq
  have gaugedClauseValueEq :
      gaugedClause =
        ⟨taggedClause.1.position,
          taggedClause.1.literals.variableGauge gauge⟩ :=
    (congrArg Prod.fst gaugedClauseEq).symm
  subst clauseIndex
  subst gaugedClause
  change
    (gaugedLiteral, literalIndex) ∈
      (taggedClause.1.literals.map
        (PeriodicLiteral.variableGauge gauge)).zipIdx
    at gaugedLiteralMem
  rw [List.zipIdx_map] at gaugedLiteralMem
  rcases List.mem_map.mp gaugedLiteralMem with
    ⟨taggedLiteral, taggedLiteralMem, gaugedLiteralEq⟩
  have literalIndexEq :
      taggedLiteral.2 = literalIndex :=
    congrArg Prod.snd gaugedLiteralEq
  have gaugedLiteralValueEq :
      gaugedLiteral =
        taggedLiteral.1.variableGauge gauge :=
    (congrArg Prod.fst gaugedLiteralEq).symm
  subst literalIndex
  subst gaugedLiteral
  have endpoints :=
    routesMatch taggedClause.1 taggedClause.2
      taggedClauseMem taggedLiteral.1 taggedLiteral.2
      taggedLiteralMem
  refine ⟨endpoints.1, ?_⟩
  rw [endpoints.2]
  exact congrArg some
    (PeriodicVariablePlacement.variableGauge_literalPosition
      placement gauge taggedLiteral.1).symm

end PositionedPeriodicCNF

end LeanTrominoes
