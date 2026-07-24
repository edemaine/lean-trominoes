import LeanTrominoes.PeriodicCNF

/-!
# Reduction of periodic CNF to periodic 3CNF

This file implements the standard chain conversion used in Theorem 3.3 of the
paper.  Each long protoclauses receives its own family of auxiliary
protovariables.  The auxiliary literals are placed at the first offset of the
original clause, so the conversion can preserve locality.
-/

namespace LeanTrominoes

/-- Original variables or a chain variable identified by its source clause
and its position in that clause's split.  Identical duplicate protoclauses may
share auxiliaries harmlessly because they generate identical constraints. -/
abbrev ThreeCNFVariable (Variable : Type*) :=
  Sum Variable (PeriodicClause Variable × Nat)

namespace PeriodicThreeCNF

/-- The first literal's offset, or the origin for an empty clause. -/
def anchor {Variable : Type*} (clause : PeriodicClause Variable) : Cell :=
  (clause.head?.map PeriodicLiteral.offset).getD (0, 0)

/-- Embed an original literal into the enlarged variable type. -/
def liftLiteral {Variable : Type*} (literal : PeriodicLiteral Variable) :
    PeriodicLiteral (ThreeCNFVariable Variable) :=
  ⟨Sum.inl literal.atom, literal.offset, literal.value⟩

/-- One literal of the auxiliary implication chain. -/
def auxiliary {Variable : Type*} (source : PeriodicClause Variable)
    (index : Nat) (value : Bool) :
    PeriodicLiteral (ThreeCNFVariable Variable) :=
  ⟨Sum.inr (source, index), anchor source, value⟩

/-- Finish a split clause after the first two original literals.  The incoming
auxiliary is true precisely when the already-consumed prefix was false. -/
def continuation {Variable : Type*} (source : PeriodicClause Variable) :
    Nat → PeriodicClause Variable →
      List (PeriodicClause (ThreeCNFVariable Variable))
  | index, [] =>
      [[auxiliary source index false]]
  | index, [first] =>
      [[auxiliary source index false, liftLiteral first]]
  | index, [first, second] =>
      [[auxiliary source index false, liftLiteral first, liftLiteral second]]
  | index, first :: second :: third :: rest =>
      [auxiliary source index false, liftLiteral first,
        auxiliary source (index + 1) true] ::
      continuation source (index + 1) (second :: third :: rest)

/-- Replace one arbitrary-width protoclauses by an equisatisfiable list of
clauses of width at most three. -/
def clauseClauses {Variable : Type*} (source : PeriodicClause Variable) :
    List (PeriodicClause (ThreeCNFVariable Variable)) :=
  match source with
  | [] => [[]]
  | [first] => [[liftLiteral first]]
  | [first, second] => [[liftLiteral first, liftLiteral second]]
  | [first, second, third] =>
      [[liftLiteral first, liftLiteral second, liftLiteral third]]
  | first :: second :: third :: fourth :: rest =>
      [liftLiteral first, liftLiteral second, auxiliary source 0 true] ::
        continuation source 0 (third :: fourth :: rest)

/-- Apply the standard clause split to every protoclauses. -/
def formula {Variable : Type*} (source : PeriodicCNF Variable) :
    PeriodicCNF (ThreeCNFVariable Variable) where
  clauses := source.clauses.flatMap clauseClauses

/-- Literals generated from one source clause are either embedded source
literals or auxiliaries anchored to that source clause. -/
def Supported {Variable : Type*} (source : PeriodicClause Variable)
    (literal : PeriodicLiteral (ThreeCNFVariable Variable)) : Prop :=
  (∃ original ∈ source, literal = liftLiteral original) ∨
    ∃ index value, literal = auxiliary source index value

theorem supported_offsetDistance_le_one {Variable : Type*}
    {source : PeriodicClause Variable} (source_local : source.IsLocal)
    {first second : PeriodicLiteral (ThreeCNFVariable Variable)}
    (first_supported : Supported source first)
    (second_supported : Supported source second) :
    PeriodicClause.offsetDistance first second ≤ 1 := by
  rcases first_supported with
      ⟨originalFirst, first_mem, rfl⟩ | ⟨firstIndex, firstValue, rfl⟩ <;>
    rcases second_supported with
      ⟨originalSecond, second_mem, rfl⟩ | ⟨secondIndex, secondValue, rfl⟩
  · simpa [PeriodicClause.offsetDistance, liftLiteral] using
      source_local originalFirst first_mem originalSecond second_mem
  · cases source with
    | nil => simp at first_mem
    | cons anchorLiteral rest =>
        simpa [PeriodicClause.offsetDistance, liftLiteral, auxiliary, anchor] using
          source_local originalFirst first_mem anchorLiteral (by simp)
  · cases source with
    | nil => simp at second_mem
    | cons anchorLiteral rest =>
        simpa [PeriodicClause.offsetDistance, liftLiteral, auxiliary, anchor] using
          source_local anchorLiteral (by simp) originalSecond second_mem
  · simp [PeriodicClause.offsetDistance, auxiliary]

theorem isLocal_of_supported {Variable : Type*}
    {source : PeriodicClause Variable} (source_local : source.IsLocal)
    {clause : PeriodicClause (ThreeCNFVariable Variable)}
    (supported : ∀ literal ∈ clause, Supported source literal) :
    clause.IsLocal := by
  intro first first_mem second second_mem
  exact supported_offsetDistance_le_one source_local
    (supported first first_mem) (supported second second_mem)

theorem continuation_supported {Variable : Type*}
    (source remaining : PeriodicClause Variable) (index : Nat)
    (remaining_mem : ∀ literal ∈ remaining, literal ∈ source) :
    ∀ clause ∈ continuation source index remaining,
      ∀ literal ∈ clause, Supported source literal := by
  induction remaining generalizing index with
  | nil =>
      intro clause clause_mem literal literal_mem
      simp only [continuation, List.mem_singleton] at clause_mem
      subst clause
      simp only [List.mem_singleton] at literal_mem
      subst literal
      exact Or.inr ⟨index, false, rfl⟩
  | cons first rest ih =>
      cases rest with
      | nil =>
          intro clause clause_mem literal literal_mem
          simp only [continuation, List.mem_singleton] at clause_mem
          subst clause
          simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
          rcases literal_mem with rfl | rfl
          · exact Or.inr ⟨index, false, rfl⟩
          · exact Or.inl ⟨first, remaining_mem first (by simp), rfl⟩
      | cons second rest =>
          cases rest with
          | nil =>
              intro clause clause_mem literal literal_mem
              simp only [continuation, List.mem_singleton] at clause_mem
              subst clause
              simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
              rcases literal_mem with rfl | rfl | rfl
              · exact Or.inr ⟨index, false, rfl⟩
              · exact Or.inl ⟨first, remaining_mem first (by simp), rfl⟩
              · exact Or.inl ⟨second, remaining_mem second (by simp), rfl⟩
          | cons third rest =>
              intro clause clause_mem literal literal_mem
              simp only [continuation, List.mem_cons] at clause_mem
              rcases clause_mem with rfl | clause_mem
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
                rcases literal_mem with rfl | rfl | rfl
                · exact Or.inr ⟨index, false, rfl⟩
                · exact Or.inl ⟨first, remaining_mem first (by simp), rfl⟩
                · exact Or.inr ⟨index + 1, true, rfl⟩
              · exact ih (index + 1)
                  (fun literal literal_mem =>
                    remaining_mem literal (by simp [literal_mem]))
                  clause clause_mem literal literal_mem

theorem clauseClauses_supported {Variable : Type*}
    (source : PeriodicClause Variable) :
    ∀ clause ∈ clauseClauses source,
      ∀ literal ∈ clause, Supported source literal := by
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseClauses]
  · cases rest with
    | nil =>
        intro clause clause_mem literal literal_mem
        simp only [clauseClauses, List.mem_singleton] at clause_mem
        subst clause
        simp only [List.mem_singleton] at literal_mem
        subst literal
        exact Or.inl ⟨first, by simp, rfl⟩
    | cons second rest =>
        cases rest with
        | nil =>
            intro clause clause_mem literal literal_mem
            simp only [clauseClauses, List.mem_singleton] at clause_mem
            subst clause
            simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
            rcases literal_mem with rfl | rfl
            · exact Or.inl ⟨first, by simp, rfl⟩
            · exact Or.inl ⟨second, by simp, rfl⟩
        | cons third rest =>
            cases rest with
            | nil =>
                intro clause clause_mem literal literal_mem
                simp only [clauseClauses, List.mem_singleton] at clause_mem
                subst clause
                simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
                rcases literal_mem with rfl | rfl | rfl
                · exact Or.inl ⟨first, by simp, rfl⟩
                · exact Or.inl ⟨second, by simp, rfl⟩
                · exact Or.inl ⟨third, by simp, rfl⟩
            | cons fourth rest =>
                intro clause clause_mem literal literal_mem
                simp only [clauseClauses, List.mem_cons] at clause_mem
                rcases clause_mem with rfl | clause_mem
                · simp only [List.mem_cons, List.not_mem_nil, or_false] at literal_mem
                  rcases literal_mem with rfl | rfl | rfl
                  · exact Or.inl ⟨first, by simp, rfl⟩
                  · exact Or.inl ⟨second, by simp, rfl⟩
                  · exact Or.inr ⟨0, true, rfl⟩
                · exact continuation_supported
                    (first :: second :: third :: fourth :: rest)
                    (third :: fourth :: rest) 0
                    (by intro item item_mem; simp [item_mem])
                    clause clause_mem literal literal_mem

theorem clauseClauses_areLocal {Variable : Type*}
    {source : PeriodicClause Variable} (source_local : source.IsLocal) :
    ∀ clause ∈ clauseClauses source, clause.IsLocal := by
  intro clause clause_mem
  exact isLocal_of_supported source_local
    (clauseClauses_supported source clause clause_mem)

/-- The standard width-three conversion preserves locality. -/
theorem formula_isLocal {Variable : Type*} {source : PeriodicCNF Variable}
    (source_local : source.IsLocal) :
    (formula source).IsLocal := by
  intro clause clause_mem
  simp only [formula, List.mem_flatMap] at clause_mem
  rcases clause_mem with ⟨sourceClause, source_mem, clause_mem⟩
  exact clauseClauses_areLocal (source_local sourceClause source_mem)
    clause clause_mem

theorem continuation_widthAtMostThree {Variable : Type*}
    (source : PeriodicClause Variable) (index : Nat)
    (remaining : PeriodicClause Variable) :
    ∀ clause ∈ continuation source index remaining,
      clause.WidthAtMost 3 := by
  induction remaining generalizing index with
  | nil =>
      simp [continuation, PeriodicClause.WidthAtMost]
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp [continuation, PeriodicClause.WidthAtMost]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [continuation, PeriodicClause.WidthAtMost]
          | cons third rest =>
              simp only [continuation, List.mem_cons]
              intro clause clause_mem
              rcases clause_mem with rfl | clause_mem
              · simp [PeriodicClause.WidthAtMost]
              · exact ih (index + 1) clause clause_mem

theorem clauseClauses_widthAtMostThree {Variable : Type*}
    (source : PeriodicClause Variable) :
    ∀ clause ∈ clauseClauses source, clause.WidthAtMost 3 := by
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseClauses, PeriodicClause.WidthAtMost]
  · cases rest with
    | nil =>
        simp [clauseClauses, PeriodicClause.WidthAtMost]
    | cons second rest =>
        cases rest with
        | nil =>
            simp [clauseClauses, PeriodicClause.WidthAtMost]
        | cons third rest =>
            cases rest with
            | nil =>
                simp [clauseClauses, PeriodicClause.WidthAtMost]
            | cons fourth rest =>
                simp only [clauseClauses, List.mem_cons]
                intro clause clause_mem
                rcases clause_mem with rfl | clause_mem
                · simp [PeriodicClause.WidthAtMost]
                · exact continuation_widthAtMostThree
                    (first :: second :: third :: fourth :: rest)
                    0 (third :: fourth :: rest) clause clause_mem

/-- Every output clause has width at most three. -/
theorem formula_widthAtMostThree {Variable : Type*}
    (source : PeriodicCNF Variable) :
    (formula source).WidthAtMost 3 := by
  intro clause clause_mem
  simp only [formula, List.mem_flatMap] at clause_mem
  rcases clause_mem with ⟨sourceClause, source_mem, clause_mem⟩
  exact clauseClauses_widthAtMostThree sourceClause clause clause_mem

end PeriodicThreeCNF
end LeanTrominoes
