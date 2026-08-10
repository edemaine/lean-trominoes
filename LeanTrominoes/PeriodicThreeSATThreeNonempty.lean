import LeanTrominoes.PeriodicThreeSATThreeComputability

/-!
# Nonempty clauses in the Wang 3SAT-3 endpoint

The geometric hardness pipeline routes one incidence for every source clause
and therefore excludes empty clauses.  A nonempty Wang tile set has this
property, and both width splitting and occurrence splitting preserve it.
-/

namespace LeanTrominoes

namespace WangPeriodicCNF

theorem formula_clausesNonempty_of_tiles_ne_nil
    (tiles : LeanWang.TileSet) (tilesNonempty : tiles ≠ []) :
    ∀ clause ∈ (formula tiles).clauses, clause ≠ [] := by
  intro clause clauseMember
  simp only [formula, List.mem_cons, List.mem_append] at clauseMember
  rcases clauseMember with (rfl | horizontalMember) | verticalMember
  · simpa [atLeastOneClause] using tilesNonempty
  · simp only [horizontalClauses, List.mem_filterMap] at horizontalMember
    rcases horizontalMember with ⟨pair, _pairMember, clauseEq⟩
    split at clauseEq
    · contradiction
    · simp only [Option.some.injEq] at clauseEq
      subst clause
      simp
  · simp only [verticalClauses, List.mem_filterMap] at verticalMember
    rcases verticalMember with ⟨pair, _pairMember, clauseEq⟩
    split at clauseEq
    · contradiction
    · simp only [Option.some.injEq] at clauseEq
      subst clause
      simp

end WangPeriodicCNF

namespace PeriodicThreeCNF

theorem continuation_clausesNonempty {Variable : Type*}
    (source remaining : PeriodicClause Variable) :
    ∀ clause ∈ continuation source remaining, clause ≠ [] := by
  induction remaining with
  | nil => simp [continuation]
  | cons first rest induction =>
      cases rest with
      | nil => simp [continuation]
      | cons second rest =>
          cases rest with
          | nil => simp [continuation]
          | cons third rest =>
              intro clause clauseMember
              simp only [continuation, List.mem_cons] at clauseMember
              rcases clauseMember with rfl | clauseMember
              · simp
              · exact induction clause clauseMember

theorem clauseClauses_clausesNonempty {Variable : Type*}
    (source : PeriodicClause Variable) (sourceNonempty : source ≠ []) :
    ∀ clause ∈ clauseClauses source, clause ≠ [] := by
  rcases source with _ | ⟨first, rest⟩
  · exact (sourceNonempty rfl).elim
  · cases rest with
    | nil => simp [clauseClauses]
    | cons second rest =>
        cases rest with
        | nil => simp [clauseClauses]
        | cons third rest =>
            cases rest with
            | nil => simp [clauseClauses]
            | cons fourth rest =>
                intro clause clauseMember
                simp only [clauseClauses, List.mem_cons] at clauseMember
                rcases clauseMember with rfl | clauseMember
                · simp
                · exact continuation_clausesNonempty
                    (first :: second :: third :: fourth :: rest)
                    (third :: fourth :: rest) clause clauseMember

theorem formula_clausesNonempty {Variable : Type*}
    (source : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause ∈ (formula source).clauses, clause ≠ [] := by
  intro clause clauseMember
  simp only [formula, List.mem_flatMap] at clauseMember
  rcases clauseMember with
    ⟨sourceClause, sourceClauseMember, clauseMember⟩
  exact clauseClauses_clausesNonempty sourceClause
    (sourceClausesNonempty sourceClause sourceClauseMember)
    clause clauseMember

end PeriodicThreeCNF

namespace PeriodicThreeSATThree

theorem cycleFrom_clausesNonempty {Variable : Type*}
    (first current : ThreeOccurrenceVariable Variable)
    (remaining : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleFrom first current remaining, clause ≠ [] := by
  induction remaining generalizing current with
  | nil => simp [cycleFrom, implicationClause]
  | cons next rest induction =>
      intro clause clauseMember
      simp only [cycleFrom, List.mem_cons] at clauseMember
      rcases clauseMember with rfl | clauseMember
      · simp [implicationClause]
      · exact induction next clause clauseMember

theorem cycleClauses_clausesNonempty {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable)) :
    ∀ clause ∈ cycleClauses copies, clause ≠ [] := by
  cases copies with
  | nil => simp [cycleClauses]
  | cons first rest =>
      exact cycleFrom_clausesNonempty first first rest

theorem allCycleClauses_clausesNonempty {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable) :
    ∀ clause ∈ allCycleClauses source, clause ≠ [] := by
  intro clause clauseMember
  simp only [allCycleClauses, List.mem_flatMap] at clauseMember
  rcases clauseMember with ⟨atom, _atomMember, clauseMember⟩
  exact cycleClauses_clausesNonempty
    (occurrenceVariables source atom) clause clauseMember

theorem formula_clausesNonempty {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ clause ∈ (formula source).clauses, clause ≠ [] := by
  intro clause clauseMember
  simp only [formula, List.mem_append] at clauseMember
  rcases clauseMember with occurrenceMember | cycleMember
  · simp only [occurrenceClauses, List.mem_map] at occurrenceMember
    rcases occurrenceMember with
      ⟨⟨sourceClause, clauseIndex⟩, taggedMember, rfl⟩
    intro occurrenceEmpty
    have sourceLengthPositive : 0 < sourceClause.length :=
      List.length_pos_of_ne_nil
        (sourceClausesNonempty sourceClause
          (List.fst_mem_of_mem_zipIdx taggedMember))
    have occurrenceLength := occurrenceClause_length clauseIndex sourceClause
    rw [occurrenceEmpty] at occurrenceLength
    simp at occurrenceLength
    omega
  · exact allCycleClauses_clausesNonempty source clause cycleMember

theorem wangFormula_clausesNonempty
    (tiles : LeanWang.TileSet) (tilesNonempty : tiles ≠ []) :
    ∀ clause ∈ (wangFormula tiles).clauses, clause ≠ [] := by
  apply formula_clausesNonempty
  apply PeriodicThreeCNF.formula_clausesNonempty
  exact WangPeriodicCNF.formula_clausesNonempty_of_tiles_ne_nil
    tiles tilesNonempty

end PeriodicThreeSATThree

end LeanTrominoes
