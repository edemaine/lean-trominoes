import LeanTrominoes.PositionedPeriodicCNFClauseOrderingComputability
import LeanTrominoes.PositionedPeriodicCNFDeduplication

/-!
# Computability of positioned periodic CNF bookkeeping

Positioned periodic clauses support executable erasure, variable renaming,
clause-position lookup, clause-anchor normalization, and duplicate-orbit
removal.  The parameterized statements allow the source formula, variable
map, and physical period to be computed from a common external input.
-/

noncomputable section

namespace LeanTrominoes

namespace PositionedPeriodicClause

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : Cell × PeriodicClause Variable =>
      PositionedPeriodicClause.mk data.1 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end PositionedPeriodicClause

namespace PositionedPeriodicCNF

private theorem clause_idxOf_decidableEq_eq
    {Variable : Type*} [DecidableEq Variable]
    (clause : PeriodicClause Variable)
    (clauses : List (PeriodicClause Variable)) :
    @List.idxOf (PeriodicClause Variable)
        instBEqOfDecidableEq clause clauses =
      clauses.idxOf clause := by
  induction clauses with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite,
        beq_iff_eq]
      rw [induction]

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun clauses : List (PositionedPeriodicClause Variable) =>
      PositionedPeriodicCNF.mk clauses :=
  equivData_symm_primrec.of_eq fun _ => rfl

theorem erase_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (erase : PositionedPeriodicCNF Variable →
      PeriodicCNF Variable) := by
  have literals : Primrec fun source : PositionedPeriodicCNF Variable =>
      source.clauses.map PositionedPeriodicClause.literals :=
    Primrec.list_map clauses_primrec
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd).to₂
  exact (PeriodicCNF.equivData_symm_primrec.comp literals).of_eq
    fun _ => rfl

theorem rename_primrec
    {Input Source Target : Type*}
    [Primcodable Input] [Primcodable Source] [Primcodable Target]
    (source : Input → PositionedPeriodicCNF Source)
    (variableMap : Input → Source → Target)
    (sourcePrimrec : Primrec source)
    (variableMapPrimrec : Primrec fun input : Input × Source =>
      variableMap input.1 input.2) :
    Primrec fun input => (source input).rename (variableMap input) := by
  have sourceClauses : Primrec fun input : Input =>
      (source input).clauses :=
    clauses_primrec.comp sourcePrimrec
  have renameLiteral : Primrec fun input :
      (Input × PositionedPeriodicClause Source) ×
        PeriodicLiteral Source =>
      PeriodicLiteral.mk
        (variableMap input.1.1 input.2.atom)
        input.2.offset input.2.value := by
    have atom : Primrec fun input :
        (Input × PositionedPeriodicClause Source) ×
          PeriodicLiteral Source =>
        variableMap input.1.1 input.2.atom :=
      variableMapPrimrec.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd))
    exact (PeriodicLiteral.equivData_symm_primrec.comp
      (Primrec.pair atom
        (Primrec.pair
          (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
          (PeriodicThreeCNF.literal_value_primrec.comp Primrec.snd)))).of_eq
      fun _ => rfl
  have renameClause : Primrec₂ fun (input : Input)
      (clause : PositionedPeriodicClause Source) =>
      PositionedPeriodicClause.mk clause.position
        (clause.literals.map fun literal =>
          PeriodicLiteral.mk
            (variableMap input literal.atom)
            literal.offset literal.value) := by
    change Primrec fun combined :
        Input × PositionedPeriodicClause Source =>
      PositionedPeriodicClause.mk combined.2.position
        (combined.2.literals.map fun literal =>
          PeriodicLiteral.mk
            (variableMap combined.1 literal.atom)
            literal.offset literal.value)
    have literals : Primrec fun combined :
        Input × PositionedPeriodicClause Source =>
        combined.2.literals.map fun literal =>
          PeriodicLiteral.mk
            (variableMap combined.1 literal.atom)
            literal.offset literal.value :=
      Primrec.list_map
        (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)
        renameLiteral
    exact (PositionedPeriodicClause.mk_primrec.comp
      (Primrec.pair
        (PositionedPeriodicClause.position_primrec.comp Primrec.snd)
        literals)).of_eq fun _ => rfl
  have clauses : Primrec fun input : Input =>
      (source input).clauses.map fun clause =>
        PositionedPeriodicClause.mk clause.position
          (clause.literals.map fun literal =>
            PeriodicLiteral.mk
              (variableMap input literal.atom)
              literal.offset literal.value) :=
    Primrec.list_map sourceClauses renameClause
  exact (mk_primrec.comp clauses).of_eq fun _ => rfl

theorem clausePosition_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : PositionedPeriodicCNF Variable × Nat =>
      input.1.clausePosition input.2 := by
  have clauses : Primrec fun input :
      PositionedPeriodicCNF Variable × Nat =>
      input.1.clauses :=
    clauses_primrec.comp Primrec.fst
  have selected : Primrec fun input :
      PositionedPeriodicCNF Variable × Nat =>
      input.1.clauses[input.2]? :=
    Primrec.list_getElem?.comp clauses Primrec.snd
  have position : Primrec fun input :
      PositionedPeriodicCNF Variable × Nat =>
      input.1.clauses[input.2]?.map PositionedPeriodicClause.position :=
    Primrec.option_map selected
      (PositionedPeriodicClause.position_primrec.comp Primrec.snd).to₂
  exact (Primrec.option_getD.comp position
    (Primrec.const ((0, 0) : Cell))).of_eq fun _ => rfl

theorem representativeClausePosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input :
        PositionedPeriodicCNF Variable × PeriodicClause Variable =>
      input.1.representativeClausePosition input.2 := by
  have erasedClauses : Primrec fun input :
      PositionedPeriodicCNF Variable × PeriodicClause Variable =>
      input.1.erase.clauses :=
    PeriodicCNF.equivData_primrec.comp
      (erase_primrec.comp Primrec.fst)
  have index : Primrec fun input :
      PositionedPeriodicCNF Variable × PeriodicClause Variable =>
      input.1.erase.clauses.idxOf input.2 :=
    (Primrec.list_idxOf.comp Primrec.snd erasedClauses).of_eq
      fun input => clause_idxOf_decidableEq_eq
        input.2 input.1.erase.clauses
  exact (clausePosition_primrec.comp
    (Primrec.pair Primrec.fst index)).of_eq fun _ => rfl

theorem canonicalClausePosition_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (periodPrimrec : Primrec period) :
    Primrec fun input : Input × PositionedPeriodicClause Variable =>
      canonicalClausePosition
        { period := period input.1
          position := fun _ : Variable => (0, 0) }
        input.2 := by
  have anchor : Primrec fun input :
      Input × PositionedPeriodicClause Variable =>
      PeriodicCNF.clauseAnchor input.2.literals :=
    PeriodicCNF.clauseAnchor_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)
  have physicalPeriod : Primrec fun input :
      Input × PositionedPeriodicClause Variable =>
      (period input.1 : Int) :=
    Computability.int_ofNat_primrec.comp
      (periodPrimrec.comp Primrec.fst)
  have translation : Primrec fun input :
      Input × PositionedPeriodicClause Variable =>
      Cell.scale (period input.1) (PeriodicCNF.clauseAnchor input.2.literals) :=
    Computability.cell_scale_primrec.comp physicalPeriod anchor
  exact (Computability.cell_sub_primrec.comp
    (PositionedPeriodicClause.position_primrec.comp Primrec.snd)
    translation).of_eq fun _ => rfl

theorem anchorNormalize_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (period : Input → Nat)
    (sourcePrimrec : Primrec source) (periodPrimrec : Primrec period) :
    Primrec fun input =>
      (source input).anchorNormalize
        { period := period input
          position := fun _ : Variable => (0, 0) } := by
  have sourceClauses : Primrec fun input : Input =>
      (source input).clauses :=
    clauses_primrec.comp sourcePrimrec
  have one : Primrec₂ fun (input : Input)
      (clause : PositionedPeriodicClause Variable) =>
      PositionedPeriodicClause.mk
        (canonicalClausePosition
          { period := period input
            position := fun _ : Variable => (0, 0) }
          clause)
        clause.literals.anchorNormalize := by
    change Primrec fun combined :
        Input × PositionedPeriodicClause Variable =>
      PositionedPeriodicClause.mk
        (canonicalClausePosition
          { period := period combined.1
            position := fun _ : Variable => (0, 0) }
          combined.2)
        combined.2.literals.anchorNormalize
    exact PositionedPeriodicClause.mk_primrec.comp
      (Primrec.pair
        (canonicalClausePosition_primrec period periodPrimrec)
        (PeriodicClause.anchorNormalize_primrec.comp
          (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)))
  have clauses : Primrec fun input : Input =>
      (source input).clauses.map fun clause =>
        PositionedPeriodicClause.mk
          (canonicalClausePosition
            { period := period input
              position := fun _ : Variable => (0, 0) }
            clause)
          clause.literals.anchorNormalize :=
    Primrec.list_map sourceClauses one
  exact (mk_primrec.comp clauses).of_eq fun _ => rfl

theorem variableGauge_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (gauge : Input → Variable → Cell)
    (sourcePrimrec : Primrec source)
    (gaugePrimrec : Primrec fun input : Input × Variable =>
      gauge input.1 input.2) :
    Primrec fun input => (source input).variableGauge (gauge input) := by
  have sourceClauses : Primrec fun input : Input =>
      (source input).clauses :=
    clauses_primrec.comp sourcePrimrec
  have one : Primrec₂ fun (input : Input)
      (clause : PositionedPeriodicClause Variable) =>
      PositionedPeriodicClause.mk clause.position
        (clause.literals.variableGauge (gauge input)) := by
    change Primrec fun combined :
        Input × PositionedPeriodicClause Variable =>
      PositionedPeriodicClause.mk combined.2.position
        (combined.2.literals.variableGauge (gauge combined.1))
    exact PositionedPeriodicClause.mk_primrec.comp
      (Primrec.pair
        (PositionedPeriodicClause.position_primrec.comp Primrec.snd)
        (PeriodicClause.variableGauge_primrec gauge gaugePrimrec |>.comp
          (Primrec.pair Primrec.fst
            (PositionedPeriodicClause.literals_primrec.comp Primrec.snd))))
  have clauses : Primrec fun input : Input =>
      (source input).clauses.map fun clause =>
        PositionedPeriodicClause.mk clause.position
          (clause.literals.variableGauge (gauge input)) :=
    Primrec.list_map sourceClauses one
  exact (mk_primrec.comp clauses).of_eq fun _ => rfl

theorem deduplicateByLiterals_primrec
    {Input Variable : Type*}
    [Primcodable Input] [Primcodable Variable] [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePrimrec : Primrec source) :
    Primrec fun input => (source input).deduplicateByLiterals := by
  have erasedClauses : Primrec fun input : Input =>
      (source input).erase.clauses :=
    PeriodicCNF.equivData_primrec.comp
      (erase_primrec.comp sourcePrimrec)
  have distinctClauses : Primrec fun input : Input =>
      (source input).erase.clauses.dedup :=
    PeriodicThreeSATThree.dedup_primrec.comp erasedClauses
  have one : Primrec₂ fun (input : Input)
      (clause : PeriodicClause Variable) =>
      PositionedPeriodicClause.mk
        ((source input).representativeClausePosition clause) clause := by
    change Primrec fun combined : Input × PeriodicClause Variable =>
      PositionedPeriodicClause.mk
        ((source combined.1).representativeClausePosition combined.2)
        combined.2
    exact PositionedPeriodicClause.mk_primrec.comp
      (Primrec.pair
        (representativeClausePosition_primrec.comp
          (Primrec.pair (sourcePrimrec.comp Primrec.fst) Primrec.snd))
        Primrec.snd)
  have clauses : Primrec fun input : Input =>
      (source input).erase.clauses.dedup.map fun clause =>
        PositionedPeriodicClause.mk
          ((source input).representativeClausePosition clause) clause :=
    Primrec.list_map distinctClauses one
  exact (mk_primrec.comp clauses).of_eq fun _ => rfl

end PositionedPeriodicCNF

namespace PeriodicVariablePlacement

theorem canonicalPositionGauge_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (position : Input → Variable → Cell)
    (periodPrimrec : Primrec period)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      position input.1 input.2) :
    Primrec fun input : Input × Variable =>
      ({ period := period input.1
         position := position input.1 } :
        PeriodicVariablePlacement Variable).canonicalPositionGauge input.2 := by
  have point : Primrec fun input : Input × Variable =>
      position input.1 input.2 :=
    positionPrimrec
  have divisor : Primrec fun input : Input × Variable =>
      period input.1 :=
    periodPrimrec.comp Primrec.fst
  exact Primrec.pair
    (Computability.int_edivNat_primrec.comp
      (Primrec.fst.comp point) divisor)
    (Computability.int_edivNat_primrec.comp
      (Primrec.snd.comp point) divisor)

end PeriodicVariablePlacement

end LeanTrominoes
