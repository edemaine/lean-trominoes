import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned
import LeanTrominoes.PeriodicEightOccurrenceSplitComputability
import LeanTrominoes.PositionedPeriodicCNFComputability

/-!
# Computability of positioned fixed-eight occurrence splitting

The fixed nine-copy implication ring has primitive-recursive local geometry.
Consequently its positioned periodic formula and companion placement are
primitive recursive whenever the source positioned formula, source period,
source variable positions, and occurrence-port lookup are primitive recursive
in a common external input.
-/

noncomputable section

namespace LeanTrominoes

namespace OccurrenceSplitRing

deriving instance Fintype for RingVertex

noncomputable instance : Primcodable RingVertex :=
  Primcodable.ofEquiv (Fin (Fintype.card RingVertex))
    (Fintype.equivFin RingVertex)

theorem ringVariablePosition_primrec : Primrec ringVariablePosition :=
  Primrec.dom_finite ringVariablePosition

theorem cycleClausePosition_primrec : Primrec cycleClausePosition :=
  Primrec.dom_finite cycleClausePosition

theorem presentedCycleVertices_primrec :
    Primrec fun (_ : Unit) => presentedCycleVertices :=
  Primrec.const presentedCycleVertices

end OccurrenceSplitRing

namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

theorem ringVertexOfIndex_primrec : Primrec ringVertexOfIndex := by
  let vertices : List RingVertex :=
    [.port .northwest, .port .north, .port .northeast, .port .east,
      .port .southeast, .port .south, .port .southwest, .port .west]
  have implementation : Primrec fun index : Nat =>
      vertices.getD index .separator :=
    (Primrec.list_getD (.separator : RingVertex)).comp
      (Primrec.const vertices) Primrec.id
  exact implementation.of_eq fun index => by
    unfold vertices
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index
    · rfl
    rcases index with _ | index <;> rfl

end PeriodicEightOccurrenceSplit

namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicThreeSATThree

theorem macroOrigin_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : Input × Variable =>
      macroOrigin (sourcePlacement input.1) input.2 := by
  exact Computability.cell_sub_primrec.comp
    (Computability.cell_scale_primrec.comp
      (Primrec.const refinementScale) positionPrimrec)
    (Primrec.const (12, 12))

theorem occurrenceVariablePosition_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : Input × ThreeOccurrenceVariable Variable =>
      occurrenceVariablePosition (sourcePlacement input.1) input.2 := by
  have origin : Primrec fun input :
      Input × ThreeOccurrenceVariable Variable =>
      macroOrigin (sourcePlacement input.1) input.2.1 :=
    macroOrigin_primrec sourcePlacement positionPrimrec |>.comp
      (Primrec.pair Primrec.fst
        (Primrec.fst.comp Primrec.snd))
  have vertex : Primrec fun input :
      Input × ThreeOccurrenceVariable Variable =>
      PeriodicEightOccurrenceSplit.ringVertexOfIndex input.2.2.1 :=
    PeriodicEightOccurrenceSplit.ringVertexOfIndex_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact Computability.cell_add_primrec.comp origin
    (OccurrenceSplitRing.ringVariablePosition_primrec.comp vertex)

theorem occurrenceClause_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (occurrencePorts : Input → PeriodicEightOccurrenceSplit.OccurrencePorts)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (occurrencePorts input.1.1).port input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × PositionedPeriodicClause Variable =>
      occurrenceClause (occurrencePorts input.1.1)
        input.1.2 input.2 := by
  have position : Primrec fun input :
      (Input × Nat) × PositionedPeriodicClause Variable =>
      Cell.scale refinementScale input.2.position :=
    Computability.cell_scale_primrec.comp
      (Primrec.const refinementScale)
      (PositionedPeriodicClause.position_primrec.comp Primrec.snd)
  have literals : Primrec fun input :
      (Input × Nat) × PositionedPeriodicClause Variable =>
      PeriodicEightOccurrenceSplit.occurrenceClause
        (occurrencePorts input.1.1)
        input.1.2 input.2.literals :=
    PeriodicEightOccurrenceSplit.occurrenceClause_primrec
      (fun input => (occurrencePorts input).port) portsPrimrec |>.comp
        (Primrec.pair Primrec.fst
          (PositionedPeriodicClause.literals_primrec.comp Primrec.snd))
  exact PositionedPeriodicClause.mk_primrec.comp
    (Primrec.pair position literals)

theorem occurrenceClauses_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (occurrencePorts : Input → PeriodicEightOccurrenceSplit.OccurrencePorts)
    (sourcePrimrec : Primrec source)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (occurrencePorts input.1.1).port input.1.2 input.2) :
    Primrec fun input => occurrenceClauses (source input)
      (occurrencePorts input) := by
  have tagged : Primrec fun input : Input =>
      (source input).clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicCNF.clauses_primrec.comp sourcePrimrec)
  have clause : Primrec₂ fun (input : Input)
      (item : PositionedPeriodicClause Variable × Nat) =>
      occurrenceClause (occurrencePorts input) item.2 item.1 := by
    change Primrec fun combined :
        Input × (PositionedPeriodicClause Variable × Nat) =>
      occurrenceClause (occurrencePorts combined.1)
        combined.2.2 combined.2.1
    exact occurrenceClause_primrec occurrencePorts portsPrimrec |>.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
  exact Primrec.list_map tagged clause

theorem cycleClause_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : (Input × Variable) ×
        (PeriodicClause (ThreeOccurrenceVariable Variable) × Nat) =>
      cycleClause
        (sourcePlacement input.1.1)
        input.1.2 input.2 := by
  have origin : Primrec fun input : (Input × Variable) ×
      (PeriodicClause (ThreeOccurrenceVariable Variable) × Nat) =>
      macroOrigin (sourcePlacement input.1.1) input.1.2 :=
    macroOrigin_primrec sourcePlacement positionPrimrec |>.comp Primrec.fst
  have vertex : Primrec fun input : (Input × Variable) ×
      (PeriodicClause (ThreeOccurrenceVariable Variable) × Nat) =>
      presentedCycleVertices.getD input.2.2 .separator :=
    (Primrec.list_getD (.separator : RingVertex)).comp
      (Primrec.const presentedCycleVertices)
      (Primrec.snd.comp Primrec.snd)
  have clausePosition : Primrec fun input : (Input × Variable) ×
      (PeriodicClause (ThreeOccurrenceVariable Variable) × Nat) =>
      Cell.add
        (macroOrigin (sourcePlacement input.1.1) input.1.2)
        (cycleClausePosition
          (presentedCycleVertices.getD input.2.2 .separator)) :=
    Computability.cell_add_primrec.comp origin
      (OccurrenceSplitRing.cycleClausePosition_primrec.comp vertex)
  exact PositionedPeriodicClause.mk_primrec.comp
    (Primrec.pair clausePosition
      (Primrec.fst.comp Primrec.snd))

theorem cycleClausesFor_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : Input × Variable =>
      cycleClausesFor (sourcePlacement input.1) input.2 := by
  have tagged : Primrec fun input : Input × Variable =>
      (PeriodicEightOccurrenceSplit.cycleClausesFor input.2).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicEightOccurrenceSplit.cycleClausesFor_primrec.comp Primrec.snd)
  have clause : Primrec₂ fun (input : Input × Variable)
      (taggedClause :
        PeriodicClause (ThreeOccurrenceVariable Variable) × Nat) =>
      cycleClause (sourcePlacement input.1) input.2 taggedClause :=
    (cycleClause_primrec sourcePlacement positionPrimrec).to₂
  exact Primrec.list_map tagged clause

theorem allCycleClauses_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input => allCycleClauses (source input)
      (sourcePlacement input) := by
  have atoms : Primrec fun input : Input =>
      PeriodicThreeSATThree.sourceVariables (source input).erase :=
    PeriodicThreeSATThree.sourceVariables_primrec.comp
      (PositionedPeriodicCNF.erase_primrec.comp sourcePrimrec)
  have cycles : Primrec₂ fun (input : Input) (atom : Variable) =>
      cycleClausesFor (sourcePlacement input) atom :=
    (cycleClausesFor_primrec sourcePlacement positionPrimrec).to₂
  exact Primrec.list_flatMap atoms cycles

/-- Positioned fixed-eight occurrence splitting is primitive recursive from
primitive-recursive finite source data, source positions, and port lookup. -/
theorem formula_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (occurrencePorts : Input →
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (sourcePrimrec : Primrec source)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      (occurrencePorts input.1.1).port input.1.2 input.2) :
    Primrec fun input => formula (source input)
      (sourcePlacement input)
      (occurrencePorts input) := by
  have clauses : Primrec fun input =>
      occurrenceClauses (source input) (occurrencePorts input) ++
        allCycleClauses (source input)
          (sourcePlacement input) :=
    Primrec.list_append.comp
      (occurrenceClauses_primrec source occurrencePorts sourcePrimrec portsPrimrec)
      (allCycleClauses_primrec source sourcePlacement sourcePrimrec positionPrimrec)
  exact (PositionedPeriodicCNF.mk_primrec.comp clauses).of_eq
    fun _ => rfl

theorem placement_period_primrec
    {Input Variable : Type*} [Primcodable Input]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (periodPrimrec : Primrec fun input => (sourcePlacement input).period) :
    Primrec fun input =>
      (placement (sourcePlacement input)).period := by
  exact (Primrec.nat_mul.comp
    (Primrec.const refinementScale.toNat) periodPrimrec).of_eq fun _ => rfl

theorem placement_position_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (positionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2) :
    Primrec fun input : Input × ThreeOccurrenceVariable Variable =>
      (placement (sourcePlacement input.1)).position input.2 :=
  occurrenceVariablePosition_primrec sourcePlacement positionPrimrec

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
