import LeanTrominoes.PeriodicCNFGaugeComputability
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerComputability
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering
import LeanTrominoes.PrimrecListSort

/-!
# Computability of route-direction clause ordering

The planar reductions stably sort each finite clause by the first directions
of its incidence routes.  This module gives the finite positioned structures
their canonical encodings and proves that the sort is primitive recursive
whenever the source clauses and route lookup are primitive recursive in a
common external input.
-/

noncomputable section

namespace LeanTrominoes

namespace PositionedPeriodicClause

def equivData {Variable : Type*} :
    PositionedPeriodicClause Variable ≃ Cell × PeriodicClause Variable where
  toFun clause := (clause.position, clause.literals)
  invFun data := ⟨data.1, data.2⟩
  left_inv clause := by cases clause; rfl
  right_inv data := by cases data; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (PositionedPeriodicClause Variable) :=
  Primcodable.ofEquiv (Cell × PeriodicClause Variable) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@equivData Variable) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@equivData Variable).symm :=
  Primrec.of_equiv_symm

theorem position_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (PositionedPeriodicClause.position :
      PositionedPeriodicClause Variable → Cell) :=
  Primrec.fst.comp equivData_primrec

theorem literals_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (PositionedPeriodicClause.literals :
      PositionedPeriodicClause Variable → PeriodicClause Variable) :=
  Primrec.snd.comp equivData_primrec

end PositionedPeriodicClause

namespace PositionedPeriodicCNF

def equivData {Variable : Type*} :
    PositionedPeriodicCNF Variable ≃
      List (PositionedPeriodicClause Variable) where
  toFun formula := formula.clauses
  invFun clauses := ⟨clauses⟩
  left_inv formula := by cases formula; rfl
  right_inv _ := rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (PositionedPeriodicCNF Variable) :=
  Primcodable.ofEquiv (List (PositionedPeriodicClause Variable)) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@equivData Variable) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@equivData Variable).symm :=
  Primrec.of_equiv_symm

theorem clauses_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (PositionedPeriodicCNF.clauses :
      PositionedPeriodicCNF Variable →
        List (PositionedPeriodicClause Variable)) :=
  equivData_primrec

end PositionedPeriodicCNF

namespace AxisDirection

theorem clockwiseRank_primrec : Primrec clockwiseRank :=
  Primrec.dom_finite clockwiseRank

end AxisDirection

namespace PositionedPeriodicCNF

set_option maxHeartbeats 800000

theorem clauseLiteralDirectionRank_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → IncidenceRoutes)
    (routesPrimrec :
      Primrec fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Primrec fun input :
        (Input × Nat) × (PeriodicLiteral Variable × Nat) =>
      clauseLiteralDirectionRank (routes input.1.1)
        input.1.2 input.2 := by
  have route : Primrec fun input :
      (Input × Nat) × (PeriodicLiteral Variable × Nat) =>
      routes input.1.1 input.1.2 input.2.2 :=
    routesPrimrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
  exact (AxisDirection.clockwiseRank_primrec.comp
    (PeriodicThreeDM.NormalizationCompiler.polylineFirstDirection_primrec.comp
      route)).of_eq fun _ => rfl

theorem clauseLiteralOrder_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → IncidenceRoutes)
    (routesPrimrec :
      Primrec fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Primrec fun input :
        (Input × Nat) × PositionedPeriodicClause Variable =>
      clauseLiteralOrder (routes input.1.1) input.1.2 input.2 := by
  let SortInput :=
    (Input × Nat) × PositionedPeriodicClause Variable
  let TaggedLiteral := PeriodicLiteral Variable × Nat
  let items : SortInput → List TaggedLiteral := fun input =>
    input.2.literals.zipIdx
  let lessEq : SortInput → TaggedLiteral → TaggedLiteral → Bool :=
    fun input first second => decide
      (clauseLiteralDirectionRank (routes input.1.1)
          input.1.2 first ≤
        clauseLiteralDirectionRank (routes input.1.1)
          input.1.2 second)
  have itemsPrimrec : Primrec items := by
    exact PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)
  have rankFirst : Primrec fun input :
      (SortInput × TaggedLiteral) × TaggedLiteral =>
      clauseLiteralDirectionRank (routes input.1.1.1.1)
        input.1.1.1.2 input.1.2 := by
    exact clauseLiteralDirectionRank_primrec routes routesPrimrec |>.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
  have rankSecond : Primrec fun input :
      (SortInput × TaggedLiteral) × TaggedLiteral =>
      clauseLiteralDirectionRank (routes input.1.1.1.1)
        input.1.1.1.2 input.2 := by
    exact clauseLiteralDirectionRank_primrec routes routesPrimrec |>.comp
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)
  have lessEqPrimrec : Primrec fun input :
      (SortInput × TaggedLiteral) × TaggedLiteral =>
      lessEq input.1.1 input.1.2 input.2 := by
    exact (Primrec.nat_le.comp rankFirst rankSecond).decide
  have sorted := Computability.boolInsertionSort_primrec
    items lessEq itemsPrimrec lessEqPrimrec
  apply sorted.of_eq
  intro input
  exact Computability.boolInsertionSort_eq_insertionSort
    (lessEq input)
    (clauseLiteralDirectionLE (routes input.1.1) input.1.2)
    (fun first second => by
      simp [lessEq, clauseLiteralDirectionLE])
    (items input)

theorem orderClauseByRouteDirection_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → IncidenceRoutes)
    (routesPrimrec :
      Primrec fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Primrec fun input :
        (Input × Nat) × PositionedPeriodicClause Variable =>
      orderClauseByRouteDirection
        (routes input.1.1) input.1.2 input.2 := by
  let OrderInput :=
    (Input × Nat) × PositionedPeriodicClause Variable
  have ordered : Primrec fun input : OrderInput =>
      clauseLiteralOrder (routes input.1.1) input.1.2 input.2 :=
    clauseLiteralOrder_primrec routes routesPrimrec
  have literals : Primrec fun input : OrderInput =>
      (clauseLiteralOrder
        (routes input.1.1) input.1.2 input.2).map Prod.fst :=
    Primrec.list_map ordered
      ((Primrec.fst.comp Primrec.snd).to₂)
  have data : Primrec fun input : OrderInput =>
      (input.2.position,
        (clauseLiteralOrder
          (routes input.1.1) input.1.2 input.2).map Prod.fst) :=
    Primrec.pair
      (PositionedPeriodicClause.position_primrec.comp Primrec.snd)
      literals
  exact (PositionedPeriodicClause.equivData_symm_primrec.comp data).of_eq
    fun _ => rfl

theorem orderClausesByRouteDirection_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (routes : Input → IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (routesPrimrec :
      Primrec fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Primrec fun input =>
      orderClausesByRouteDirection (source input) (routes input) := by
  have tagged : Primrec fun input : Input =>
      (source input).clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicCNF.clauses_primrec.comp sourcePrimrec)
  have one : Primrec₂ fun (input : Input)
      (taggedClause : PositionedPeriodicClause Variable × Nat) =>
      orderClauseByRouteDirection
        (routes input) taggedClause.2 taggedClause.1 := by
    change Primrec fun combined : Input ×
        (PositionedPeriodicClause Variable × Nat) =>
      orderClauseByRouteDirection
        (routes combined.1) combined.2.2 combined.2.1
    exact orderClauseByRouteDirection_primrec routes routesPrimrec |>.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
  have clauses : Primrec fun input =>
      (source input).clauses.zipIdx.map fun taggedClause =>
        orderClauseByRouteDirection
          (routes input) taggedClause.2 taggedClause.1 :=
    Primrec.list_map tagged one
  exact (PositionedPeriodicCNF.equivData_symm_primrec.comp clauses).of_eq
    fun _ => rfl

/-- Reindexing a route family through the primitive-recursive stable clause
sort is itself primitive recursive. -/
theorem orderRoutesByClauseDirection_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (routes : Input → IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (routesPrimrec :
      Primrec fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      orderRoutesByClauseDirection
        (source input.1.1) (routes input.1.1)
        input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have selectedClause : Primrec fun input : Query =>
      (source input.1.1).clauses[input.1.2]? :=
    Primrec.list_getElem?.comp
      (PositionedPeriodicCNF.clauses_primrec.comp
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst)
  have noClause : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (clause : PositionedPeriodicClause Variable) =>
      match
          (clauseLiteralOrder (routes input.1.1)
            input.1.2 clause)[input.2]? with
      | Option.none => []
      | Option.some taggedLiteral =>
          routes input.1.1 input.1.2 taggedLiteral.2 := by
    let Combined := Query × PositionedPeriodicClause Variable
    have ordered : Primrec fun input : Combined =>
        clauseLiteralOrder (routes input.1.1.1)
          input.1.1.2 input.2 :=
      (clauseLiteralOrder_primrec routes routesPrimrec).comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          Primrec.snd)
    have selectedLiteral : Primrec fun input : Combined =>
        (clauseLiteralOrder (routes input.1.1.1)
          input.1.1.2 input.2)[input.1.2]? :=
      Primrec.list_getElem?.comp ordered
        (Primrec.snd.comp Primrec.fst)
    have noLiteral : Primrec fun _input : Combined =>
        ([] : List Cell) :=
      Primrec.const []
    have oneLiteral : Primrec₂ fun (input : Combined)
        (taggedLiteral : PeriodicLiteral Variable × Nat) =>
        routes input.1.1.1 input.1.1.2 taggedLiteral.2 := by
      change Primrec fun input : Combined ×
          (PeriodicLiteral Variable × Nat) =>
        routes input.1.1.1.1 input.1.1.1.2 input.2.2
      exact routesPrimrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp
              (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp (Primrec.fst.comp
              (Primrec.fst.comp Primrec.fst))))
          (Primrec.snd.comp Primrec.snd))
    change Primrec fun input : Combined =>
      match
          (clauseLiteralOrder (routes input.1.1.1)
            input.1.1.2 input.2)[input.1.2]? with
      | Option.none => []
      | Option.some taggedLiteral =>
          routes input.1.1.1 input.1.1.2 taggedLiteral.2
    exact (Primrec.option_casesOn
      selectedLiteral noLiteral oneLiteral).of_eq fun input => by
        cases (clauseLiteralOrder (routes input.1.1.1)
          input.1.1.2 input.2)[input.1.2]? <;> rfl
  exact (Primrec.option_casesOn selectedClause noClause some).of_eq
    fun input => by
      unfold orderRoutesByClauseDirection
      cases (source input.1.1).clauses[input.1.2]? <;> rfl

/-- Canonical route reindexing, including the whole-period change of clause
anchor gauge, is primitive recursive from the source formula, placement
period, and route lookup. -/
theorem orderCanonicalRoutesByClauseDirection_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (placement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input => (placement input).period)
    (routesPrimrec :
      Primrec fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      orderCanonicalRoutesByClauseDirection
        (source input.1.1) (placement input.1.1)
        (routes input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have selectedClause : Primrec fun input : Query =>
      (source input.1.1).clauses[input.1.2]? :=
    Primrec.list_getElem?.comp
      (PositionedPeriodicCNF.clauses_primrec.comp
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst)
  have noClause : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (sourceClause : PositionedPeriodicClause Variable) =>
      let orderedClause := orderClauseByRouteDirection
        (routes input.1.1) input.1.2 sourceClause
      PeriodicOrthocrossing.translatePolyline
        ((placement input.1.1).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor sourceClause.literals)
            (PeriodicCNF.clauseAnchor orderedClause.literals)))
        (orderRoutesByClauseDirection
          (source input.1.1) (routes input.1.1)
          input.1.2 input.2) := by
    let Combined := Query × PositionedPeriodicClause Variable
    have orderedClause : Primrec fun input : Combined =>
        orderClauseByRouteDirection
          (routes input.1.1.1) input.1.1.2 input.2 :=
      (orderClauseByRouteDirection_primrec routes routesPrimrec).comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          Primrec.snd)
    have sourceAnchor : Primrec fun input : Combined =>
        PeriodicCNF.clauseAnchor input.2.literals :=
      PeriodicCNF.clauseAnchor_primrec.comp
        (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)
    have orderedAnchor : Primrec fun input : Combined =>
        PeriodicCNF.clauseAnchor
          (orderClauseByRouteDirection
            (routes input.1.1.1) input.1.1.2 input.2).literals :=
      PeriodicCNF.clauseAnchor_primrec.comp
        (PositionedPeriodicClause.literals_primrec.comp orderedClause)
    have anchorDifference : Primrec fun input : Combined => Cell.sub
        (PeriodicCNF.clauseAnchor input.2.literals)
        (PeriodicCNF.clauseAnchor
          (orderClauseByRouteDirection
            (routes input.1.1.1) input.1.1.2 input.2).literals) :=
      Computability.cell_sub_primrec.comp sourceAnchor orderedAnchor
    have physicalPeriod : Primrec fun input : Combined =>
        ((placement input.1.1.1).period : Int) :=
      Computability.int_ofNat_primrec.comp
        (periodPrimrec.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    have translation : Primrec fun input : Combined =>
        (placement input.1.1.1).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor input.2.literals)
            (PeriodicCNF.clauseAnchor
              (orderClauseByRouteDirection
                (routes input.1.1.1) input.1.1.2 input.2).literals)) :=
      Computability.cell_scale_primrec.comp
        physicalPeriod anchorDifference
    have reorderedRoute : Primrec fun input : Combined =>
        orderRoutesByClauseDirection
          (source input.1.1.1) (routes input.1.1.1)
          input.1.1.2 input.1.2 :=
      (orderRoutesByClauseDirection_primrec
        source routes sourcePrimrec routesPrimrec).comp Primrec.fst
    change Primrec fun input : Combined =>
      PeriodicOrthocrossing.translatePolyline
        ((placement input.1.1.1).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor input.2.literals)
            (PeriodicCNF.clauseAnchor
              (orderClauseByRouteDirection
                (routes input.1.1.1) input.1.1.2 input.2).literals)))
        (orderRoutesByClauseDirection
          (source input.1.1.1) (routes input.1.1.1)
          input.1.1.2 input.1.2)
    exact PeriodicThreeDM.NormalizationCompiler.translatePolyline_primrec.comp
      (Primrec.pair translation reorderedRoute)
  exact (Primrec.option_casesOn selectedClause noClause some).of_eq
    fun input => by
      unfold orderCanonicalRoutesByClauseDirection
      cases (source input.1.1).clauses[input.1.2]? <;> rfl

/-! ## Computable route lookup -/

/-- The direction rank remains computable when route lookup is merely
computable. -/
theorem clauseLiteralDirectionRank_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → IncidenceRoutes)
    (routesComputable :
      Computable fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Computable fun input :
        (Input × Nat) × (PeriodicLiteral Variable × Nat) =>
      clauseLiteralDirectionRank (routes input.1.1)
        input.1.2 input.2 := by
  have route : Computable fun input :
      (Input × Nat) × (PeriodicLiteral Variable × Nat) =>
      routes input.1.1 input.1.2 input.2.2 :=
    routesComputable.comp
      (show Computable fun input :
          (Input × Nat) × (PeriodicLiteral Variable × Nat) =>
          ((input.1.1, input.1.2), input.2.2) from
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)).to_comp)
  exact (AxisDirection.clockwiseRank_primrec.to_comp.comp
    (PeriodicThreeDM.NormalizationCompiler.polylineFirstDirection_primrec.to_comp.comp
      route)).of_eq fun _ => rfl

/-- Literal sorting in one positioned clause is computable from a
computable route lookup. -/
theorem clauseLiteralOrder_computable_of_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → IncidenceRoutes)
    (routesComputable :
      Computable fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Computable fun input :
        (Input × Nat) × PositionedPeriodicClause Variable =>
      clauseLiteralOrder (routes input.1.1) input.1.2 input.2 := by
  let SortInput :=
    (Input × Nat) × PositionedPeriodicClause Variable
  let TaggedLiteral := PeriodicLiteral Variable × Nat
  let items : SortInput → List TaggedLiteral := fun input =>
    input.2.literals.zipIdx
  let lessEq : SortInput → TaggedLiteral → TaggedLiteral → Bool :=
    fun input first second => decide
      (clauseLiteralDirectionRank (routes input.1.1)
          input.1.2 first ≤
        clauseLiteralDirectionRank (routes input.1.1)
          input.1.2 second)
  have itemsComputable : Computable items :=
    (PeriodicThreeSATThree.zipIdx_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp Primrec.snd)).to_comp
  have rankFirst : Computable fun input :
      (SortInput × TaggedLiteral) × TaggedLiteral =>
      clauseLiteralDirectionRank (routes input.1.1.1.1)
        input.1.1.1.2 input.1.2 :=
    (clauseLiteralDirectionRank_computable routes routesComputable).to₂.comp
      (Computable.fst.comp
        (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst)
  have rankSecond : Computable fun input :
      (SortInput × TaggedLiteral) × TaggedLiteral =>
      clauseLiteralDirectionRank (routes input.1.1.1.1)
        input.1.1.1.2 input.2 :=
    (clauseLiteralDirectionRank_computable routes routesComputable).to₂.comp
      (Computable.fst.comp
        (Computable.fst.comp Computable.fst))
      Computable.snd
  have lessEqComputable : Computable fun input :
      (SortInput × TaggedLiteral) × TaggedLiteral =>
      lessEq input.1.1 input.1.2 input.2 := by
    have leBool : Computable fun ranks : Nat × Nat =>
        decide (ranks.1 ≤ ranks.2) :=
      (Primrec.nat_le.comp Primrec.fst Primrec.snd).decide.to_comp
    exact leBool.to₂.comp rankFirst rankSecond
  have sorted := Computability.boolInsertionSort_computable
    items lessEq itemsComputable lessEqComputable
  apply sorted.of_eq
  intro input
  exact Computability.boolInsertionSort_eq_insertionSort
    (lessEq input)
    (clauseLiteralDirectionLE (routes input.1.1) input.1.2)
    (fun first second => by
      simp [lessEq, clauseLiteralDirectionLE])
    (items input)

/-- Rebuilding one positioned clause after computable route-direction
sorting is computable. -/
theorem orderClauseByRouteDirection_computable_of_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → IncidenceRoutes)
    (routesComputable :
      Computable fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Computable fun input :
        (Input × Nat) × PositionedPeriodicClause Variable =>
      orderClauseByRouteDirection
        (routes input.1.1) input.1.2 input.2 := by
  let OrderInput :=
    (Input × Nat) × PositionedPeriodicClause Variable
  have ordered : Computable fun input : OrderInput =>
      clauseLiteralOrder (routes input.1.1) input.1.2 input.2 :=
    clauseLiteralOrder_computable_of_computable routes routesComputable
  have literals : Computable fun input : OrderInput =>
      (clauseLiteralOrder
        (routes input.1.1) input.1.2 input.2).map Prod.fst :=
    (show Primrec fun literals :
        List (PeriodicLiteral Variable × Nat) =>
        literals.map Prod.fst from
      Primrec.list_map Primrec.id
        ((Primrec.fst.comp Primrec.snd).to₂)).to_comp.comp ordered
  have position : Computable fun input : OrderInput => input.2.position :=
    (PositionedPeriodicClause.position_primrec.comp Primrec.snd).to_comp
  have data : Computable fun input : OrderInput =>
      (input.2.position,
        (clauseLiteralOrder
          (routes input.1.1) input.1.2 input.2).map Prod.fst) :=
    Computable.pair position literals
  exact (PositionedPeriodicClause.equivData_symm_primrec.to_comp.comp data).of_eq
    fun _ => rfl

/-- Stable route-direction ordering of all clauses is computable when both
the positioned source and route lookup are computable. -/
theorem orderClausesByRouteDirection_computable_of_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (routes : Input → IncidenceRoutes)
    (sourceComputable : Computable source)
    (routesComputable :
      Computable fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Computable fun input =>
      orderClausesByRouteDirection (source input) (routes input) := by
  have tagged : Computable fun input : Input =>
      (source input).clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.to_comp.comp
      (PositionedPeriodicCNF.clauses_primrec.to_comp.comp sourceComputable)
  let PreparedClause :=
    (Input × Nat) × PositionedPeriodicClause Variable
  have prepareOne : Computable₂ fun (input : Input)
      (taggedClause : PositionedPeriodicClause Variable × Nat) =>
      (((input, taggedClause.2), taggedClause.1) : PreparedClause) :=
    (show Primrec fun combined : Input ×
        (PositionedPeriodicClause Variable × Nat) =>
        ((combined.1, combined.2.2), combined.2.1) from
      Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd)).to_comp
  let preparedClauses : Input → List PreparedClause := fun input =>
    (source input).clauses.zipIdx.map fun taggedClause =>
      (((input, taggedClause.2), taggedClause.1) : PreparedClause)
  have preparedComputable : Computable preparedClauses :=
    Computability.listMap_computable
      (fun input => (source input).clauses.zipIdx)
      (fun input taggedClause =>
        (((input, taggedClause.2), taggedClause.1) : PreparedClause))
      tagged prepareOne
  have ordered : Computable fun input : PreparedClause =>
      orderClauseByRouteDirection
        (routes input.1.1) input.1.2 input.2 :=
    orderClauseByRouteDirection_computable_of_computable
      routes routesComputable
  have one : Computable₂ fun (_ : Input)
      (preparedClause : PreparedClause) =>
      orderClauseByRouteDirection
        (routes preparedClause.1.1)
        preparedClause.1.2 preparedClause.2 := by
    change Computable fun combined : Input × PreparedClause =>
      orderClauseByRouteDirection
        (routes combined.2.1.1)
        combined.2.1.2 combined.2.2
    exact ordered.comp Computable.snd
  have clauses : Computable fun input =>
      (source input).clauses.zipIdx.map fun taggedClause =>
        orderClauseByRouteDirection
          (routes input) taggedClause.2 taggedClause.1 :=
    (Computability.listMap_computable
      preparedClauses
      (fun _ preparedClause =>
        orderClauseByRouteDirection
          (routes preparedClause.1.1)
          preparedClause.1.2 preparedClause.2)
      preparedComputable one).of_eq fun input => by
        simp [preparedClauses, PreparedClause]
  exact (PositionedPeriodicCNF.equivData_symm_primrec.to_comp.comp clauses).of_eq
    fun _ => rfl

theorem orderClausesByRouteDirection_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (routes : Input → IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (routesPrimrec :
      Primrec fun input : (Input × Nat) × Nat =>
        routes input.1.1 input.1.2 input.2) :
    Computable fun input =>
      orderClausesByRouteDirection (source input) (routes input) :=
  (orderClausesByRouteDirection_primrec
    source routes sourcePrimrec routesPrimrec).to_comp

end PositionedPeriodicCNF

end LeanTrominoes
