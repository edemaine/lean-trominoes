import LeanTrominoes.PeriodicOneInThreeToThreeDMEncodingSemantics

/-!
# Correctness of the natural-number periodic 3DM encoding

The generic incidence permutation is specialized to all three colors of the
exact-one construction.  Mapping those permutations through encoded or
decoded assignments preserves incident truth values and hence exact cover in
both directions.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Encoding a typed assignment preserves generic colored incident values up
to permutation. -/
theorem encode_incidentValues_perm
    {Variable Element : Type*}
    [DecidableEq Variable] [DecidableEq Element]
    (problem : TypedPeriodicThreeDM Variable)
    (elements : List Element)
    (reference : Triple Variable → Reference Element)
    (color : Gadget.WireColor)
    (referenceEncoded :
      ∀ triple,
        (problem.encodeTriple triple).reference color =
          encodeReference elements (reference triple))
    (referencesListed :
      ∀ triple ∈ problem.triples,
        (reference triple).atom ∈ elements)
    (triplesNodup : problem.triples.Nodup)
    (assignment : problem.MatchingAssignment)
    (atom : Element) (atomMember : atom ∈ elements)
    (cell : Cell) :
    List.Perm
      (problem.encode.incidentValues
        (problem.encode.liftAssignment
          (problem.encodeAssignment assignment))
        color (elements.idxOf atom) cell)
      ((referenceIncidences problem reference atom).map
        fun incidence =>
          problem.incidenceValue assignment incidence cell) := by
  have incidencePerm :=
    encode_incidences_perm problem elements reference color
      referenceEncoded referencesListed triplesNodup atom atomMember
  have valuePerm :=
    incidencePerm.map fun incidence =>
      problem.encodeAssignment assignment incidence.tripleIndex
        (Cell.sub cell incidence.offset)
  have rightEq :
      (((referenceIncidences problem reference atom).map
        problem.encodeIncidence).map fun incidence =>
          problem.encodeAssignment assignment incidence.tripleIndex
            (Cell.sub cell incidence.offset)) =
        (referenceIncidences problem reference atom).map
          fun incidence =>
            problem.incidenceValue assignment incidence cell := by
    rw [List.map_map]
    apply List.map_congr_left
    intro incidence incidenceMember
    change
      problem.encodeAssignment assignment
          (problem.triples.idxOf incidence.triple)
          (Cell.sub cell incidence.offset) =
        assignment incidence.triple
          (Cell.sub cell incidence.offset)
    rw [problem.encodeAssignment_idxOf
      assignment incidence.triple
      (triple_mem_of_mem_referenceIncidences
        problem reference atom incidence incidenceMember)
      (Cell.sub cell incidence.offset)]
  rw [← rightEq]
  simpa [PeriodicThreeDM.incidentValues,
    PeriodicThreeDM.liftAssignment] using valuePerm

/-- Decoding a numbered assignment likewise preserves generic incident
values up to permutation. -/
theorem decode_incidentValues_perm
    {Variable Element : Type*}
    [DecidableEq Variable] [DecidableEq Element]
    (problem : TypedPeriodicThreeDM Variable)
    (elements : List Element)
    (reference : Triple Variable → Reference Element)
    (color : Gadget.WireColor)
    (referenceEncoded :
      ∀ triple,
        (problem.encodeTriple triple).reference color =
          encodeReference elements (reference triple))
    (referencesListed :
      ∀ triple ∈ problem.triples,
        (reference triple).atom ∈ elements)
    (triplesNodup : problem.triples.Nodup)
    (assignment : problem.encode.MatchingAssignment)
    (atom : Element) (atomMember : atom ∈ elements)
    (cell : Cell) :
    List.Perm
      (problem.encode.incidentValues
        (problem.encode.liftAssignment assignment)
        color (elements.idxOf atom) cell)
      ((referenceIncidences problem reference atom).map
        fun incidence =>
          problem.incidenceValue
            (problem.decodeAssignment assignment)
            incidence cell) := by
  have incidencePerm :=
    encode_incidences_perm problem elements reference color
      referenceEncoded referencesListed triplesNodup atom atomMember
  have valuePerm :=
    incidencePerm.map fun incidence =>
      assignment incidence.tripleIndex
        (Cell.sub cell incidence.offset)
  simpa [PeriodicThreeDM.incidentValues,
    PeriodicThreeDM.liftAssignment,
    TypedPeriodicThreeDM.decodeAssignment,
    TypedPeriodicThreeDM.encodeIncidence,
    TypedPeriodicThreeDM.incidenceValue,
    List.map_map, Function.comp_def] using valuePerm

/-- Encoded red incident values are a permutation of typed red values. -/
theorem encoded_redIncidentValues_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (atom : RedElement Variable)
    (atomMember : atom ∈ redElements source) (cell : Cell) :
    List.Perm
      ((encodedProblem source).incidentValues
        ((encodedProblem source).liftAssignment
          ((problem source).encodeAssignment assignment))
        .red ((redElements source).idxOf atom) cell)
      ((problem source).redIncidentValues
        assignment atom cell) := by
  simpa [encodedProblem, problem,
    TypedPeriodicThreeDM.redIncidentValues,
    TypedPeriodicThreeDM.redIncidences,
    referenceIncidences] using
      encode_incidentValues_perm
        (problem source) (redElements source)
        (fun triple => (tripleReferences source triple).red)
        .red
        (by intro triple; rfl)
        (fun triple tripleMember =>
          (problem_isWellFormed source
            triple tripleMember).1)
        (triples_nodup source) assignment atom atomMember cell

/-- Encoded green incident values are a permutation of typed green values. -/
theorem encoded_greenIncidentValues_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (atom : GreenElement Variable)
    (atomMember : atom ∈ greenElements source) (cell : Cell) :
    List.Perm
      ((encodedProblem source).incidentValues
        ((encodedProblem source).liftAssignment
          ((problem source).encodeAssignment assignment))
        .green ((greenElements source).idxOf atom) cell)
      ((problem source).greenIncidentValues
        assignment atom cell) := by
  simpa [encodedProblem, problem,
    TypedPeriodicThreeDM.greenIncidentValues,
    TypedPeriodicThreeDM.greenIncidences,
    referenceIncidences] using
      encode_incidentValues_perm
        (problem source) (greenElements source)
        (fun triple => (tripleReferences source triple).green)
        .green
        (by intro triple; rfl)
        (fun triple tripleMember =>
          (problem_isWellFormed source
            triple tripleMember).2.1)
        (triples_nodup source) assignment atom atomMember cell

/-- Encoded blue incident values are a permutation of typed blue values. -/
theorem encoded_blueIncidentValues_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (atom : BlueElement Variable)
    (atomMember : atom ∈ blueElements source) (cell : Cell) :
    List.Perm
      ((encodedProblem source).incidentValues
        ((encodedProblem source).liftAssignment
          ((problem source).encodeAssignment assignment))
        .blue ((blueElements source).idxOf atom) cell)
      ((problem source).blueIncidentValues
        assignment atom cell) := by
  simpa [encodedProblem, problem,
    TypedPeriodicThreeDM.blueIncidentValues,
    TypedPeriodicThreeDM.blueIncidences,
    referenceIncidences] using
      encode_incidentValues_perm
        (problem source) (blueElements source)
        (fun triple => (tripleReferences source triple).blue)
        .blue
        (by intro triple; rfl)
        (fun triple tripleMember =>
          (problem_isWellFormed source
            triple tripleMember).2.2)
        (triples_nodup source) assignment atom atomMember cell

/-- Decoded red incident values are a permutation of numbered red values. -/
theorem decoded_redIncidentValues_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (encodedProblem source).MatchingAssignment)
    (atom : RedElement Variable)
    (atomMember : atom ∈ redElements source) (cell : Cell) :
    List.Perm
      ((encodedProblem source).incidentValues
        ((encodedProblem source).liftAssignment assignment)
        .red ((redElements source).idxOf atom) cell)
      ((problem source).redIncidentValues
        ((problem source).decodeAssignment assignment)
        atom cell) := by
  simpa [encodedProblem, problem,
    TypedPeriodicThreeDM.redIncidentValues,
    TypedPeriodicThreeDM.redIncidences,
    referenceIncidences] using
      decode_incidentValues_perm
        (problem source) (redElements source)
        (fun triple => (tripleReferences source triple).red)
        .red
        (by intro triple; rfl)
        (fun triple tripleMember =>
          (problem_isWellFormed source
            triple tripleMember).1)
        (triples_nodup source) assignment atom atomMember cell

/-- Decoded green incident values are a permutation of numbered green
values. -/
theorem decoded_greenIncidentValues_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (encodedProblem source).MatchingAssignment)
    (atom : GreenElement Variable)
    (atomMember : atom ∈ greenElements source) (cell : Cell) :
    List.Perm
      ((encodedProblem source).incidentValues
        ((encodedProblem source).liftAssignment assignment)
        .green ((greenElements source).idxOf atom) cell)
      ((problem source).greenIncidentValues
        ((problem source).decodeAssignment assignment)
        atom cell) := by
  simpa [encodedProblem, problem,
    TypedPeriodicThreeDM.greenIncidentValues,
    TypedPeriodicThreeDM.greenIncidences,
    referenceIncidences] using
      decode_incidentValues_perm
        (problem source) (greenElements source)
        (fun triple => (tripleReferences source triple).green)
        .green
        (by intro triple; rfl)
        (fun triple tripleMember =>
          (problem_isWellFormed source
            triple tripleMember).2.1)
        (triples_nodup source) assignment atom atomMember cell

/-- Decoded blue incident values are a permutation of numbered blue values. -/
theorem decoded_blueIncidentValues_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (encodedProblem source).MatchingAssignment)
    (atom : BlueElement Variable)
    (atomMember : atom ∈ blueElements source) (cell : Cell) :
    List.Perm
      ((encodedProblem source).incidentValues
        ((encodedProblem source).liftAssignment assignment)
        .blue ((blueElements source).idxOf atom) cell)
      ((problem source).blueIncidentValues
        ((problem source).decodeAssignment assignment)
        atom cell) := by
  simpa [encodedProblem, problem,
    TypedPeriodicThreeDM.blueIncidentValues,
    TypedPeriodicThreeDM.blueIncidences,
    referenceIncidences] using
      decode_incidentValues_perm
        (problem source) (blueElements source)
        (fun triple => (tripleReferences source triple).blue)
        .blue
        (by intro triple; rfl)
        (fun triple tripleMember =>
          (problem_isWellFormed source
            triple tripleMember).2.2)
        (triples_nodup source) assignment atom atomMember cell

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
