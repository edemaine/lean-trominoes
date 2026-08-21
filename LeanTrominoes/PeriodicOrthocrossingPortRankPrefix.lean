/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPorts

/-! # Port ranks as filtered prefix lengths -/

namespace LeanTrominoes

namespace List

/-- The index of a selected member in a filtered list is the number of
selected elements before its first occurrence in the original list. -/
theorem idxOf_filter_eq_filter_take_idxOf_length
    {α : Type*} [DecidableEq α]
    (predicate : α → Bool) (values : List α) (target : α)
    (targetMember : target ∈ values)
    (targetSelected : predicate target = true) :
    (values.filter predicate).idxOf target =
      ((values.take (values.idxOf target)).filter predicate).length := by
  induction values with
  | nil => simp at targetMember
  | cons head tail induction =>
      by_cases same : head = target
      · subst head
        simp [targetSelected]
      · have targetMemberTail : target ∈ tail := by
          simpa [same, Ne.symm same] using targetMember
        have tailEquality := induction targetMemberTail
        cases headSelected : predicate head <;>
          simp [same, headSelected, tailEquality]

end List

namespace PeriodicOrthocrossing

/-- A port's local rank is exactly the number of earlier global ports attached
to the same vertex. -/
theorem portRank_eq_sameVertexPrefixLength
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (port : GraphPort Vertex)
    (portMember : port ∈ allPorts graph) :
    portRank graph port =
      (((allPorts graph).take ((allPorts graph).idxOf port)).filter
        fun candidate => candidate.vertex = port.vertex).length := by
  unfold portRank portsAt
  exact List.idxOf_filter_eq_filter_take_idxOf_length
    (fun candidate => decide (candidate.vertex = port.vertex))
    (allPorts graph) port portMember (by simp)

end PeriodicOrthocrossing
end LeanTrominoes
