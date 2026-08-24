/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import LeanTrominoes.DelimitedBinaryWordPairFintypeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagControlData

/-! # Finiteness of route-descriptor pair tagger data -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags

instance sideFintype : Fintype Side := derive_fintype% Side
instance tokenFintype : Fintype Token := derive_fintype% Token
instance controlFintype : Fintype Control := derive_fintype% Control

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairFieldTags
