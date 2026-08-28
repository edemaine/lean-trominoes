/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarPeriodicizationComputability

/-! # Canonical encodings of routed planar-SAT variables -/

/-
The existing planar-periodicization computability layer supplies the
canonical `Primcodable` instances for indexed segments, crossing records and
ports, routed planar-SAT variables, and their opaque periodic wrappers.  This
leaf gives downstream numeric-code constructions one lightweight import for
that complete instance chain.
-/
