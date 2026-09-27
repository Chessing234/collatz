import CollatzTargetDensity.Dynamics
import Erdos1135.Tao.Syracuse.Basic

namespace CollatzTargetDensity
open Erdos1135

/-- The arithmetic input to the analytic argument: every finite ternary class
    contains arbitrarily large nonperiodic immediate predecessors. -/
def SeedSupply (target : ℕ) : Prop :=
  ∀ q X : ℕ, ∀ r : Fin (3 ^ q), ∃ M : ℕ,
    Odd M ∧ X < M ∧ Tao.syracuse M = target ∧ M % 3 ^ q = r ∧
      Nonperiodic Tao.syracuse M

end CollatzTargetDensity
