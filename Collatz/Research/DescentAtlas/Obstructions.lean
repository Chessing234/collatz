import Collatz.Research.DescentAtlas.Threshold

/-! Testing alternative universal descent techniques: monotone ranking and
finite-horizon coefficient certificates. Neither obstruction refutes Collatz. -/
namespace Collatz.Research.DescentAtlas

/-- A potential increasing with the input cannot strictly decrease at every
accelerated step, since the concrete input 3 increases to 5. -/
theorem no_monotone_step_ranking (V : Nat → Nat)
    (hmono : ∀ a b, a ≤ b → V a ≤ V b) :
    ¬ (∀ n, 1 < n → V (acceleratedStep n) < V n) := by
  intro h
  have hs := h 3 (by decide)
  have he : acceleratedStep 3 = 5 := by decide
  rw [he] at hs
  have hm := hmono 3 5 (by decide)
  omega

/-- Every nonnegative affine potential is covered by the obstruction. -/
theorem no_affine_step_ranking (a b : Nat) :
    ¬ (∀ n, 1 < n → a * acceleratedStep n + b < a * n + b) := by
  apply no_monotone_step_ranking (fun n => a * n + b)
  intro x y hxy
  exact Nat.add_le_add_right (Nat.mul_le_mul_left a hxy) b

/-- Natural power potentials fail for the same reason, including exponent 0. -/
theorem no_power_step_ranking (p : Nat) :
    ¬ (∀ n, 1 < n → (acceleratedStep n) ^ p < n ^ p) := by
  apply no_monotone_step_ranking (fun n => n ^ p)
  intro x y hxy
  exact Nat.pow_le_pow_left hxy p

/-- At depth eight, contracting coefficients do not guarantee descent of
the representative. The test isolates this logically different failure mode. -/
theorem contracting_without_representative_descent :
    3 ^ oddCount 7 8 < 2 ^ 8 ∧ ¬ acceleratedOrbit 8 7 < 7 := by
  decide

/-- A Boolean finite census of the nonnegative representative exceptions.
Zero and the trivial 1–2 cycle are included intentionally. -/
def exceptions (k : Nat) : List Nat :=
  (List.range (2 ^ k)).filter (fun r =>
    decide (3 ^ oddCount r k < 2 ^ k ∧ r ≤ acceleratedOrbit k r))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Five nontrivial contracting exceptions occur at depth eight. -/
theorem exceptions_eight : exceptions 8 = [0, 1, 2, 7, 9, 18, 19, 25] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- At depth ten only 0 and the trivial cycle representatives remain. -/
theorem exceptions_ten : exceptions 10 = [0, 1, 2] := by
  decide

end Collatz.Research.DescentAtlas
