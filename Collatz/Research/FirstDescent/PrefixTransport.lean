import Collatz.Research.DescentAtlas.Core

/-! Prefix transport separates endpoint descent from first descent.
A prefix is uniformly non-descending when both its linear coefficient and its
representative endpoint are non-descending. No convergence hypothesis is used. -/
namespace Collatz.Research.FirstDescent
open Collatz

/-- Refining a binary cylinder preserves a non-descending prefix. -/
theorem prefix_transport {j k r m : Nat} (hjk : j ≤ k)
    (hc : 2 ^ j ≤ 3 ^ oddCount r j)
    (hr : r ≤ acceleratedOrbit j r) :
    2 ^ k * m + r ≤ acceleratedOrbit j (2 ^ k * m + r) := by
  have hp : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hp, Nat.mul_assoc]
  exact Collatz.Research.DescentAtlas.no_descent_of_noncontracting hc hr

/-- Exact first descent on an infinite cylinder follows from finitely many
prefix inequalities and one contracting endpoint. -/
theorem first_descent_transport {k r : Nat}
    (hc : 3 ^ oddCount r k < 2 ^ k)
    (he : acceleratedOrbit k r < r)
    (hp : ∀ j, j < k → 2 ^ j ≤ 3 ^ oddCount r j ∧
      r ≤ acceleratedOrbit j r) (m : Nat) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r ∧
    ∀ j, j < k → 2 ^ k * m + r ≤ acceleratedOrbit j (2 ^ k * m + r) := by
  refine ⟨Collatz.Research.DescentAtlas.descent_of_endpoint hc he, ?_⟩
  intro j hj
  exact prefix_transport (by omega) (hp j hj).1 (hp j hj).2

/-- Cylinder descent excludes the universal no-descent predicate. -/
theorem excludes_never_dropping {k r : Nat}
    (hc : 3 ^ oddCount r k < 2 ^ k)
    (he : acceleratedOrbit k r < r) (m : Nat) :
    ¬ (∀ j, 2 ^ k * m + r ≤ acceleratedOrbit j (2 ^ k * m + r)) := by
  intro h
  have hd := Collatz.Research.DescentAtlas.descent_of_endpoint (m := m) hc he
  have hn := h k
  omega

/-- Two exact first-descent certificates for the same start have the same time.
This is the logical reason cylinders with different first-descent times cannot
cover a common integer. -/
theorem first_descent_unique {n k l : Nat}
    (hk : acceleratedOrbit k n < n)
    (hpk : ∀ j, j < k → n ≤ acceleratedOrbit j n)
    (hl : acceleratedOrbit l n < n)
    (hpl : ∀ j, j < l → n ≤ acceleratedOrbit j n) : k = l := by
  have hkl : ¬ k < l := by
    intro h
    have hp := hpl k h
    omega
  have hlk : ¬ l < k := by
    intro h
    have hp := hpk l h
    omega
  omega

end Collatz.Research.FirstDescent
