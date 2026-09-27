import Collatz.Strategy.InverseCoverMod9
import Collatz.Strategy.InverseCoverMod27

/-!
# Quantitative inverse-tree coverage, uniformly over all roots

For every positive `a` not divisible by three and every residue `r`:

* modulo 9: an odd `n < 720*a` reaches `a` within 19 accelerated steps;
* modulo 27: an odd `n < 19419*a` reaches `a` within 22 accelerated steps.

The quantifier over `a` is unbounded. These conclusions follow from finite
ternary certificates and the proved soundness theorem, not a finite scan of
starting integers. The certificates include residues divisible by three.

The general qualitative coverage theorem is classical. These explicit bounds
are additions to this development; priority in the literature is not claimed.
Neither convergence nor a bound uniform over all moduli is proved here.
-/

namespace Collatz.QuantitativeBackwardCover

private theorem cover_of_certificates {k B V : Nat}
    (certs : ∀ r b : Nat, r < 3 ^ k → b = 1 ∨ b = 2 →
      ∃ c : InverseCover.HitCert, InverseCover.check k r B V b 1 c = true)
    {a r : Nat} (ha : 0 < a) (ha3 : a % 3 ≠ 0) (hr : r < 3 ^ k) :
    ∃ n t, 0 < n ∧ n % 2 = 1 ∧ n % 3 ^ k = r ∧
      t ≤ V ∧ acceleratedOrbit t n = a ∧ n < B * a := by
  have hb : a % 3 = 1 ∨ a % 3 = 2 := by omega
  obtain ⟨c, hc⟩ := certs r (a % 3) hr hb
  exact InverseCover.check_sound hc ha (by simp)

/-- All nine classes have small odd representatives in every eligible inverse tree. -/
theorem cover_mod9 {a r : Nat} (ha : 0 < a) (ha3 : a % 3 ≠ 0) (hr : r < 9) :
    ∃ n t, 0 < n ∧ n % 2 = 1 ∧ n % 9 = r ∧
      t ≤ 19 ∧ acceleratedOrbit t n = a ∧ n < 720 * a :=
  cover_of_certificates (k := 2) (B := 720) (V := 19)
    InverseCoverMod9.exists_checked ha ha3 hr

/-- All twenty-seven classes are covered, with a uniform size and time bound. -/
theorem cover_mod27 {a r : Nat} (ha : 0 < a) (ha3 : a % 3 ≠ 0) (hr : r < 27) :
    ∃ n t, 0 < n ∧ n % 2 = 1 ∧ n % 27 = r ∧
      t ≤ 22 ∧ acceleratedOrbit t n = a ∧ n < 19419 * a :=
  cover_of_certificates (k := 3) (B := 19419) (V := 22)
    InverseCoverMod27.exists_checked ha ha3 hr

/-- In particular the size cost at this modulus is below the cube of the modulus. -/
theorem cover_mod27_cube {a r : Nat} (ha : 0 < a) (ha3 : a % 3 ≠ 0) (hr : r < 27) :
    ∃ n t, 0 < n ∧ n % 2 = 1 ∧ n % 27 = r ∧
      t ≤ 22 ∧ acceleratedOrbit t n = a ∧ n < 27 ^ 3 * a := by
  obtain ⟨n, t, hn, ho, hm, ht, he, hb⟩ := cover_mod27 ha ha3 hr
  exact ⟨n, t, hn, ho, hm, ht, he, by omega⟩

/-- A hypothetical nonconvergent root has small nonconvergent odd predecessors
in EVERY residue modulo 27. This transports nonconvergence; it does not exclude it. -/
theorem nonconvergent_in_every_class {a r : Nat} (ha : 0 < a)
    (ha3 : a % 3 ≠ 0) (hnr : ¬ Reach.ReachesOne a) (hr : r < 27) :
    ∃ n, 0 < n ∧ n % 2 = 1 ∧ n % 27 = r ∧ n < 19419 * a ∧
      ¬ Reach.ReachesOne n := by
  obtain ⟨n, t, hn, ho, hm, _, he, hb⟩ := cover_mod27 ha ha3 hr
  refine ⟨n, hn, ho, hm, hb, ?_⟩
  intro h
  apply hnr
  rw [← he]
  exact (Reach.reachesOne_accOrbit_iff hn t).mp h

/-- Verifying one residue class up to the larger bound transfers convergence
to all eligible roots below the smaller bound. The hypothesis remains explicit. -/
theorem reachesOne_of_class_verified {N a r : Nat} (ha : 0 < a)
    (ha3 : a % 3 ≠ 0) (haN : a ≤ N) (hr : r < 27)
    (verified : ∀ n, 0 < n → n % 2 = 1 → n % 27 = r →
      n < 19419 * N → Reach.ReachesOne n) : Reach.ReachesOne a := by
  obtain ⟨n, t, hn, ho, hm, _, he, hb⟩ := cover_mod27 ha ha3 hr
  have hbound : n < 19419 * N :=
    Nat.lt_of_lt_of_le hb (Nat.mul_le_mul_left 19419 haN)
  have h := (Reach.reachesOne_accOrbit_iff hn t).mp (verified n hn ho hm hbound)
  rwa [he] at h

end Collatz.QuantitativeBackwardCover
