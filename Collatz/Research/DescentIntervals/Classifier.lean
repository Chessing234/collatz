import Collatz.Research.DescentIntervals.Arithmetic

/-!
# An effective maximal interval for exact first descent

For `n = 2^k*m+r`, each prefix is affine in `m`. Intersecting their
nondrop inequalities with the strict endpoint drop computes the entire
solution set. The equivalence is unconditional; it does not assert coverage
of all starting integers as the depth varies.
-/
namespace Collatz.Research.DescentIntervals

/-- Slope of prefix j in the index of a depth-k dyadic cylinder. -/
def prefixSlope (k r j : Nat) : Nat := 3 ^ oddCount r j * 2 ^ (k - j)

/-- Indices that have not dropped at prefix j. Used only when j ≤ k. -/
def prefixInterval (k r j : Nat) : IndexInterval :=
  solveLE (2 ^ k) r (prefixSlope k r j) (acceleratedOrbit j r)

/-- Indices whose endpoint is strictly below their start. -/
def endpointInterval (k r : Nat) : IndexInterval :=
  solveLE (3 ^ oddCount r k) (acceleratedOrbit k r + 1) (2 ^ k) r

/-- The complete exact-time solution set, not just a sufficient tail. -/
def exactInterval (k r : Nat) : IndexInterval :=
  if k = 0 then noIndices else
    intersect (endpointInterval k r)
      (intersectMany ((List.range k).map (prefixInterval k r)))

theorem prefixInterval_spec {k r j : Nat} (hj : j ≤ k) (m : Nat) :
    (prefixInterval k r j).Contains m ↔
      2 ^ k * m + r ≤ acceleratedOrbit j (2 ^ k * m + r) := by
  rw [FirstDescentClass.prefix_orbit hj]
  exact solveLE_spec _ _ _ _ m

theorem endpointInterval_spec (k r m : Nat) :
    (endpointInterval k r).Contains m ↔
      acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  rw [Congruence.accOrbit_pow_two_mul_add]
  unfold endpointInterval
  rw [solveLE_spec]
  omega

/-- Every successful index and every failure is accounted for by the endpoints. -/
theorem exactInterval_spec (k r m : Nat) :
    (exactInterval k r).Contains m ↔ stoppingTime (2 ^ k * m + r) k := by
  by_cases hk : k = 0
  · subst k
    simp [exactInterval, stoppingTime]
  · have hpre :
        (intersectMany ((List.range k).map (prefixInterval k r))).Contains m ↔
          ∀ j : Nat, j < k → 2 ^ k * m + r ≤ acceleratedOrbit j (2 ^ k * m + r) := by
      rw [intersectMany_spec]
      simp only [List.forall_mem_map, List.mem_range]
      exact forall_congr' fun j => imp_congr_right fun hj =>
        prefixInterval_spec (Nat.le_of_lt hj) m
    rw [exactInterval, if_neg hk, contains_intersect, endpointInterval_spec, hpre]
    constructor
    · rintro ⟨hd, hp⟩
      refine ⟨by omega, hd, ?_⟩
      intro j _ hj
      have := hp j hj
      omega
    · intro h
      exact ⟨h.2.1, fun j hj => FirstDescentResidue.before_first_descent h j hj⟩

/-- Equality to a computed interval is a compact certificate for infinitely many inputs. -/
theorem exact_of_certificate {k r : Nat} {I : IndexInterval}
    (h : exactInterval k r = I) (m : Nat) :
    stoppingTime (2 ^ k * m + r) k ↔ I.Contains m := by
  rw [← h]
  exact (exactInterval_spec k r m).symm

/-- Normalize an arbitrary starting integer into its canonical dyadic class. -/
theorem canonical_exact_iff (n k : Nat) :
    stoppingTime n k ↔ (exactInterval k (n % 2 ^ k)).Contains (n / 2 ^ k) := by
  rw [exactInterval_spec, Nat.div_add_mod]

/-- The executable interval query agrees with the independent orbit checker. -/
theorem checker_agrees (k r m : Nat) :
    membershipB (exactInterval k r) m = Search.firstDescentB (2 ^ k * m + r) k := by
  apply Bool.eq_iff_iff.mpr
  rw [membershipB_spec, exactInterval_spec, Search.firstDescentB_spec]

/-- A certified index excludes every other first-descent time at this input. -/
theorem excludes_other_time {k r m j : Nat}
    (h : (exactInterval k r).Contains m) (hne : j ≠ k) :
    ¬ stoppingTime (2 ^ k * m + r) j := by
  intro hj
  exact hne (FirstDescentResidue.stoppingTime_unique hj ((exactInterval_spec k r m).mp h))

/-- The ordinary checker is complete for an entire ray after its computed cutoff. -/
theorem tail_certificate {k r t : Nat} (h : exactInterval k r = ⟨t, none⟩) (m : Nat) :
    stoppingTime (2 ^ k * m + r) k ↔ t ≤ m := by
  simpa [IndexInterval.Contains] using exact_of_certificate h m

/-- An empty interval certifies impossibility for the entire infinite class. -/
theorem empty_certificate {k r : Nat} (h : exactInterval k r = noIndices) (m : Nat) :
    ¬ stoppingTime (2 ^ k * m + r) k := by
  rw [exact_of_certificate h m]
  exact not_contains_empty m

end Collatz.Research.DescentIntervals
