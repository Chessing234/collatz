import Collatz.Strategy.FirstLightDescent
import Collatz.Strategy.FirstDescentClassComplete
import Collatz.Strategy.AffineObstruction
import Collatz.Research.DescentIntervals.Classifier

/-!
# Coefficient crossing and actual first descent

These lemmas distinguish the coefficient event from actual descent. They
provide the interface for finite witnesses and a conditional horizon theorem.
The horizon bounds the time of an assumed first crossing, not every orbit.
-/
namespace Collatz.Research.CoefficientDescent

open FirstLightDescent FirstDescentClass DescentIntervals

/-- No coefficient contraction means no actual descent at that time. -/
theorem no_drop_of_heavy {n j : Nat} (h : 2 ^ j ≤ 3 ^ oddCount n j) :
    n ≤ acceleratedOrbit j n := by
  apply Classical.byContradiction
  intro hd
  have := AffineObstruction.light_of_drop (show acceleratedOrbit j n < n by omega)
  omega

/-- Actual descent at the first coefficient crossing is automatically the first descent. -/
theorem stopping_of_firstLight_drop {n k : Nat} (hf : FirstLight n k)
    (hd : acceleratedOrbit k n < n) : stoppingTime n k := by
  have hk : 0 < k := by
    apply Classical.byContradiction
    intro h
    have hz : k = 0 := by omega
    subst k
    simp at hd
  exact ⟨hk, hd, fun j _ hj => by
    have := no_drop_of_heavy (hf.2 j hj)
    omega⟩

/-- A complete-class certificate gives both events at the base. -/
theorem witness_of_certificate {n k : Nat} (h : classCertificateB k n = true) :
    FirstLight n k ∧ acceleratedOrbit k n < n := by
  obtain ⟨hc, hs, hp⟩ := (classCertificateB_spec k n).mp h
  exact ⟨⟨hc, hp⟩, hs.2.1⟩

/-- An odd-input interval with certified coefficient crossings and actual descents. -/
def CertifiedRange (lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → n < hi → n % 2 = 1 →
    ∃ k, FirstLight n k ∧ acceleratedOrbit k n < n

/-- Adjacent finite ranges can be assembled without re-evaluating their orbits. -/
theorem CertifiedRange.append {a b c : Nat}
    (hab : CertifiedRange a b) (hbc : CertifiedRange b c) : CertifiedRange a c := by
  intro n hn hc ho
  by_cases hb : n < b
  · exact hab n hn hb ho
  · exact hbc n (by omega) hc ho

/-- Positive even inputs have both stopping times equal to one. -/
theorem even_witness {n : Nat} (hn : 0 < n) (he : n % 2 = 0) :
    FirstLight n 1 ∧ acceleratedOrbit 1 n < n := by
  constructor
  · constructor
    · simp [Congruence.oddCount_succ_of_even he]
    · intro j hj
      have : j = 0 := by omega
      subst j
      simp
  · exact (FirstDescentResidue.stoppingTime_of_even hn he).2.1

/-- A natural-number certificate for the accumulator failure bound at one horizon. -/
def GapBound (K B : Nat) : Prop :=
  ∀ k a, k ≤ K → a ≤ k → 3 ^ a < 2 ^ k →
    a * 3 ^ a < 3 * (2 ^ k - 3 ^ a) * B

/-- The global horizon reduction separates a finite input check from a finite gap check. -/
theorem descent_of_gap_and_small {K B : Nat} (hg : GapBound K B)
    (hs : ∀ n, 1 < n → n < B → ∃ j, FirstLight n j ∧ acceleratedOrbit j n < n)
    {n k : Nat} (hn : 1 < n) (hk : k ≤ K) (hf : FirstLight n k) :
    acceleratedOrbit k n < n := by
  by_cases hb : n < B
  · obtain ⟨j, hj, hd⟩ := hs n hn hb
    have he := first_light_unique hj hf
    simpa only [he] using hd
  · have ht := hg k (oddCount n k) hk (AffineExact.oddCount_le_self n k) hf.1
    apply Classical.byContradiction
    intro hd
    have hfails := failure_bound hf (by omega)
    have hm := Nat.mul_le_mul_left (3 * (2 ^ k - 3 ^ oddCount n k))
      (show B ≤ n by omega)
    omega

/-- A first descent cannot begin at zero or one. -/
theorem start_gt_one {n k : Nat} (hs : stoppingTime n k) : 1 < n := by
  have hd := hs.2.1
  have hn : 0 < n := by omega
  have hp := acceleratedOrbit_positive hn k
  omega

/-- A descent has a least coefficient crossing no later than its own time. -/
theorem exists_firstLight_of_drop {n k : Nat} (hd : acceleratedOrbit k n < n) :
    ∃ j, j ≤ k ∧ FirstLight n j := by
  have hex : ∃ j, 3 ^ oddCount n j < 2 ^ j :=
    ⟨k, AffineObstruction.light_of_drop hd⟩
  obtain ⟨j, hj, hmin⟩ := Minimum.exists_min hex
  refine ⟨j, ?_, hj, ?_⟩
  · apply Classical.byContradiction
    intro h
    exact hmin k (by omega) (AffineObstruction.light_of_drop hd)
  · intro i hi
    have := hmin i hi
    omega

/-- Any proved first-crossing horizon also gives equality of the two stopping times there. -/
theorem stopping_iff_firstLight_of_horizon {K : Nat}
    (H : ∀ n k, 1 < n → k ≤ K → FirstLight n k → acceleratedOrbit k n < n)
    {n k : Nat} (hn : 1 < n) (hk : k ≤ K) :
    stoppingTime n k ↔ FirstLight n k := by
  constructor
  · intro hs
    obtain ⟨j, hjk, hj⟩ := exists_firstLight_of_drop hs.2.1
    have hd := H n j hn (by omega) hj
    have he := FirstDescentResidue.stoppingTime_unique hs (stopping_of_firstLight_drop hj hd)
    simpa only [he] using hj
  · intro hf
    exact stopping_of_firstLight_drop hf (H n k hn hk hf)

end Collatz.Research.CoefficientDescent
