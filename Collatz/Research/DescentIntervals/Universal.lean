import Collatz.Research.DescentIntervals.Classifier
import Collatz.Exploration.TimeChange
import Collatz.Research.RefinementAtlas.AdaptiveObstruction

/-!
# The exact remaining coverage obligation

The interval method yields universal descent precisely when each n>1 belongs
to a certified interval at some input-dependent depth. This is equivalent to
Collatz. No finite census or bounded choice of depths establishes coverage.
-/
namespace Collatz.Research.DescentIntervals

/-- Coverage allows the depth to depend without bound on the entire input. -/
def Covers : Prop := ∀ n : Nat, 1 < n →
  ∃ k : Nat, (exactInterval k (n % 2 ^ k)).Contains (n / 2 ^ k)

/-- Any descent witness has a least positive descent time. -/
theorem first_of_drop {n : Nat} (h : ∃ k, acceleratedOrbit k n < n) :
    ∃ k, stoppingTime n k := by
  obtain ⟨k, hk, hmin⟩ := Minimum.exists_min h
  have hk0 : k ≠ 0 := by intro hz; subst k; simp at hk
  exact ⟨k, by omega, hk, fun j _ hj => hmin j hj⟩

/-- Pointwise coverage is exactly existence of a descent, with a canonical residue. -/
theorem coverage_at_iff (n : Nat) :
    (∃ k, (exactInterval k (n % 2 ^ k)).Contains (n / 2 ^ k)) ↔
      ∃ k, acceleratedOrbit k n < n := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, ((canonical_exact_iff n k).mpr hk).2.1⟩
  · intro h
    obtain ⟨k, hk⟩ := first_of_drop h
    exact ⟨k, (canonical_exact_iff n k).mp hk⟩

/-- Strong induction turns universal interval coverage into convergence to one. -/
theorem collatz_of_coverage (h : Covers) : CollatzConjecture := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n; exact one_reaches_one
    · obtain ⟨k, hk⟩ := h n (by omega)
      have hs := (canonical_exact_iff n k).mpr hk
      have hp := acceleratedOrbit_positive hn k
      have hr := ih (acceleratedOrbit k n) hs.2.1 hp
      exact Reach.reachesOne_of_accOrbit hn hr

/-- Convergence would supply the missing coverage at some depth for every n>1. -/
theorem coverage_of_collatz (h : CollatzConjecture) : Covers := by
  intro n hn
  obtain ⟨k, hk⟩ := h n (by omega)
  have hd : orbit k n < n := by omega
  obtain ⟨j, _, hj⟩ := Exploration.TimeChange.accelerated_drop_of_standard hd
  exact (coverage_at_iff n).mpr ⟨j, hj⟩

/-- Exact logical status of the interval-based universal descent program. -/
theorem coverage_iff_collatz : Covers ↔ CollatzConjecture :=
  ⟨collatz_of_coverage, coverage_of_collatz⟩

/-- No finite maximum depth can provide coverage, even with adaptive choices. -/
theorem finite_depth_incomplete (K : Nat) :
    ∃ n : Nat, 1 < n ∧ ∀ k, k ≤ K →
      ¬ (exactInterval k (n % 2 ^ k)).Contains (n / 2 ^ k) := by
  obtain ⟨n, hn, hg⟩ := RefinementAtlas.simultaneous_returns
    (m := 1) (K := K + 1) (by decide) (by omega)
  refine ⟨n, hn, ?_⟩
  intro k hk hc
  have hs := (canonical_exact_iff n k).mpr hc
  have hr := (hg k (by have := hs.1; omega) (by omega)).1
  have hd := hs.2.1
  omega

/-- A finite menu of candidate depths still has an explicit noncovered input. -/
theorem finite_menu_incomplete (depths : List Nat) :
    ∃ n : Nat, 1 < n ∧ ∀ k ∈ depths,
      ¬ (exactInterval k (n % 2 ^ k)).Contains (n / 2 ^ k) := by
  obtain ⟨n, hn, h⟩ := finite_depth_incomplete (depths.foldr max 0)
  refine ⟨n, hn, fun k hk => h k ?_⟩
  clear h
  induction depths with
  | nil => simp at hk
  | cons a rest ih =>
    simp only [List.mem_cons] at hk
    simp only [List.foldr_cons]
    rcases hk with rfl | hk
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hk) (Nat.le_max_right _ _)

end Collatz.Research.DescentIntervals
