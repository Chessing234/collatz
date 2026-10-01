import Collatz.Strategy.FirstDescentDensityTransport
import Collatz.Papers.KorecCertified
import Collatz.Structure.CofiniteNaturalDensity

/-!
# Power-target times cannot have density-tight tails

For p<q, a successful time k with T^k(n)^q<n^p forces n<2^(kq).
Consequently every fixed time window misses the target for all sufficiently
large inputs. A rule that reaches the power target at density one therefore
cannot satisfy the uniform tail condition used for first-descent transport.
-/
namespace Collatz.PowerStoppingTimeBarrier
open NaturalDensity StoppingRuleDensity Papers.Korec1994

/-- The accelerated map cannot shrink size faster than repeated halvings. -/
theorem orbit_halving_lower (n k : Nat) : n≤2^k*acceleratedOrbit k n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have hs := FirstDescentDensityTransport.input_le_twice_step n
    have hi := Nat.mul_le_mul_left 2 (ih (acceleratedStep n))
    have ht := Nat.le_trans hs hi
    simpa only [acceleratedOrbit_succ, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using ht

/-- The exact integer size-time constraint for a successful power hit. -/
theorem power_gap_bound_of_hit {p q n k : Nat} (hpq : p<q)
    (hh : (acceleratedOrbit k n)^q<n^p) : n^(q-p)<2^(k*q) := by
  have hlo := Nat.pow_le_pow_left (orbit_halving_lower n k) q
  simp only [Nat.mul_pow, ← Nat.pow_mul] at hlo
  have hhit := Nat.mul_lt_mul_of_pos_left hh (Nat.pow_pos (by decide) : 0<(2:Nat)^(k*q))
  have ht := Nat.lt_of_le_of_lt hlo hhit
  have he : n^q=n^(q-p)*n^p := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [he] at ht
  exact Nat.lt_of_mul_lt_mul_right ht

/-- A coarser cutoff form convenient for uniform finite-window statements. -/
theorem input_bound_of_power_hit {p q n k : Nat} (hpq : p<q)
    (hh : (acceleratedOrbit k n)^q<n^p) : n<2^(k*q) := by
  have hg := power_gap_bound_of_hit hpq hh
  by_cases hz : n=0
  · subst n
    exact Nat.pow_pos (by decide)
  · have hn : n≤n^(q-p) := by
      simpa only [Nat.pow_one] using
        Nat.pow_le_pow_right (by omega : 1≤n) (by omega : 1≤q-p)
    exact Nat.lt_of_le_of_lt hn hg

/-- No time up to K succeeds once the input reaches the explicit cutoff. -/
theorem no_power_hit_through {p q n K : Nat} (hpq : p<q) (hn : 2^(K*q)≤n) :
    ∀ k, k≤K → ¬(acceleratedOrbit k n)^q<n^p := by
  intro k hk hh
  have hi := input_bound_of_power_hit hpq hh
  have he := Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) (Nat.mul_le_mul_right q hk)
  omega

/-- A selected time attains the strict power target. -/
def Success (p q : Nat) (time : Nat → Nat) (n : Nat) : Prop :=
  (acceleratedOrbit (time n) n)^q<n^p

/-- Tight selected times hit any strict sublinear power target on a set of
natural density zero, expressed by complementary integer precision. -/
theorem success_sparse_of_tight {p q : Nat} (hpq : p<q) (time : Nat → Nat)
    (ht : DensityTight time) : ∀ r, 0<r → ∃ N0, ∀ N, N0≤N →
      r*predicateCount (Success p q time) N≤N := by
  intro r hr
  obtain ⟨K, NT, htail⟩ := ht (2*r) (by omega)
  let B := 2^(K*q)
  refine ⟨max NT (2*r*B), ?_⟩
  intro N hn
  have hc := predicateCount_eventual_mono (P := Success p q time)
    (Q := fun n => K<time n) B N (by
      intro n hB hh
      by_cases hk : time n≤K
      · exact False.elim (no_power_hit_through hpq hB (time n) hk hh)
      · omega)
  have hm := Nat.mul_le_mul_left (2*r) hc
  have hb : 2*r*B≤N := by omega
  have htN := htail N (by omega)
  simp only [Nat.mul_add, Nat.mul_assoc] at hm hb htN
  omega

/-- A density-one power-hitting rule cannot be density-tight. -/
theorem not_tight_of_power_success {p q : Nat} (hpq : p<q) (time : Nat → Nat)
    (hP : DensityOne (Success p q time)) : ¬DensityTight time := by
  intro ht
  obtain ⟨NS, hs⟩ := success_sparse_of_tight hpq time ht 2 (by decide)
  obtain ⟨NP, hp⟩ := hP 4 (by decide)
  let N := max NS NP+1
  have hsmall := hs N (by dsimp [N]; omega)
  have hlarge := hp N (by dsimp [N]; omega)
  dsimp [N] at hsmall hlarge
  omega

/-- A density-one power-hitting rule has a density-one large-time tail at
every fixed horizon, the opposite of the required tightness condition. -/
theorem power_success_forces_large_times {p q : Nat} (hpq : p<q) (time : Nat → Nat)
    (hP : DensityOne (Success p q time)) (K : Nat) : DensityOne (fun n => K<time n) := by
  apply densityOne_eventual_mono (P := Success p q time) (B := 2^(K*q)) _ hP
  intro n hn hh
  by_cases hk : time n≤K
  · exact False.elim (no_power_hit_through hpq hn (time n) hk hh)
  · omega

/-- Choose a successful power time when one exists; use zero otherwise.
No computability or least-time claim is made for this totalization. -/
noncomputable def powerTime (p q n : Nat) : Nat := by
  classical
  exact if h : OrbitBelowPower p q n then Classical.choose h else 0

/-- The chosen time satisfies its power target on every input where one exists. -/
theorem powerTime_spec {p q n : Nat} (h : OrbitBelowPower p q n) :
    Success p q (powerTime p q) n := by
  classical
  unfold Success powerTime
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- Korec's theorem supplies an actual density-one power-hitting rule. -/
theorem powerTime_success_density {p q : Nat} (hq : 0<q) (hgap : 3^q<4^p) :
    DensityOne (Success p q (powerTime p q)) :=
  densityOne_mono (fun _ h => powerTime_spec h) (rationalExponentStatement_proved p q hq hgap)

/-- In the sublinear Korec range, this actual power rule fails density tightness.
The first-descent transport theorem cannot be applied to it directly. -/
theorem powerTime_not_tight {p q : Nat} (hpq : p<q) (hgap : 3^q<4^p) :
    ¬DensityTight (powerTime p q) :=
  not_tight_of_power_success hpq _ (powerTime_success_density (by omega) hgap)

end Collatz.PowerStoppingTimeBarrier
