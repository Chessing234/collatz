import Collatz.Strategy.PeriodicSingleDefectAll

/-!
A stability refinement of periodic Collatz total variation. In addition to
paying for its range, a potential pays for oscillation away from residue zero.
These are finite modular theorems, not orbit convergence results.
-/
namespace Collatz.PeriodicVariationStability
open PeriodicRigidity PeriodicDefectMinimum PeriodicSingleDefectAll Collatz.Sum

/-- A cut separating two nonzero residues cannot be a one-defect cut. -/
theorem cut_cost {m : Nat} (hm : 1 < m) {g : Nat → Bool}
    (hp : HasPeriod g m) (hne : ∃ a b, g a ≠ g b)
    {u v : Nat} (hu : u % m ≠ 0) (hv : v % m ≠ 0) :
    1 + (if g u = g v then 0 else 1) ≤ defectCount m g := by
  have hpos := defectCount_positive (by omega) hp hne
  by_cases he : g u = g v
  · simp [he]; omega
  · have hnot : defectCount m g ≠ 1 := by
      intro h
      obtain ⟨_, _, hf⟩ := (one_defect_iff_all hm hp).mp h
      have heq : g u = g v := by rw [hf u, hf v, if_neg hu, if_neg hv]
      exact he heq
    simp [he]; omega

/-- Quantitative stability: any two values in the interval between `f a` and
`f b`, at nonzero residues, incur their distance as an additional cost.
No divisibility-by-three assumption is needed. -/
theorem variation_stability {m : Nat} (hm : 1 < m) {f : Nat → Nat}
    (hp : HasPeriod f m) (a b u v : Nat)
    (hu : u % m ≠ 0) (hv : v % m ≠ 0)
    (hau : f a ≤ f u) (hub : f u ≤ f b)
    (hav : f a ≤ f v) (hvb : f v ≤ f b) :
    (f b - f a) + distance (f u) (f v) ≤ variation m f := by
  let K := f b - f a
  let label := fun t n => decide (f a + t < f n)
  have hcut : ∀ t, t < K →
      1 + (if label t u = label t v then 0 else 1) ≤ defectCount m (label t) := by
    intro t ht
    have hperiod : HasPeriod (label t) m := by intro n; simp [label, hp n]
    have hne : ∃ x y, label t x ≠ label t y := by
      refine ⟨a, b, ?_⟩
      have hfalse : ¬ f a + t < f a := by omega
      have htrue : f a + t < f b := by dsimp [K] at ht; omega
      simp [label, hfalse, htrue]
    exact cut_cost hm hperiod hne hu hv
  have hlower := sumRange_le hcut
  rw [sumRange_add, sumRange_const] at hlower
  have hthreshold : sumRange K (fun t => if label t u = label t v then 0 else 1) =
      distance (f u) (f v) := by
    rw [show (fun t => if label t u = label t v then 0 else 1) =
      (fun t => if decide (f a + t < f u) = decide (f a + t < f v) then 0 else 1)
      from rfl, threshold_sum]
    dsimp [K, distance]
    omega
  rw [hthreshold, Nat.mul_one] at hlower
  have hupper : sumRange K (fun t => defectCount m (label t)) ≤ variation m f := by
    unfold defectCount variation
    rw [TreeStochastic.sumRange_comm]
    exact sumRange_le (fun n _ => threshold_sum_le K (f a) (f (acceleratedStep n)) (f n))
  exact Nat.le_trans hlower hupper

/-- At the range lower bound, every nonzero residue has the same value. -/
theorem equality_rigidity {m : Nat} (hm : 1 < m) {f : Nat → Nat}
    (hp : HasPeriod f m) (a b : Nat)
    (hmin : ∀ n, f a ≤ f n) (hmax : ∀ n, f n ≤ f b)
    (heq : variation m f = f b - f a) :
    ∀ n, f n = if n % m = 0 then f 0 else f 1 := by
  intro n
  by_cases hz : n % m = 0
  · rw [if_pos hz, period_mod hp n, hz]
  · rw [if_neg hz]
    have h := variation_stability hm hp a b n 1 hz
      (by rw [Nat.mod_eq_of_lt hm]; decide) (hmin n) (hmax n) (hmin 1) (hmax 1)
    rw [heq] at h
    unfold distance at h
    omega

/-- Exact variation of every potential constant off the zero residue. -/
theorem spike_variation {m : Nat} (hm : 1 < m) {f : Nat → Nat}
    (hf : ∀ n, f n = if n % m = 0 then f 0 else f 1) :
    variation m f = (if m % 3 = 0 then 1 else 2) * distance (f 0) (f 1) := by
  have hpoint : ∀ n, distance (f (acceleratedStep n)) (f n) =
      distance (f 0) (f 1) *
        (if divisibleLabel m (acceleratedStep n) = divisibleLabel m n then 0 else 1) := by
    intro n
    rw [hf (acceleratedStep n), hf n]
    unfold divisibleLabel
    by_cases ht : acceleratedStep n % m = 0 <;> by_cases hn : n % m = 0 <;>
      simp [ht, hn, distance, Nat.add_comm]
  unfold variation
  rw [sumRange_congr (fun n _ => hpoint n), sumRange_const_mul]
  change distance (f 0) (f 1) * defectCount m (divisibleLabel m) = _
  rw [divisibleLabel_defectCount hm, Nat.mul_comm]

/-- Complete characterization of nonconstant potentials attaining variation
exactly equal to their range, including the necessary modulus condition. -/
theorem optimal_iff {m : Nat} (hm : 1 < m) {f : Nat → Nat}
    (hp : HasPeriod f m) (a b : Nat) (hab : f a < f b)
    (hmin : ∀ n, f a ≤ f n) (hmax : ∀ n, f n ≤ f b) :
    variation m f = f b - f a ↔ m % 3 = 0 ∧
      ∀ n, f n = if n % m = 0 then f 0 else f 1 := by
  constructor
  · intro heq
    have h3 : m % 3 = 0 := by
      have h := variation_lower_bound hm hp a b
      rw [heq] at h
      by_cases ht : m % 3 = 0
      · exact ht
      · rw [if_neg ht] at h; omega
    exact ⟨h3, equality_rigidity hm hp a b hmin hmax heq⟩
  · rintro ⟨h3, hf⟩
    rw [spike_variation hm hf, if_pos h3, Nat.one_mul]
    have ha := hf a
    have hb := hf b
    have h0min := hmin 0
    have h1min := hmin 1
    have h0max := hmax 0
    have h1max := hmax 1
    unfold distance
    split at ha <;> split at hb <;> omega

/-- A potential within `E` of the range bound is uniformly within `E` of
a constant on all nonzero residues. The zero-residue value is unrestricted. -/
theorem near_optimal_uniform {m : Nat} (hm : 1 < m) {f : Nat → Nat}
    (hp : HasPeriod f m) (a b E : Nat)
    (hmin : ∀ n, f a ≤ f n) (hmax : ∀ n, f n ≤ f b)
    (hbudget : variation m f ≤ (f b - f a) + E) :
    ∀ u v, u % m ≠ 0 → v % m ≠ 0 → distance (f u) (f v) ≤ E := by
  intro u v hu hv
  have h := variation_stability hm hp a b u v hu hv
    (hmin u) (hmax u) (hmin v) (hmax v)
  omega

/-- The extra oscillation term is sharp, at every height, already modulo six. -/
theorem stability_sharp (H : Nat) :
    let f := fun n => if n % 6 = 0 then 2 * H else if n % 6 = 3 then H else 0
    HasPeriod f 6 ∧ f 0 = 2 * H ∧ f 1 = 0 ∧ f 3 = H ∧
      variation 6 f = (f 0 - f 1) + distance (f 1) (f 3) := by
  dsimp
  refine ⟨?_, by simp, by simp, by simp, ?_⟩
  · intro n; simp
  · simp [variation, sumRange, acceleratedStep, distance]
    omega
/-- Uniform sharpness at every modulus divisible by six. Two nested
zero-residue cuts give three disjoint units of variation. -/
theorem nested_spikes_variation {M : Nat} (hM : 1 < M) (h3 : M % 3 = 0) (H : Nat) :
    let f := fun n => if n % (2 * M) = 0 then 2 * H else if n % M = 0 then H else 0
    HasPeriod f (2 * M) ∧ f 0 = 2 * H ∧ f 1 = 0 ∧ f M = H ∧
      variation (2 * M) f = 3 * H := by
  let f := fun n => if n % (2 * M) = 0 then 2 * H else if n % M = 0 then H else 0
  let w := fun d n => if divisibleLabel d (acceleratedStep n) = divisibleLabel d n then 0 else 1
  have hz : ∀ n, n % (2 * M) = 0 → n % M = 0 := by
    intro n hn
    have h := Nat.mod_mod_of_dvd n (Nat.dvd_mul_left M 2)
    rw [hn] at h
    exact h.symm
  have hpoint : ∀ n, distance (f (acceleratedStep n)) (f n) =
      H * (w (2 * M) n + w M n) := by
    intro n
    have hs := hz (acceleratedStep n)
    have hn := hz n
    dsimp [f, w, divisibleLabel]
    by_cases hs2 : acceleratedStep n % (2 * M) = 0 <;>
      by_cases hn2 : n % (2 * M) = 0 <;>
      by_cases hs1 : acceleratedStep n % M = 0 <;>
      by_cases hn1 : n % M = 0 <;>
      simp_all [distance] <;> omega
  have hwperiod : HasPeriod (w M) (2 * M) := by
    intro n
    have h := defect_period (divisibleLabel_period M) n
    have he : (divisibleLabel M (acceleratedStep (n + 2 * M)) = divisibleLabel M (n + 2 * M)) ↔
        (divisibleLabel M (acceleratedStep n) = divisibleLabel M n) := by
      change (_ ≠ _) = (_ ≠ _) at h
      constructor <;> intro heq <;> apply Classical.byContradiction <;> intro hn
      · exact (Eq.mpr h hn) heq
      · exact (Eq.mp h hn) heq
    simp only [w, he]
  have hsum : sumRange (2 * (2 * M)) (w M) = 2 * defectCount M (divisibleLabel M) := by
    rw [sumRange_two_mul]
    have heq : sumRange (2 * M) (fun i => w M (2 * M + i)) = sumRange (2 * M) (w M) := by
      apply sumRange_congr
      intro i _
      simpa [Nat.add_comm] using hwperiod i
    rw [heq]
    change _ + _ = 2 * sumRange (2 * M) (w M)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp [f]
    simp [Nat.add_mod]
  · simp
  · simp [Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (show 1 < 2 * M by omega)]
  · simp [Nat.mod_eq_of_lt (show M < 2 * M by omega), show M ≠ 0 by omega]
  · change variation (2 * M) f = _
    unfold variation
    rw [sumRange_congr (fun n _ => hpoint n), sumRange_const_mul, sumRange_add, hsum]
    change H * (defectCount (2 * M) (divisibleLabel (2 * M)) + 2 * defectCount M (divisibleLabel M)) = _
    rw [divisibleLabel_defectCount (by omega), divisibleLabel_defectCount hM,
      if_pos h3, if_pos (show (2 * M) % 3 = 0 by omega)]
    omega
end Collatz.PeriodicVariationStability
