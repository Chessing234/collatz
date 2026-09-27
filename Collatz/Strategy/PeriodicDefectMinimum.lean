import Collatz.Strategy.PeriodicRigidity
import Collatz.Strategy.TreeStochastic

/-!
Exact minimum number of defects of a nonconstant Boolean label of period m.
The minimum is one when 3 divides m, and two otherwise (m > 1).
-/

namespace Collatz.PeriodicDefectMinimum

open Collatz.Sum PeriodicRigidity

theorem affine_injective {m : Nat} (hm3 : m % 3 ≠ 0)
    {a b : Nat} (ha : a < m) (hb : b < m)
    (he : (3 * a + 2) % m = (3 * b + 2) % m) : a = b := by
  have ordered : ∀ a b, a < m → b ≤ a →
      (3 * a + 2) % m = (3 * b + 2) % m → a = b := by
    intro a b ha hab he
    obtain ⟨u, v, huv⟩ := Nat.mod_eq_mod_iff.mp he
    have hd := Nat.dvd_sub (Nat.dvd_mul_left m v) (Nat.dvd_mul_left m u)
    have heq : v * m - u * m = 3 * (a - b) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [heq] at hd
    have hdiv := (LocalBlindness.coprime_three_of_not_dvd hm3).dvd_of_dvd_mul_left hd
    have hz := Nat.mod_eq_zero_of_dvd hdiv
    rw [Nat.mod_eq_of_lt (by omega : a - b < m)] at hz
    omega
  by_cases h : b ≤ a
  · exact ordered a b ha h he
  · exact (ordered b a hb (by omega) he.symm).symm

theorem finite_preimage {m : Nat} {p : Nat → Nat}
    (hb : ∀ i, i < m → p i < m)
    (hi : ∀ i j, i < m → j < m → p i = p j → i = j)
    {r : Nat} (hr : r < m) : ∃ i, i < m ∧ p i = r := by
  let q := fun i => if i < m then p i else r
  have hq : ∀ i, i ≤ m → q i < m := by
    intro i _
    simp only [q]
    split
    · exact hb _ (by assumption)
    · exact hr
  obtain ⟨i, j, hij, hjm, heq⟩ := Pigeonhole.exists_repeat hq (Nat.le_refl m)
  have him : i < m := by omega
  by_cases hj : j < m
  · have hpij : p i = p j := by simpa [q, him, hj] using heq
    have := hi i j him hj hpij
    omega
  · exact ⟨i, him, by simpa [q, him, hj] using heq⟩

theorem affine_sum {m : Nat} (hm : 0 < m) (hm3 : m % 3 ≠ 0)
    {f : Nat → Nat} (hp : HasPeriod f m) :
    sumRange m (fun i => f (3 * i + 2)) = sumRange m f := by
  have hbij : ∀ r, r < m → ∃ i, i < m ∧ True ∧ (3 * i + 2) % m = r ∧
      ∀ j, j < m → True → (3 * j + 2) % m = r → j = i := by
    intro r hr
    obtain ⟨i, hi, hir⟩ := finite_preimage
      (fun i _ => Nat.mod_lt (3 * i + 2) hm)
      (fun _ _ hi hj h => affine_injective hm3 hi hj h) hr
    exact ⟨i, hi, trivial, hir, fun j hj _ hjr => affine_injective hm3 hj hi (hjr.trans hir.symm)⟩
  have h := TreeStochastic.sumRange_reindex (n := m) (B := m)
    (fun _ => True) (fun i => (3 * i + 2) % m) f
    (fun i _ _ => Nat.mod_lt _ hm) hbij
  simp only [if_true] at h
  rw [← h]
  exact sumRange_congr (fun i _ => period_mod hp (3 * i + 2))

theorem sum_even_odd (m : Nat) (f : Nat → Nat) :
    sumRange (2 * m) f = sumRange m (fun i => f (2 * i)) +
      sumRange m (fun i => f (2 * i + 1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
    rw [sumRange_succ, sumRange_succ, ih, sumRange_succ, sumRange_succ]
    omega

/-- Conservation of periodic label mass when 3 is invertible modulo m. -/
theorem mass_conservation {m : Nat} (hm : 0 < m) (hm3 : m % 3 ≠ 0)
    {f : Nat → Nat} (hp : HasPeriod f m) :
    sumRange (2 * m) (fun n => f (acceleratedStep n)) = sumRange (2 * m) f := by
  rw [sum_even_odd]
  have he : ∀ n, acceleratedStep (2 * n) = n := by
    intro n; simp [acceleratedStep]
  have ho : ∀ n, acceleratedStep (2 * n + 1) = 3 * n + 2 := by
    intro n; unfold acceleratedStep; rw [if_neg (by omega)]; omega
  simp only [he, ho]
  rw [affine_sum hm hm3 hp, sumRange_two_mul]
  have hshift : sumRange m (fun i => f (m + i)) = sumRange m f := by
    exact sumRange_congr (fun i _ => by simpa [Nat.add_comm] using hp i)
  rw [hshift]

def defectCount (m : Nat) (f : Nat → Bool) : Nat :=
  sumRange (2 * m) (fun n => if f (acceleratedStep n) = f n then 0 else 1)

def exitCount (m : Nat) (f : Nat → Bool) : Nat :=
  sumRange (2 * m) (fun n => if f n = true ∧ f (acceleratedStep n) = false then 1 else 0)

def entryCount (m : Nat) (f : Nat → Bool) : Nat :=
  sumRange (2 * m) (fun n => if f n = false ∧ f (acceleratedStep n) = true then 1 else 0)

theorem defects_split (m : Nat) (f : Nat → Bool) :
    defectCount m f = exitCount m f + entryCount m f := by
  unfold defectCount exitCount entryCount
  rw [← sumRange_add]
  apply sumRange_congr
  intro n _
  cases f n <;> cases f (acceleratedStep n) <;> decide

theorem entries_eq_exits {m : Nat} (hm : 0 < m) (hm3 : m % 3 ≠ 0)
    {f : Nat → Bool} (hp : HasPeriod f m) : entryCount m f = exitCount m f := by
  let w := fun n => if f n then 1 else 0
  have hwp : HasPeriod w m := by intro n; simp [w, hp n]
  have hmass := mass_conservation hm hm3 hwp
  have hsum : sumRange (2 * m) (fun n => w (acceleratedStep n)) + exitCount m f =
      sumRange (2 * m) w + entryCount m f := by
    unfold exitCount entryCount
    rw [← sumRange_add, ← sumRange_add]
    apply sumRange_congr
    intro n _
    simp only [w]
    cases f n <;> cases f (acceleratedStep n) <;> decide
  omega

/-- All cuts have an even number of defects when 3 does not divide m. -/
theorem defects_twice_exits {m : Nat} (hm : 0 < m) (hm3 : m % 3 ≠ 0)
    {f : Nat → Bool} (hp : HasPeriod f m) : defectCount m f = 2 * exitCount m f := by
  rw [defects_split, entries_eq_exits hm hm3 hp]
  omega

theorem defectCount_positive {m : Nat} (hm : 0 < m)
    {f : Nat → Bool} (hp : HasPeriod f m) (hne : ∃ a b, f a ≠ f b) :
    0 < defectCount m f := by
  obtain ⟨r, _, hr, hd⟩ := defect_progression hm hp hne
  have hdr : f (acceleratedStep r) ≠ f r := by simpa [Defect] using hd 0
  have h := le_sumRange (fun n => if f (acceleratedStep n) = f n then 0 else 1) hr
  rw [if_neg hdr] at h
  exact h

theorem two_le_defectCount {m : Nat} (hm : 0 < m) (hm3 : m % 3 ≠ 0)
    {f : Nat → Bool} (hp : HasPeriod f m) (hne : ∃ a b, f a ≠ f b) :
    2 ≤ defectCount m f := by
  have hpos := defectCount_positive hm hp hne
  have he := defects_twice_exits hm hm3 hp
  omega

theorem step_mod_self_ne {m : Nat} (hm : 1 < m) : acceleratedStep m % m ≠ 0 := by
  by_cases he : m % 2 = 0
  · have hs : acceleratedStep m = m / 2 := by simp [acceleratedStep, he]
    rw [hs, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hs : acceleratedStep m = (3 * m + 1) / 2 := by simp [acceleratedStep, he]
    rw [hs, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem residue_zero_iff {m n : Nat} (_hm : 0 < m) (hn : n < 2 * m) :
    n % m = 0 ↔ n = 0 ∨ n = m := by
  by_cases h : n < m
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- The singleton zero residue has exactly one exiting edge at every modulus. -/
theorem divisibleLabel_exitCount {m : Nat} (hm : 1 < m) :
    exitCount m (divisibleLabel m) = 1 := by
  have hexit : ∀ n, n < 2 * m →
      ((divisibleLabel m n = true ∧ divisibleLabel m (acceleratedStep n) = false) ↔ n = m) := by
    intro n hn
    simp only [divisibleLabel, decide_eq_true_eq, decide_eq_false_iff_not]
    constructor
    · rintro ⟨hdiv, hs⟩
      rcases (residue_zero_iff (by omega : 0 < m) hn).mp hdiv with h | h
      · subst n; simp at hs
      · exact h
    · intro h; subst n
      exact ⟨Nat.mod_self _, step_mod_self_ne hm⟩
  unfold exitCount
  exact TreeStochastic.sumRange_indicator_one _ (by omega : m < 2 * m)
    ((hexit m (by omega)).mpr rfl)
    (fun n hn h => (hexit n hn).mp h)

theorem divisibleLabel_defectCount {m : Nat} (hm : 1 < m) :
    defectCount m (divisibleLabel m) = if m % 3 = 0 then 1 else 2 := by
  by_cases h3 : m % 3 = 0
  · rw [if_pos h3]
    classical
    have hcount := TreeStochastic.sumRange_indicator_one
      (fun n => Defect (divisibleLabel m) n) (by omega : m < 2 * m)
      ((divisibleLabel_defect (by omega : 0 < m) h3 m).mpr (Nat.mod_eq_of_lt (by omega)))
      (fun n hn hd => by
        have h := (divisibleLabel_defect (by omega : 0 < m) h3 n).mp hd
        rwa [Nat.mod_eq_of_lt hn] at h)
    rw [← hcount]
    unfold defectCount
    apply sumRange_congr
    intro n _
    unfold Defect
    split <;> simp_all
  · rw [if_neg h3, defects_twice_exits (by omega) h3 (divisibleLabel_period m),
      divisibleLabel_exitCount hm]

/-- Exact optimization over all nonconstant Boolean labels of period m.
The witness has least positive period m. -/
theorem minimum_defects {m : Nat} (hm : 1 < m) :
    (∀ f : Nat → Bool, HasPeriod f m → (∃ a b, f a ≠ f b) →
      (if m % 3 = 0 then 1 else 2) ≤ defectCount m f) ∧
    HasPeriod (divisibleLabel m) m ∧
    (∃ a b, divisibleLabel m a ≠ divisibleLabel m b) ∧
    defectCount m (divisibleLabel m) = (if m % 3 = 0 then 1 else 2) ∧
    (∀ d, 0 < d → HasPeriod (divisibleLabel m) d → m ≤ d) := by
  refine ⟨?_, divisibleLabel_period m, divisibleLabel_nonconstant hm,
    divisibleLabel_defectCount hm, fun _ hd hp => divisibleLabel_least_period hd hp⟩
  intro f hp hne
  split
  · exact defectCount_positive (by omega) hp hne
  · exact two_le_defectCount (by omega) (by assumption) hp hne

/-- Integer absolute difference, without a signed-number library. -/
def distance (u v : Nat) : Nat := (u - v) + (v - u)

/-- Discrete coarea, restricted to an arbitrary interval of thresholds. -/
theorem threshold_sum (K a u v : Nat) :
    sumRange K (fun t => if decide (a + t < u) = decide (a + t < v) then 0 else 1) =
      distance (min K (u - a)) (min K (v - a)) := by
  induction K with
  | zero => simp [distance]
  | succ K ih =>
    rw [sumRange_succ, ih]
    unfold distance
    by_cases hu : a + K < u <;> by_cases hv : a + K < v <;> simp [hu, hv] <;> omega

theorem threshold_sum_le (K a u v : Nat) :
    sumRange K (fun t => if decide (a + t < u) = decide (a + t < v) then 0 else 1) ≤
      distance u v := by
  rw [threshold_sum]
  unfold distance
  omega

/-- Total variation of a numerical periodic potential across all residue edges. -/
def variation (m : Nat) (f : Nat → Nat) : Nat :=
  sumRange (2 * m) (fun n => distance (f (acceleratedStep n)) (f n))

/-- A sharp lower bound for every numerical periodic potential and any two
of its values. Layering the optimal Boolean cuts proves the inequality. -/
theorem variation_lower_bound {m : Nat} (hm : 1 < m)
    {f : Nat → Nat} (hp : HasPeriod f m) (a b : Nat) :
    (if m % 3 = 0 then 1 else 2) * (f b - f a) ≤ variation m f := by
  let K := f b - f a
  let c := if m % 3 = 0 then 1 else 2
  let label := fun t n => decide (f a + t < f n)
  have hcut : ∀ t, t < K → c ≤ defectCount m (label t) := by
    intro t ht
    have hperiod : HasPeriod (label t) m := by intro n; simp [label, hp n]
    have hne : ∃ x y, label t x ≠ label t y := by
      refine ⟨a, b, ?_⟩
      have hfalse : ¬ f a + t < f a := by omega
      have htrue : f a + t < f b := by dsimp [K] at ht; omega
      simp [label, hfalse, htrue]
    exact (minimum_defects hm).1 _ hperiod hne
  have hlower : K * c ≤ sumRange K (fun t => defectCount m (label t)) := by
    rw [← sumRange_const]
    exact sumRange_le hcut
  have hupper : sumRange K (fun t => defectCount m (label t)) ≤ variation m f := by
    unfold defectCount variation
    rw [TreeStochastic.sumRange_comm]
    exact sumRange_le (fun n _ => threshold_sum_le K (f a) (f (acceleratedStep n)) (f n))
  have h := Nat.le_trans hlower hupper
  simpa [K, c, Nat.mul_comm] using h

/-- The lower bound is attained for every height H and every m > 1. -/
theorem variation_sharp {m : Nat} (hm : 1 < m) (H : Nat) :
    let f := fun n => if divisibleLabel m n then H else 0
    HasPeriod f m ∧ f 0 = H ∧ f 1 = 0 ∧
      variation m f = (if m % 3 = 0 then 1 else 2) * H := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n; dsimp; rw [divisibleLabel_period m n]
  · simp [divisibleLabel]
  · simp [divisibleLabel, Nat.mod_eq_of_lt hm]
  · have hpoint : ∀ n, distance
        (if divisibleLabel m (acceleratedStep n) then H else 0)
        (if divisibleLabel m n then H else 0) =
        H * (if divisibleLabel m (acceleratedStep n) = divisibleLabel m n then 0 else 1) := by
      intro n
      cases divisibleLabel m (acceleratedStep n) <;> cases divisibleLabel m n <;>
        simp [distance]
    unfold variation
    rw [sumRange_congr (fun n _ => hpoint n), sumRange_const_mul]
    change H * defectCount m (divisibleLabel m) = _
    rw [divisibleLabel_defectCount hm, Nat.mul_comm]

end Collatz.PeriodicDefectMinimum
