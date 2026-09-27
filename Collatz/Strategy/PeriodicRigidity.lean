import Collatz.Core.Reach

/-!
Periodic orbit labels are constant. A nonconstant periodic label therefore
has a full arithmetic progression of Collatz invariance defects.
This is an elementary formalization and quantitative corollary of modular
connectivity, not a proof of Collatz or a claim of historical novelty.
-/

namespace Collatz.PeriodicRigidity

def HasPeriod (f : Nat → α) (m : Nat) : Prop := ∀ n, f (n + m) = f n

theorem period_mul {f : Nat → α} {m : Nat} (h : HasPeriod f m)
    (n k : Nat) : f (n + k * m) = f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, h, ih]

theorem period_mod {f : Nat → α} {m : Nat} (h : HasPeriod f m)
    (n : Nat) : f n = f (n % m) := by
  have := period_mul h (n % m) (n / m)
  have he : n % m + n / m * m = n := by
    simpa [Nat.mul_comm] using Nat.mod_add_div n m
  rwa [he] at this

/-- Algebraic rigidity for the two inverse branch identities. -/
theorem branch_rigidity (m : Nat) (hm : 0 < m) (f : Nat → α)
    (hp : HasPeriod f m) (h2 : ∀ n, f (2 * n) = f n)
    (h3 : ∀ n, n % 2 = 1 → f (3 * n + 1) = f n) :
    ∀ n, f n = f 0 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases he : m % 2 = 0
    · have hp' : HasPeriod f (m / 2) := by
        intro n
        calc
          f (n + m / 2) = f (2 * (n + m / 2)) := (h2 _).symm
          _ = f (2 * n + m) := by congr 1; omega
          _ = f (2 * n) := hp _
          _ = f n := h2 _
      exact ih (m / 2) (by omega) (by omega) hp'
    · have ho : m % 2 = 1 := by omega
      have hall : ∀ n, f (3 * n + 1) = f n := by
        intro n
        by_cases hn : n % 2 = 1
        · exact h3 n hn
        · calc
            f (3 * n + 1) = f (3 * n + 1 + 3 * m) := (period_mul hp _ 3).symm
            _ = f (3 * (n + m) + 1) := by congr 1; omega
            _ = f (n + m) := h3 _ (by omega)
            _ = f n := hp n
      by_cases ht : m % 3 = 0
      · have hp' : HasPeriod f (m / 3) := by
          intro n
          calc
            f (n + m / 3) = f (3 * (n + m / 3) + 1) := (hall _).symm
            _ = f (3 * n + 1 + m) := by congr 1; omega
            _ = f (3 * n + 1) := hp _
            _ = f n := hall _
        exact ih (m / 3) (by omega) (by omega) hp'
      · have hadj : ∀ n, f (6 * n + 2) = f (6 * n + 1) := by
          intro n
          calc
            f (6 * n + 2) = f (2 * (3 * n + 1)) := by congr 1; omega
            _ = f n := (h2 _).trans (hall n)
            _ = f (3 * (2 * n) + 1) := ((hall _).trans (h2 n)).symm
            _ = f (6 * n + 1) := by congr 1; omega
        have hshift : ∀ n, f (n + 1) = f n := by
          intro n
          have hm6 : m % 6 = 1 ∨ m % 6 = 5 := by omega
          have hex : ∃ k, (n + k * m) % 6 = 1 := by
            rcases hm6 with h | h
            · have : (n + (7 - n % 6) * m) % 6 = 1 := by
                rw [Nat.add_mod, Nat.mul_mod, h]
                omega
              exact ⟨7 - n % 6, this⟩
            · have : (n + (n % 6 + 5) * m) % 6 = 1 := by
                rw [Nat.add_mod, Nat.mul_mod, h]
                omega
              exact ⟨n % 6 + 5, this⟩
          obtain ⟨k, hk⟩ := hex
          have heq : n + k * m = 6 * ((n + k * m) / 6) + 1 := by omega
          calc
            f (n + 1) = f (n + 1 + k * m) := (period_mul hp _ k).symm
            _ = f (6 * ((n + k * m) / 6) + 2) := by congr 1; omega
            _ = f (6 * ((n + k * m) / 6) + 1) := hadj _
            _ = f (n + k * m) := by rw [← heq]
            _ = f n := period_mul hp _ k
        intro n
        induction n with
        | zero => rfl
        | succ n hn => exact (hshift n).trans hn

/-- Every periodic invariant of the accelerated Collatz map is constant. -/
theorem invariant_constant {f : Nat → α} {m : Nat} (hm : 0 < m)
    (hp : HasPeriod f m) (hi : ∀ n, f (acceleratedStep n) = f n) :
    ∀ n, f n = f 0 := by
  have h2 : ∀ n, f (2 * n) = f n := by
    intro n
    have h := hi (2 * n)
    have hs : acceleratedStep (2 * n) = n := by simp [acceleratedStep]
    rw [hs] at h
    exact h.symm
  apply branch_rigidity m hm f hp h2
  intro n hn
  have hs : acceleratedStep n = (3 * n + 1) / 2 := by simp [acceleratedStep, hn]
  have he : 2 * ((3 * n + 1) / 2) = 3 * n + 1 := by omega
  calc
    f (3 * n + 1) = f (2 * ((3 * n + 1) / 2)) := by rw [he]
    _ = f ((3 * n + 1) / 2) := h2 _
    _ = f n := by simpa [hs] using hi n

/-- A defect is a step on which the label changes. -/
def Defect (f : Nat → α) (n : Nat) : Prop := f (acceleratedStep n) ≠ f n

theorem step_add_even (n d : Nat) :
    acceleratedStep (n + 2 * d) = acceleratedStep n +
      (if n % 2 = 0 then d else 3 * d) := by
  unfold acceleratedStep
  have he : (n + 2 * d) % 2 = n % 2 := by omega
  rw [he]
  split <;> omega

/-- Label defects repeat with period `2*m`, including when `m` is odd. -/
theorem defect_period {f : Nat → α} {m : Nat} (hp : HasPeriod f m) :
    HasPeriod (Defect f) (2 * m) := by
  intro n
  apply propext
  unfold Defect
  rw [step_add_even]
  have hf : f (n + 2 * m) = f n := period_mul hp n 2
  rw [hf]
  split
  · rw [hp]
  · rw [period_mul hp _ 3]

/-- Every nonconstant periodic label fails on a full positive progression.
There is at least one defect in each block of `2*m` consecutive integers. -/
theorem defect_progression {f : Nat → α} {m : Nat} (hm : 0 < m)
    (hp : HasPeriod f m) (hne : ∃ a b, f a ≠ f b) :
    ∃ r, 0 < r ∧ r < 2 * m ∧ ∀ k, Defect f (r + k * (2 * m)) := by
  classical
  have hex : ∃ n, Defect f n := by
    apply Classical.byContradiction
    intro hn
    have hi : ∀ n, f (acceleratedStep n) = f n := by
      intro n
      by_cases h : f (acceleratedStep n) = f n
      · exact h
      · exact False.elim (hn ⟨n, h⟩)
    obtain ⟨a, b, hab⟩ := hne
    exact hab ((invariant_constant hm hp hi a).trans (invariant_constant hm hp hi b).symm)
  obtain ⟨n, hn⟩ := hex
  have hr : Defect f (n % (2 * m)) := by
    rw [← period_mod (defect_period hp) n]
    exact hn
  refine ⟨n % (2 * m), ?_, Nat.mod_lt _ (by omega), ?_⟩
  · by_cases h : n % (2 * m) = 0
    · simp [h, Defect] at hr
    · omega
  · intro k
    rw [period_mul (defect_period hp)]
    exact hr

/-- The progression gives `K` distinct defects strictly below `2*m*K`.
This expresses the lower frequency `1/(2*m)` without asymptotic notation. -/
theorem defect_packing {f : Nat → α} {m : Nat} (hm : 0 < m)
    (hp : HasPeriod f m) (hne : ∃ a b, f a ≠ f b) :
    ∃ r, 0 < r ∧ r < 2 * m ∧
      (∀ K k, k < K → 0 < r + k * (2 * m) ∧
        r + k * (2 * m) < 2 * m * K ∧ Defect f (r + k * (2 * m))) ∧
      (∀ i j, r + i * (2 * m) = r + j * (2 * m) → i = j) := by
  obtain ⟨r, hr, hrm, hd⟩ := defect_progression hm hp hne
  refine ⟨r, hr, hrm, ?_, ?_⟩
  · intro K k hk
    have hmul := Nat.mul_le_mul_right (2 * m) (show k + 1 ≤ K by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    rw [Nat.mul_comm (2 * m) K]
    exact ⟨by omega, by omega, hd k⟩
  · intro i j hij
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * m) (by omega)

/-- The factor `1/(2*m)` is attained at `m=3`. -/
def threeLabel (n : Nat) : Bool := n % 3 == 0

theorem threeLabel_period : HasPeriod threeLabel 3 := by
  intro n
  simp [threeLabel]

theorem threeLabel_nonconstant : ∃ a b, threeLabel a ≠ threeLabel b := by
  exact ⟨0, 1, by decide⟩

/-- Exactly one of the six residue classes is defective. -/
theorem threeLabel_defect (n : Nat) : Defect threeLabel n ↔ n % 6 = 3 := by
  have hp := period_mod (defect_period threeLabel_period) n
  change Defect threeLabel n = Defect threeLabel (n % 6) at hp
  rw [hp]
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by decide)
  have hc : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨
      n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hc with h | h | h | h | h | h <;> rw [h] <;> unfold Defect <;> decide

/-- A label recording divisibility by the modulus. -/
def divisibleLabel (m n : Nat) : Bool := decide (n % m = 0)

theorem divisibleLabel_period (m : Nat) : HasPeriod (divisibleLabel m) m := by
  intro n
  simp [divisibleLabel]

/-- Sharpness at every modulus divisible by three, not just at modulus 3.
The unique defective class modulo `2*m` is `m` itself. -/
theorem divisibleLabel_defect {m : Nat} (hm : 0 < m)
    (hm3 : m % 3 = 0) (n : Nat) :
    Defect (divisibleLabel m) n ↔ n % (2 * m) = m := by
  have hp := period_mod (defect_period (divisibleLabel_period m)) n
  rw [hp]
  have hr : n % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  generalize n % (2 * m) = r at *
  have hrem : r % m = if r < m then r else r - m := by
    by_cases h : r < m
    · simp [h, Nat.mod_eq_of_lt h]
    · rw [if_neg h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hzero_or : r % m = 0 ↔ r = 0 ∨ r = m := by
    rw [hrem]
    split <;> omega
  by_cases he : r % 2 = 0
  · have hhalf : r / 2 < m := by omega
    simp only [Defect, divisibleLabel, acceleratedStep, he, if_true,
      Nat.mod_eq_of_lt hhalf]
    by_cases hz : r = 0
    · subst r; simp; omega
    · have hhz : r / 2 ≠ 0 := by omega
      have hzmod : r % m = 0 ↔ r = m := by rw [hzero_or]; omega
      simp [hhz, hzmod]
  · have hs : acceleratedStep r = (3 * r + 1) / 2 := by simp [acceleratedStep, he]
    have hs3 : acceleratedStep r % 3 = 2 := by rw [hs]; omega
    have hsmod : acceleratedStep r % m ≠ 0 := by
      intro h
      have heq : acceleratedStep r = m * (acceleratedStep r / m) := by
        have := Nat.div_add_mod (acceleratedStep r) m
        omega
      have hmod := congrArg (fun t => t % 3) heq
      rw [Nat.mul_mod, hm3] at hmod
      simp at hmod
      omega
    have hrzero : r % m = 0 ↔ r = m := by rw [hzero_or]; omega
    simp [Defect, divisibleLabel, hsmod, hrzero]

theorem divisibleLabel_nonconstant {m : Nat} (hm : 1 < m) :
    ∃ a b, divisibleLabel m a ≠ divisibleLabel m b := by
  refine ⟨0, 1, ?_⟩
  simp [divisibleLabel, Nat.mod_eq_of_lt hm]

/-- Sharpness uses the actual least positive period of the label. -/
theorem divisibleLabel_least_period {m d : Nat} (hd : 0 < d)
    (hp : HasPeriod (divisibleLabel m) d) : m ≤ d := by
  have h := hp 0
  simp [divisibleLabel] at h
  exact Nat.le_of_dvd hd (Nat.dvd_of_mod_eq_zero h)

/-- Periodicity is allowed to start after an arbitrary finite threshold. -/
def EventuallyPeriodic (f : Nat → α) : Prop :=
  ∃ m N, 0 < m ∧ ∀ n, N ≤ n → f (n + m) = f n

/-- An eventually periodic orbit invariant is constant on the positive integers.
Doubling transports every positive input above the exceptional finite region. -/
theorem eventually_invariant_constant {f : Nat → α}
    (hp : EventuallyPeriodic f)
    (hi : ∀ n, 0 < n → f (acceleratedStep n) = f n) :
    ∀ n, 0 < n → f n = f 1 := by
  obtain ⟨m, N, hm, hp⟩ := hp
  have h2 : ∀ n, 0 < n → f (2 * n) = f n := by
    intro n hn
    have h := hi (2 * n) (by omega)
    have hs : acceleratedStep (2 * n) = n := by simp [acceleratedStep]
    rw [hs] at h
    exact h.symm
  have hpow : ∀ k n, 0 < n → f (2 ^ k * n) = f n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc,
        h2 _ (Nat.mul_pos (Nat.pow_pos (by decide)) hn), ih n hn]
  have hpm : ∀ k n, N ≤ n → f (n + k * m) = f n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [Nat.succ_mul, ← Nat.add_assoc, hp _ (by omega), ih n hn]
  have hposperiod : ∀ n, 0 < n → f (n + m) = f n := by
    intro n hn
    have hbound : N ≤ 2 ^ N * n := by
      have hpowN : N < 2 ^ N := Nat.lt_two_pow_self
      have hmul := Nat.mul_le_mul_left (2 ^ N) (show 1 ≤ n by omega)
      omega
    calc
      f (n + m) = f (2 ^ N * (n + m)) := (hpow N _ (by omega)).symm
      _ = f (2 ^ N * n + 2 ^ N * m) := by rw [Nat.mul_add]
      _ = f (2 ^ N * n) := hpm _ _ hbound
      _ = f n := hpow N n hn
  let g : Nat → α := fun n => if n = 0 then f m else f n
  have hg : ∀ n, 0 < n → g n = f n := by
    intro n hn
    simp [g, show n ≠ 0 by omega]
  have hgp : HasPeriod g m := by
    intro n
    rw [hg _ (by omega)]
    by_cases hn : n = 0
    · subst n; simp [g]
    · rw [hg _ (by omega), hposperiod _ (by omega)]
  have hgi : ∀ n, g (acceleratedStep n) = g n := by
    intro n
    by_cases hn : n = 0
    · subst n; rfl
    · have hnpos : 0 < n := by omega
      have hspos : 0 < acceleratedStep n := by
        unfold acceleratedStep
        split <;> omega
      rw [hg _ hspos, hg _ hnpos]
      exact hi n hnpos
  intro n hn
  have he := (invariant_constant hm hgp hgi n).trans
    (invariant_constant hm hgp hgi 1).symm
  simpa [hg n hn, hg 1 (by decide)] using he

/-- Ultimate periodicity of the convergence set is already equivalent to Collatz.
This is a reduction, not a proof of the periodicity hypothesis. -/
theorem collatz_iff_eventually_periodic_basin :
    CollatzConjecture ↔ EventuallyPeriodic Reach.ReachesOne := by
  constructor
  · intro hc
    refine ⟨1, 1, by decide, ?_⟩
    intro n hn
    apply propext
    exact ⟨fun _ => hc n hn, fun _ => hc (n + 1) (by omega)⟩
  · intro hp n hn
    have hi : ∀ n, 0 < n → Reach.ReachesOne (acceleratedStep n) = Reach.ReachesOne n := by
      intro n hn
      apply propext
      exact (Reach.reachesOne_accStep_iff hn).symm
    have he := eventually_invariant_constant hp hi n hn
    change Reach.ReachesOne n
    rw [he]
    exact Reach.reachesOne_one

end Collatz.PeriodicRigidity
