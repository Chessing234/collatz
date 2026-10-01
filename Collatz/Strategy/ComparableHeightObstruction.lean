import Collatz.Strategy.ResidueMonotoneObstruction

/-!
# A bounded-distortion obstruction to bounded descent

A natural-valued height eventually trapped between n+1 and C*(n+1) cannot
admit uniformly bounded positive descent times for the accelerated Collatz
map. No monotonicity or residue regularity of the height is assumed.

The argument concatenates descent choices inside an arbitrarily long all-odd
run. The resulting orbit grows by more than the allowed multiplicative
variation of the height. This restricts a class of possible universal-descent
certificates; it does not rule out unbounded schedules or all height functions.
-/

namespace Collatz.ComparableHeightObstruction

open ResidueMonotoneObstruction

/-- An elementary integer form of Bernoulli's inequality for (3/2)^i. -/
theorem linear_growth_bound (i : Nat) : (i+2)*2^i ≤ 2*3^i := by
  induction i with
  | zero => decide
  | succ i ih =>
    have h := Nat.mul_le_mul_left 3 ih
    have hm := Nat.mul_le_mul_right (2^i) (by omega : (i+3)*2≤(i+2)*3)
    calc
      (i+1+2)*2^(i+1) ≤ (i+2)*3*2^i := by
        simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.add_assoc, Nat.reduceAdd] using hm
      _ ≤ 2*3^(i+1) := by
        simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using h

/-- After more than 2C odd steps, growth exceeds an arbitrary factor C. -/
theorem power_ratio_exceeds {C i : Nat} (hi : 2*C+1≤i) : C*2^i < 3^i := by
  have hb := linear_growth_bound i
  have hp : 0 < (2:Nat)^i := Nat.pow_pos (by decide)
  have hm := Nat.mul_le_mul_right (2^i) hi
  simp only [Nat.add_mul, Nat.mul_assoc] at hb hm
  omega

/-- The explicit odd-run witness exceeds a prescribed size factor at any
sufficiently late time within the run. -/
theorem odd_run_exceeds {C q K i : Nat} (hq : 0<q)
    (hi : 2*C+1≤i) (hiK : i≤K) :
    C*((q*2^K-1)+1) < acceleratedOrbit i (q*2^K-1)+1 := by
  rw [orbit_mul_pow_pred q K hq i hiK]
  have hp : 0<q*2^K := Nat.mul_pos hq (Nat.pow_pos (by decide))
  have hr : 0<q*3^i*2^(K-i) :=
    Nat.mul_pos (Nat.mul_pos hq (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))
  rw [Nat.sub_add_cancel (by omega : 1≤q*2^K),
    Nat.sub_add_cancel (by omega : 1≤q*3^i*2^(K-i))]
  have he : 2^K=2^i*2^(K-i) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [he]
  have ht := Nat.mul_lt_mul_of_pos_right (power_ratio_exceeds hi)
    (Nat.mul_pos hq (Nat.pow_pos (by decide) : 0<(2:Nat)^(K-i)))
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ht

/-- Concatenate a fixed number of bounded descent choices while the orbit
remains above the exceptional range. Only nonincrease is needed here. -/
theorem concatenate_descent (height : Nat → Nat) (B cutoff n rounds : Nat)
    (hn : cutoff<n ∧ 1<n)
    (hrun : ∀ t, 0<t → t≤B*rounds → n<acceleratedOrbit t n)
    (hdesc : ∀ x, cutoff<x → 1<x → ∃ k, 0<k ∧ k≤B ∧
      height (acceleratedOrbit k x)≤height x) :
    ∀ j, j≤rounds → ∃ t, j≤t ∧ t≤B*j ∧
      height (acceleratedOrbit t n)≤height n := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨0, by omega, by omega, Nat.le_refl _⟩
  | succ j ih =>
    intro hj
    obtain ⟨t, hjt, ht, hh⟩ := ih (by omega)
    have htn : n≤acceleratedOrbit t n := by
      by_cases hz : t=0
      · subst t; exact Nat.le_refl _
      · have hbound := Nat.mul_le_mul_left B (by omega : j≤rounds)
        exact Nat.le_of_lt (hrun t (by omega) (by omega))
    obtain ⟨k, hk, hkB, hdrop⟩ := hdesc (acceleratedOrbit t n) (by omega) (by omega)
    refine ⟨k+t, by omega, ?_, ?_⟩
    · rw [Nat.mul_succ]
      omega
    · rw [← acceleratedOrbit_add]
      exact Nat.le_trans hdrop hh

/-- No height with bounded multiplicative distortion of size supports a
uniformly bounded descent schedule, even outside an arbitrary finite range.
The height may oscillate arbitrarily between its two bounds. -/
theorem no_bounded_comparable_height_nonincrease (height : Nat → Nat)
    (C B cutoff : Nat)
    (hheight : ∀ n, cutoff<n → 1<n → n+1≤height n ∧ height n≤C*(n+1)) :
    ¬ (∀ n, cutoff<n → 1<n → ∃ k, 0<k ∧ k≤B ∧
      height (acceleratedOrbit k n)≤height n) := by
  intro hdesc
  let rounds := 2*C+1
  let K := B*rounds+1
  let q := cutoff+3
  let n := q*2^K-1
  have hq : 0<q := by dsimp [q]; omega
  have hn : cutoff<n ∧ 1<n := by
    have hp := Nat.one_le_pow K 2 (by decide)
    have hm := Nat.mul_le_mul_left q hp
    dsimp [n, q] at *
    omega
  have hrun : ∀ t, 0<t → t≤B*rounds → n<acceleratedOrbit t n := by
    intro t ht htb
    have h := (same_residue_rising_run 1 q (B*rounds) (by decide) hq t ht htb).1
    simpa only [Nat.one_mul] using h
  obtain ⟨t, htmin, htmax, hh⟩ :=
    concatenate_descent height B cutoff n rounds hn hrun
      hdesc rounds (Nat.le_refl _)
  have hg : C*(n+1)<acceleratedOrbit t n+1 :=
    odd_run_exceeds hq htmin (by dsimp [K]; omega)
  have hr := hrun t (by dsimp [rounds] at htmin; omega) htmax
  have hl := (hheight (acceleratedOrbit t n) (by omega) (by omega)).1
  have hu := (hheight n hn.1 hn.2).2
  omega

/-- Strict descent is a special case of the excluded nonincrease schedule. -/
theorem no_bounded_comparable_height_descent (height : Nat → Nat)
    (C B cutoff : Nat)
    (hheight : ∀ n, cutoff<n → 1<n → n+1≤height n ∧ height n≤C*(n+1)) :
    ¬ (∀ n, cutoff<n → 1<n → ∃ k, 0<k ∧ k≤B ∧
      height (acceleratedOrbit k n)<height n) := by
  intro h
  apply no_bounded_comparable_height_nonincrease height C B cutoff hheight
  intro n hn h1
  obtain ⟨k, hk, hkB, hd⟩ := h n hn h1
  exact ⟨k, hk, hkB, Nat.le_of_lt hd⟩

/-- A fixed factor on the lower comparison bound also does not help. Thus the
obstruction applies to heights comparable to size from both sides, with no
normalization of the lower factor required. -/
theorem no_bounded_two_sided_comparable_height (height : Nat → Nat)
    (A C B cutoff : Nat)
    (hheight : ∀ n, cutoff<n → 1<n → n+1≤A*height n ∧ height n≤C*(n+1)) :
    ¬ (∀ n, cutoff<n → 1<n → ∃ k, 0<k ∧ k≤B ∧
      height (acceleratedOrbit k n)≤height n) := by
  intro h
  apply no_bounded_comparable_height_nonincrease (fun n => A*height n)
    (A*C) B cutoff
  · intro n hn h1
    obtain ⟨hl, hu⟩ := hheight n hn h1
    refine ⟨hl, ?_⟩
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left A hu
  · intro n hn h1
    obtain ⟨k, hk, hkB, hd⟩ := h n hn h1
    exact ⟨k, hk, hkB, Nat.mul_le_mul_left A hd⟩

end Collatz.ComparableHeightObstruction
