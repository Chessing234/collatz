import Collatz.Strategy.ThreeAdicEscape

/-!
# Residues at first descent

The fixed-time modulo-three population has a two-to-one bias toward residue
two. First-descent sampling follows a different rule. Residue zero at first
descent is possible exactly for initial values divisible by six, and the
stopping time is then one. No existence of a stopping time is assumed for
arbitrary positive inputs.
-/

namespace Collatz.FirstDescentResidue

/-- A positive even input first descends in one step. -/
theorem stoppingTime_of_even {n : Nat} (hn : 0 < n) (he : n % 2 = 0) :
    stoppingTime n 1 := by
  refine ⟨by decide, ?_, ?_⟩
  · simp only [acceleratedOrbit_succ, acceleratedOrbit_zero]
    simp only [acceleratedStep, if_pos he]
    exact Nat.div_lt_self hn (by decide)
  · intro j hj hlt
    omega

/-- A first-descent index is uniquely determined if it exists. -/
theorem stoppingTime_unique {n k j : Nat}
    (hk : stoppingTime n k) (hj : stoppingTime n j) : k = j := by
  obtain ⟨hkpos, hkdrop, hkfirst⟩ := hk
  obtain ⟨hjpos, hjdrop, hjfirst⟩ := hj
  by_cases hkj : k < j
  · exact False.elim (hjfirst k hkpos hkj hkdrop)
  · by_cases hjk : j < k
    · exact False.elim (hkfirst j hjpos hjk hjdrop)
    · omega

/-- An odd accelerated step strictly increases its input. -/
theorem odd_step_increases {n : Nat} (hn : n % 2 = 1) :
    n < acceleratedStep n := by
  simp only [acceleratedStep, if_neg (by omega : n % 2 ≠ 0)]
  omega

/-- Every one-step first descent starts from an even input. -/
theorem even_of_stoppingTime_one {n : Nat} (h : stoppingTime n 1) : n % 2 = 0 := by
  have hd : acceleratedStep n < n := h.2.1
  by_cases he : n % 2 = 0
  · exact he
  · have hg := odd_step_increases (show n % 2 = 1 by omega)
    omega

/-- A positive input has one-step stopping time exactly when it is even. -/
theorem stoppingTime_one_iff_even {n : Nat} (hn : 0 < n) :
    stoppingTime n 1 ↔ n % 2 = 0 :=
  ⟨even_of_stoppingTime_one, stoppingTime_of_even hn⟩

/-- A first descent landing in residue zero necessarily took one step. -/
theorem zero_landing_forces_one {n k : Nat} (hn : 0 < n)
    (hk : stoppingTime n k) (hz : 3 ∣ acceleratedOrbit k n) : k = 1 := by
  have hkn : 1 ≤ k := hk.1
  by_cases he : n % 2 = 0
  · exact stoppingTime_unique hk (stoppingTime_of_even hn he)
  · have ho : n % 2 = 1 := by omega
    obtain ⟨j, hj⟩ : ∃ j : Nat, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj] at hz
    exact False.elim (ThreeAdicEscape.odd_escape_persistent ho j hz)

/-- Zero-residue landings occur exactly on the divisible-by-six initial class. -/
theorem zero_landing_iff_six {n k : Nat} (hn : 0 < n) (hk : stoppingTime n k) :
    3 ∣ acceleratedOrbit k n ↔ 6 ∣ n := by
  constructor
  · intro hz
    have hk1 := zero_landing_forces_one hn hk hz
    rw [hk1, ThreeAdicEscape.orbit_divisible_three_iff] at hz
    exact hz
  · intro h6
    obtain ⟨q, hq⟩ := h6
    have he : n % 2 = 0 := by rw [hq]; omega
    have hk1 := stoppingTime_unique hk (stoppingTime_of_even hn he)
    rw [hk1, ThreeAdicEscape.orbit_divisible_three_iff]
    exact ⟨q, hq⟩

/-- The residue-zero landing class admits unconditional descent witnesses. -/
theorem exists_zero_landing_iff {n : Nat} (hn : 0 < n) :
    (∃ k : Nat, stoppingTime n k ∧ 3 ∣ acceleratedOrbit k n) ↔ 6 ∣ n := by
  constructor
  · rintro ⟨k, hk, hz⟩
    exact (zero_landing_iff_six hn hk).mp hz
  · intro h6
    obtain ⟨q, hq⟩ := h6
    have he : n % 2 = 0 := by rw [hq]; omega
    have hs := stoppingTime_of_even hn he
    exact ⟨1, hs, (zero_landing_iff_six hn hs).mpr ⟨q, hq⟩⟩

/-- Every stopping time beyond one lands outside the multiples of three. -/
theorem delayed_landing_nonzero {n k : Nat} (hn : 0 < n)
    (hk : stoppingTime n k) (hdelay : 1 < k) : ¬ 3 ∣ acceleratedOrbit k n := by
  intro hz
  have h := zero_landing_forces_one hn hk hz
  omega

/-- The state immediately before any first descent is even. -/
theorem last_state_even {n k : Nat} (hk : stoppingTime n (k + 1)) :
    acceleratedOrbit k n % 2 = 0 := by
  have hdrop := hk.2.1
  rw [acceleratedOrbit_succ_step] at hdrop
  have hbefore : n ≤ acceleratedOrbit k n := by
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hf := hk.2.2 k (by omega) (by omega)
      omega
  by_cases he : acceleratedOrbit k n % 2 = 0
  · exact he
  · have ho := odd_step_increases (show acceleratedOrbit k n % 2 = 1 by omega)
    omega

end Collatz.FirstDescentResidue
