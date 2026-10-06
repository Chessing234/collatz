import Collatz.Research.PassageAtlas.Timing

/-! Complete, unbounded classification of possible coefficient first-crossing
TIMES. This does not give a crossing for each starting INTEGER. -/
namespace Collatz.Research.PassageAtlas
open FirstLightDescent StoppingAtlas

/-- Shorter parity vectors are the corresponding initial segments. -/
theorem parity_prefix_take (n H j : Nat) (hj : j ≤ H) :
    (parityVector n H).take j = parityVector n j := by
  unfold parityVector
  rw [← List.map_take, List.take_range, Nat.min_eq_left hj]

/-- Ones followed by zeros have an explicit prefix odd count. -/
theorem initial_ones_count (a b j : Nat) :
    ((List.replicate a 1 ++ List.replicate b 0).take j).count 1 = min j a := by
  simp only [List.take_append, List.take_replicate, List.length_replicate,
    List.count_append, List.count_replicate]
  simp

/-- Every occupied power band occurs as a first crossing at arbitrarily large inputs.
The construction uses a finite parity word and a lift of its binary residue. -/
theorem crossing_of_power_band {k a : Nat}
    (hb : 2 ^ k ≤ 3 ^ a ∧ 3 ^ a < 2 ^ (k + 1)) (B : Nat) :
    ∃ n : Nat, B < n ∧ 1 < n ∧ FirstLight n (k + 1) := by
  have ha : a ≤ k + 1 := by
    by_cases h : a ≤ k + 1
    · exact h
    · have hp : (2 : Nat) ^ (k + 1) ≤ 2 ^ a :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have h23 : (2 : Nat) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by decide) a
      omega
  let p := List.replicate a 1 ++ List.replicate (k + 1 - a) 0
  have hlen : p.length = k + 1 := by
    simp only [p, List.length_append, List.length_replicate]
    omega
  have hbits : ∀ x ∈ p, x = 0 ∨ x = 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (List.mem_replicate.mp hx).2
    · exact Or.inl (List.mem_replicate.mp hx).2
  obtain ⟨r, hr, hp⟩ := parityVector_surjective_mod_pow_two (k + 1) p hlen hbits
  let n := r + (B + 2) * 2 ^ (k + 1)
  have hmod : n % 2 ^ (k + 1) = r := by
    dsimp only [n]
    rw [Nat.add_mod, Nat.mul_mod]
    simp only [Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.mod_eq_of_lt hr]
  have hnvec : parityVector n (k + 1) = p := by
    rw [parityVector_mod_pow_two, hmod, hp]
  have hcount : ∀ j, j ≤ k + 1 → oddCount n j = min j a := by
    intro j hj
    unfold oddCount
    rw [← parity_prefix_take n (k + 1) j hj, hnvec]
    exact initial_ones_count a (k + 1 - a) j
  have hsize := Nat.mul_le_mul_left (B + 2)
    (show 1 ≤ 2 ^ (k + 1) by have := Nat.two_pow_pos (k + 1); omega)
  simp only [Nat.mul_one] at hsize
  refine ⟨n, by dsimp [n]; omega, by dsimp [n]; omega, ?_⟩
  constructor
  · rw [hcount (k + 1) (Nat.le_refl _), Nat.min_eq_right ha]
    exact hb.2
  · intro j hj
    rw [hcount j (by omega)]
    by_cases hja : j ≤ a
    · rw [Nat.min_eq_left hja]
      exact Nat.pow_le_pow_left (by decide) j
    · rw [Nat.min_eq_right (by omega : a ≤ j)]
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : j ≤ k)) hb.1

/-- A complete characterization of possible times, without a bounded horizon. -/
theorem crossing_time_iff_power_band (k : Nat) :
    (∃ n : Nat, 1 < n ∧ FirstLight n (k + 1)) ↔
      ∃ a : Nat, 2 ^ k ≤ 3 ^ a ∧ 3 ^ a < 2 ^ (k + 1) := by
  constructor
  · rintro ⟨n, _, hf⟩
    exact ⟨oddCount n (k + 1), firstLight_power_band hf⟩
  · rintro ⟨a, hb⟩
    obtain ⟨n, _, hn, hf⟩ := crossing_of_power_band hb 1
    exact ⟨n, hn, hf⟩

/-- The certified horizon transfers the complete time classification to actual stopping. -/
theorem stopping_time_iff_power_band {k : Nat} (hk : k + 1 ≤ 2592) :
    (∃ n : Nat, 1 < n ∧ stoppingTime n (k + 1)) ↔
      ∃ a : Nat, 2 ^ k ≤ 3 ^ a ∧ 3 ^ a < 2 ^ (k + 1) := by
  rw [← crossing_time_iff_power_band]
  constructor
  · rintro ⟨n, hn, hs⟩
    exact ⟨n, hn, (stopping_iff_firstLight_le_2592 hn hk).mp hs⟩
  · rintro ⟨n, hn, hf⟩
    exact ⟨n, hn, (stopping_iff_firstLight_le_2592 hn hk).mpr hf⟩

end Collatz.Research.PassageAtlas
