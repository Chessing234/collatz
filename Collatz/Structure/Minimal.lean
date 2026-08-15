import Collatz.Structure.Congruence
import Collatz.Search.Verify
import Collatz.Search.Descent
import Collatz.Core.Minimum

/-!
# The minimal counterexample and its residue sieve

If Collatz fails, it fails at a smallest positive number.  This file extracts
that number and squeezes it.

The extraction is `exists_minimalCounterexample`.  The squeezing is the *sieve*:
combining the congruence engine of `Collatz.Structure.Congruence` with
minimality shows that a minimal counterexample cannot lie in any descending
residue class, and the surviving classes thin out rapidly:

| modulus | surviving residues                | density |
|---------|-----------------------------------|---------|
| `2`     | `1`                               | `1/2`   |
| `4`     | `3`                               | `1/4`   |
| `8`     | `3, 7`                            | `1/4`   |
| `16`    | `7, 11, 15`                       | `3/16`  |
| `32`    | `7, 15, 27, 31`                   | `1/8`   |
| `64`    | `7, 15, 27, 31, 39, 47, 59, 63`   | `1/8`   |

Every line of that table is a theorem below, proved by kernel computation over
the finitely many residues together with `not_descends_of_minimal`.

The sieve is not a proof of the conjecture — the surviving density does not
provably reach zero, which is exactly the open part — but it is the sharpest
elementary constraint available, and it is the engine that `Collatz.Strategy`
turns into a reduction.
-/

namespace Collatz
namespace Minimal

open Reach Congruence

/-! ## Extraction -/

/-- `IsCounterexample n` says `n` is a positive number that never reaches `1`. -/
def IsCounterexample (n : Nat) : Prop := 0 < n ∧ ¬ ReachesOne n

/-- `MinimalCounterexample n` says `n` is the least counterexample. -/
def MinimalCounterexample (n : Nat) : Prop :=
  IsCounterexample n ∧ ∀ m : Nat, 0 < m → m < n → ReachesOne m

/-- A minimal counterexample is positive. -/
theorem pos_of_minimal {n : Nat} (h : MinimalCounterexample n) : 0 < n := h.1.1

/-- A minimal counterexample does not reach `1`. -/
theorem not_reachesOne_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    ¬ ReachesOne n := h.1.2

/-- Everything strictly below a minimal counterexample reaches `1`. -/
theorem reachesOne_of_lt_minimal {n : Nat} (h : MinimalCounterexample n)
    {m : Nat} (hm : 0 < m) (hlt : m < n) : ReachesOne m := h.2 m hm hlt

/-- **Extraction.**  If the conjecture fails, a minimal counterexample exists. -/
theorem exists_minimalCounterexample (h : ¬ CollatzConjecture) :
    ∃ n : Nat, MinimalCounterexample n := by
  have hex : ∃ n : Nat, 0 < n ∧ ¬ ReachesOne n := by
    by_cases hc : ∃ n : Nat, 0 < n ∧ ¬ ReachesOne n
    · exact hc
    · exfalso
      refine h (fun n hn => ?_)
      by_cases hr : ReachesOne n
      · exact hr
      · exact absurd ⟨n, hn, hr⟩ hc
  obtain ⟨n, hpos, hnr, hmin⟩ := Minimum.exists_min_pos hex
  refine ⟨n, ⟨hpos, hnr⟩, fun m hm hlt => ?_⟩
  by_cases hr : ReachesOne m
  · exact hr
  · exact absurd hr (hmin m hm hlt)

/-- Conversely, a minimal counterexample refutes the conjecture. -/
theorem not_collatz_of_minimalCounterexample {n : Nat} (h : MinimalCounterexample n) :
    ¬ CollatzConjecture := fun hC => h.1.2 (hC n h.1.1)

/-- The conjecture is equivalent to the nonexistence of a minimal
counterexample. -/
theorem collatz_iff_no_minimalCounterexample :
    CollatzConjecture ↔ ¬ ∃ n : Nat, MinimalCounterexample n := by
  constructor
  · intro hC ⟨n, hn⟩
    exact not_collatz_of_minimalCounterexample hn hC
  · intro hno
    by_cases hC : CollatzConjecture
    · exact hC
    · exact absurd (exists_minimalCounterexample hC) hno

/-! ## Elementary constraints -/

/-- A minimal counterexample exceeds every verified bound. -/
theorem gt_1024_of_minimal {n : Nat} (h : MinimalCounterexample n) : 1024 < n :=
  Search.counterexample_gt_1024 h.1.1 h.1.2

/-- The sharper verified bound, from descent verification. -/
theorem gt_10000_of_minimal {n : Nat} (h : MinimalCounterexample n) : 10000 < n :=
  Search.counterexample_gt_10000 h.1.1 h.1.2

/-- A minimal counterexample exceeds one. -/
theorem gt_one_of_minimal {n : Nat} (h : MinimalCounterexample n) : 1 < n := by
  have := gt_1024_of_minimal h; omega

/-- **A minimal counterexample is odd.**  An even counterexample would be twice a
smaller counterexample. -/
theorem odd_of_minimal {n : Nat} (h : MinimalCounterexample n) : n % 2 = 1 := by
  rcases Arith.mod_two_eq_zero_or_one n with heven | hodd
  · exfalso
    have hpos := pos_of_minimal h
    have hgt := gt_one_of_minimal h
    have hhalf : ReachesOne (n / 2) :=
      reachesOne_of_lt_minimal h (by omega) (by omega)
    exact h.1.2 ((reachesOne_even_iff hpos heven).mpr hhalf)
  · exact hodd

/-- No accelerated iterate of a minimal counterexample drops below it. -/
theorem not_accOrbit_lt_of_minimal {n : Nat} (h : MinimalCounterexample n) (k : Nat) :
    ¬ acceleratedOrbit k n < n := by
  intro hlt
  have hpos := pos_of_minimal h
  have hposk : 0 < acceleratedOrbit k n := acceleratedOrbit_positive hpos k
  have hreach : ReachesOne (acceleratedOrbit k n) :=
    reachesOne_of_lt_minimal h hposk hlt
  exact h.1.2 (reachesOne_of_accOrbit hpos hreach)

/-- **The sieve step.**  A minimal counterexample lies in no descending residue
class. -/
theorem not_descends_of_minimal {n : Nat} (h : MinimalCounterexample n) (k : Nat)
    (hk : 2 ^ k ≤ n) : ¬ Descends k (n % 2 ^ k) := by
  intro hd
  exact not_accOrbit_lt_of_minimal h k (accOrbit_lt_of_descends_of_mod hd hk)

/-- The powers of two that the sieve may use, given that a minimal
counterexample exceeds `1024`. -/
theorem pow_two_le_of_minimal {n : Nat} (h : MinimalCounterexample n) {k : Nat}
    (hk : k ≤ 13) : 2 ^ k ≤ n := by
  have h1 : (2:Nat) ^ k ≤ 2 ^ 13 := Arith.two_pow_le_two_pow hk
  have h2 : (2:Nat) ^ 13 = 8192 := by decide
  have h3 := gt_10000_of_minimal h
  omega

/-- The sieve condition at a modulus at most `2 ^ 10`. -/
theorem not_descends_of_minimal' {n : Nat} (h : MinimalCounterexample n) {k : Nat}
    (hk : k ≤ 13) : ¬ Descends k (n % 2 ^ k) :=
  not_descends_of_minimal h k (pow_two_le_of_minimal h hk)

/-! ## The residue sieve

Each theorem below intersects the sieve conditions at all moduli up to `2 ^ j`
and reads off the surviving residues.  The finite sweep is a single Boolean
computation closed by `decide`. -/

/-- Reducing the modulus of a residue. -/
theorem mod_pow_two_mod {n j k : Nat} (hjk : j ≤ k) :
    n % 2 ^ k % 2 ^ j = n % 2 ^ j :=
  Nat.mod_mod_of_dvd n (Arith.two_pow_dvd_two_pow hjk)

/-- **A minimal counterexample survives the sieve at every level up to `10`.** -/
theorem survives_of_minimal {n : Nat} (h : MinimalCounterexample n) {j : Nat}
    (hj : j ≤ 13) : survives j (n % 2 ^ j) = true := by
  refine survives_of_not_descends (fun i hi => ?_)
  rw [mod_pow_two_mod (by omega : i ≤ j)]
  exact not_descends_of_minimal' h (by omega)

/-- The residue of a minimal counterexample lies below its modulus. -/
theorem mod_lt_of_minimal (n : Nat) (j : Nat) : n % 2 ^ j < 2 ^ j :=
  Nat.mod_lt _ (Arith.two_pow_pos j)

theorem sieveCheck_one : sieveCheck 1 [1] = true := by decide
theorem sieveCheck_two : sieveCheck 2 [3] = true := by decide
theorem sieveCheck_three : sieveCheck 3 [3, 7] = true := by decide
theorem sieveCheck_four : sieveCheck 4 [7, 11, 15] = true := by decide
theorem sieveCheck_five : sieveCheck 5 [7, 15, 27, 31] = true := by decide
theorem sieveCheck_six : sieveCheck 6 [7, 15, 27, 31, 39, 47, 59, 63] = true := by decide

set_option maxRecDepth 10000 in
theorem sieveCheck_seven :
    sieveCheck 7 [27, 31, 39, 47, 63, 71, 79, 91, 95, 103, 111, 123, 127] = true := by
  decide

set_option maxRecDepth 40000 in
theorem sieveCheck_eight :
    sieveCheck 8 [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223,
      231, 239, 251, 255] = true := by
  decide


set_option maxRecDepth 100000 in
/-- At modulus `512` only `38` of `512` classes survive. -/
theorem sieveCheck_nine :
    sieveCheck 9
    [      27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251,
      255, 283, 287, 303, 319, 327, 347, 359, 367, 383, 411, 415, 423, 447, 463, 479, 487,
      495, 507, 511] = true := by
  decide

set_option maxRecDepth 200000 in
/-- At modulus `1024` only `64` of `1024` classes survive, a density of
`1/16`. -/
theorem sieveCheck_ten :
    sieveCheck 10
    [      27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251,
      255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543,
      559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831,
      839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] = true := by
  decide

/-- A minimal counterexample is odd, read off the sieve at modulus `2`. -/
theorem mod_two_of_minimal {n : Nat} (h : MinimalCounterexample n) : n % 2 = 1 := by
  have hc := mem_allowed_of_sieveCheck sieveCheck_one
    (mod_lt_of_minimal n 1) (survives_of_minimal h (by omega))
  rw [show (2:Nat) ^ 1 = 2 from by decide] at hc
  simpa using hc

/-- A minimal counterexample is `3` modulo `4`. -/
theorem mod_four_of_minimal {n : Nat} (h : MinimalCounterexample n) : n % 4 = 3 := by
  have hc := mem_allowed_of_sieveCheck sieveCheck_two
    (mod_lt_of_minimal n 2) (survives_of_minimal h (by omega))
  rw [show (2:Nat) ^ 2 = 4 from by decide] at hc
  simpa using hc

/-- A minimal counterexample is `3` or `7` modulo `8`. -/
theorem mod_eight_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    n % 8 = 3 ∨ n % 8 = 7 := by
  have hc := mem_allowed_of_sieveCheck sieveCheck_three
    (mod_lt_of_minimal n 3) (survives_of_minimal h (by omega))
  rw [show (2:Nat) ^ 3 = 8 from by decide] at hc
  simpa using hc

/-- A minimal counterexample is `7`, `11` or `15` modulo `16`. -/
theorem mod_sixteen_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by
  have hc := mem_allowed_of_sieveCheck sieveCheck_four
    (mod_lt_of_minimal n 4) (survives_of_minimal h (by omega))
  rw [show (2:Nat) ^ 4 = 16 from by decide] at hc
  simpa using hc

/-- A minimal counterexample is `7`, `15`, `27` or `31` modulo `32`. -/
theorem mod_thirtytwo_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31 := by
  have hc := mem_allowed_of_sieveCheck sieveCheck_five
    (mod_lt_of_minimal n 5) (survives_of_minimal h (by omega))
  rw [show (2:Nat) ^ 5 = 32 from by decide] at hc
  simpa using hc

/-- A minimal counterexample lies in one of eight classes modulo `64`. -/
theorem mod_sixtyfour_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    n % 64 = 7 ∨ n % 64 = 15 ∨ n % 64 = 27 ∨ n % 64 = 31 ∨
    n % 64 = 39 ∨ n % 64 = 47 ∨ n % 64 = 59 ∨ n % 64 = 63 := by
  have hc := mem_allowed_of_sieveCheck sieveCheck_six
    (mod_lt_of_minimal n 6) (survives_of_minimal h (by omega))
  rw [show (2:Nat) ^ 6 = 64 from by decide] at hc
  simpa using hc

/-- A minimal counterexample lies in one of thirteen classes modulo `128`. -/
theorem mod_onetwentyeight_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    n % 128 = 27 ∨ n % 128 = 31 ∨ n % 128 = 39 ∨ n % 128 = 47 ∨ n % 128 = 63 ∨
    n % 128 = 71 ∨ n % 128 = 79 ∨ n % 128 = 91 ∨ n % 128 = 95 ∨ n % 128 = 103 ∨
    n % 128 = 111 ∨ n % 128 = 123 ∨ n % 128 = 127 := by
  have hc := mem_allowed_of_sieveCheck sieveCheck_seven
    (mod_lt_of_minimal n 7) (survives_of_minimal h (by omega))
  rw [show (2:Nat) ^ 7 = 128 from by decide] at hc
  simpa using hc

/-- A minimal counterexample lies in one of nineteen classes modulo `256`:
only `19/256 ≈ 7.4%` of residues survive. -/
theorem mod_twofiftysix_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    n % 256 = 27 ∨ n % 256 = 31 ∨ n % 256 = 47 ∨ n % 256 = 63 ∨ n % 256 = 71 ∨
    n % 256 = 91 ∨ n % 256 = 103 ∨ n % 256 = 111 ∨ n % 256 = 127 ∨ n % 256 = 155 ∨
    n % 256 = 159 ∨ n % 256 = 167 ∨ n % 256 = 191 ∨ n % 256 = 207 ∨ n % 256 = 223 ∨
    n % 256 = 231 ∨ n % 256 = 239 ∨ n % 256 = 251 ∨ n % 256 = 255 := by
  have hc := mem_allowed_of_sieveCheck sieveCheck_eight
    (mod_lt_of_minimal n 8) (survives_of_minimal h (by omega))
  rw [show (2:Nat) ^ 8 = 256 from by decide] at hc
  simpa using hc

/-- The sieve is consistent with oddness: every surviving residue modulo `4` is
odd, recovering `odd_of_minimal` from the congruence side. -/
theorem odd_of_mod_four {n : Nat} (h : n % 4 = 3) : n % 2 = 1 := by omega

/-- A minimal counterexample is congruent to `3` modulo `4`, hence `n = 4m + 3`
for some `m`, and the class `3 mod 4` is the unique nondescending class. -/
theorem eq_four_mul_add_three_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    ∃ m : Nat, n = 4 * m + 3 := by
  have hm := mod_four_of_minimal h
  exact ⟨n / 4, by omega⟩

/-- On the surviving class the two-step accelerated map *grows*: `T²(4m+3) = 9m+8`.
This is the precise obstruction — the sieve pushes a counterexample into the one
class where the elementary descent argument fails. -/
theorem accOrbit_two_of_minimal {n : Nat} (h : MinimalCounterexample n) :
    ∃ m : Nat, n = 4 * m + 3 ∧ acceleratedOrbit 2 n = 9 * m + 8 := by
  obtain ⟨m, hm⟩ := eq_four_mul_add_three_of_minimal h
  exact ⟨m, hm, by rw [hm]; exact accOrbit_two_three_mod_four m⟩

end Minimal
end Collatz
