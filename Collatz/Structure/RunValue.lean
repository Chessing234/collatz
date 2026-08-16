import Collatz.Structure.RunBounds

/-!
# The exact value after a run

`OddRuns.two_mul_succ_step` says `2(T(x) + 1) = 3(x + 1)` for odd `x`.  Iterating
it along a run of `j` consecutive odd steps gives the closed form

`2 ^ j · (T^j(x) + 1) = 3 ^ j · (x + 1)`.

A run is not merely bounded, it is *computed*: writing `x + 1 = 2 ^ j · q`, the
value at the end of the run is exactly `3 ^ j · q − 1`.  The whole climb is a
single multiplication by `3 ^ j`, performed on `x + 1` rather than on `x`.

This is what upgrades the run bounds into a quantitative statement about cycles.
A cycle's greatest point `M` dominates the end of the run starting at its least
point `m`, so

`3 ^ j · (m + 1) ≤ 2 ^ j · (M + 1)`,  i.e.  `M + 1 ≥ (3/2) ^ j · (m + 1)`,

where `j` is the length of the run at the minimum.  Since the minimum always
begins a run of length at least two (`RunBounds.min_oddRun_two`), this gives

`4 · (M + 1) ≥ 9 · (m + 1)`,

improving `CycleExtremes.two_mul_min_le_cycleMax` from `M ≥ 2m` to
`M ≥ 2.25 m + 1.25`.  On the class `m ≡ 7 (mod 8)` the run has length three and
the constant rises again, to `M ≥ 3.375 m + 2.375`.
-/

namespace Collatz
namespace RunValue

open Reach Congruence AccCycle CycleExtremes OddRuns RunBounds

/-! ## The closed form -/

/-- A run of length `j + 1` continues as a run of length `j` from the next
value. -/
theorem oddRun_tail {x j : Nat} (h : OddRun x (j + 1)) : OddRun (acceleratedStep x) j := by
  refine (oddRun_iff j (acceleratedStep x)).mpr ?_
  have hdvd : 2 ^ (j + 1) ∣ (x + 1) := (oddRun_iff (j + 1) x).mp h
  have hx : x % 2 = 1 := by
    have := h 0 (by omega)
    rw [acceleratedOrbit] at this
    exact this
  obtain ⟨c, hc⟩ := hdvd
  have hA : (2:Nat) ^ (j + 1) * c = 2 * (2 ^ j * c) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  rw [hA] at hc
  have hid := two_mul_succ_step hx
  rw [hc] at hid
  have hexp : 3 * (2 * (2 ^ j * c)) = 2 * (3 * (2 ^ j * c)) := by
    rw [Nat.mul_left_comm]
  rw [hexp] at hid
  refine ⟨3 * c, ?_⟩
  have hcomm : (2:Nat) ^ j * (3 * c) = 3 * (2 ^ j * c) := by
    rw [Nat.mul_left_comm]
  rw [hcomm]
  omega

/-- **The closed form for a run.**  Along `j` consecutive odd steps the quantity
`x + 1` is multiplied by exactly `(3/2) ^ j`. -/
theorem oddRun_value : ∀ (j x : Nat), OddRun x j →
    2 ^ j * (acceleratedOrbit j x + 1) = 3 ^ j * (x + 1) := by
  intro j
  induction j with
  | zero =>
    intro x _
    rw [acceleratedOrbit]
  | succ j ih =>
    intro x h
    have hx : x % 2 = 1 := by
      have := h 0 (by omega)
      rw [acceleratedOrbit] at this
      exact this
    have htail := ih (acceleratedStep x) (oddRun_tail h)
    have hshift : acceleratedOrbit (j + 1) x = acceleratedOrbit j (acceleratedStep x) := rfl
    have hid := two_mul_succ_step hx
    have hL : (2:Nat) ^ (j + 1) * (acceleratedOrbit (j + 1) x + 1)
        = 2 * (2 ^ j * (acceleratedOrbit j (acceleratedStep x) + 1)) := by
      rw [hshift, Arith.two_pow_succ, Nat.mul_assoc]
    have hR : (3:Nat) ^ (j + 1) * (x + 1) = 3 ^ j * (3 * (x + 1)) := by
      rw [Arith.three_pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
    rw [hL, htail, hR, ← hid, Nat.mul_left_comm]

/-- Written multiplicatively: if `x + 1 = 2 ^ j · q` then the run ends at
`3 ^ j · q − 1`. -/
theorem oddRun_value_quot {x j q : Nat} (h : OddRun x j) (hq : x + 1 = 2 ^ j * q) :
    acceleratedOrbit j x + 1 = 3 ^ j * q := by
  have hval := oddRun_value j x h
  rw [hq] at hval
  have hA : (3:Nat) ^ j * (2 ^ j * q) = 2 ^ j * (3 ^ j * q) := by
    rw [Nat.mul_left_comm]
  rw [hA] at hval
  have hpos : 0 < 2 ^ j := Arith.two_pow_pos j
  exact Nat.eq_of_mul_eq_mul_left hpos hval

/-- `2 ^ j < 3 ^ j` for `j ≥ 1`. -/
theorem two_pow_lt_three_pow : ∀ j : Nat, 0 < j → 2 ^ j < 3 ^ j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; decide
    · have hlt := ih h0
      rw [Arith.two_pow_succ, Arith.three_pow_succ]
      omega

/-- The run strictly increases the value once `j ≥ 1` and `x ≥ 1`: the climb is
real, not a formality. -/
theorem lt_oddRun_value {x j : Nat} (hx : 0 < x) (hj : 0 < j) (h : OddRun x j) :
    x < acceleratedOrbit j x := by
  have hval := oddRun_value j x h
  have h2 : (2:Nat) ^ j < 3 ^ j := two_pow_lt_three_pow j hj
  have hkey : 2 ^ j * (x + 1) < 3 ^ j * (x + 1) :=
    Nat.mul_lt_mul_of_pos_right h2 (by omega)
  rw [← hval] at hkey
  have := Nat.lt_of_mul_lt_mul_left hkey
  omega

/-! ## The two-step identity -/

/-- A run of length two is exactly the class `3 mod 4`. -/
theorem oddRun_two_iff_mod_four (m : Nat) : OddRun m 2 ↔ m % 4 = 3 := by
  have h4 : (2:Nat) ^ 2 = 4 := by decide
  constructor
  · intro h
    have hdvd : 2 ^ 2 ∣ (m + 1) := (oddRun_iff 2 m).mp h
    rw [h4] at hdvd
    omega
  · intro h
    refine (oddRun_iff 2 m).mpr ?_
    rw [h4]
    omega

/-- **The two-step climb is exact.**  Every `m ≡ 3 (mod 4)` satisfies
`4 (T²(m) + 1) = 9 (m + 1)` — no inequality, an identity.  So the first two
steps of any such number multiply `m + 1` by exactly `9/4`. -/
theorem two_step_exact {m : Nat} (h : m % 4 = 3) :
    4 * (acceleratedOrbit 2 m + 1) = 9 * (m + 1) := by
  have hrun := (oddRun_two_iff_mod_four m).mpr h
  have hval := oddRun_value 2 m hrun
  have h9 : (3:Nat) ^ 2 = 9 := by decide
  have h4 : (2:Nat) ^ 2 = 4 := by decide
  rw [h9, h4] at hval
  exact hval

/-- Likewise the three-step climb on `m ≡ 7 (mod 8)`. -/
theorem three_step_exact {m : Nat} (h : m % 8 = 7) :
    8 * (acceleratedOrbit 3 m + 1) = 27 * (m + 1) := by
  have hrun := run_three_of_mod_eight h
  have hval := oddRun_value 3 m hrun
  have h27 : (3:Nat) ^ 3 = 27 := by decide
  have h8 : (2:Nat) ^ 3 = 8 := by decide
  rw [h27, h8] at hval
  exact hval

/-! ## The improved cycle bound -/

/-- **A cycle must be at least `(3/2) ^ j` times its least point**, where `j` is
the length of the run of odd steps starting there. -/
theorem cycleMax_ge_of_run {n L m j : Nat} (h : AccIsCycleOf n L)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) (hrun : OddRun m j) :
    3 ^ j * (m + 1) ≤ 2 ^ j * (cycleMax n L + 1) := by
  obtain ⟨i, hi⟩ := hm
  have hreach : acceleratedOrbit j m = acceleratedOrbit (j + i) n := by
    rw [← hi, acceleratedOrbit_add]
  have hle : acceleratedOrbit j m ≤ cycleMax n L := by
    rw [hreach]; exact le_cycleMax h (j + i)
  have hval := oddRun_value j m hrun
  have hmono : 2 ^ j * (acceleratedOrbit j m + 1) ≤ 2 ^ j * (cycleMax n L + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **`M ≥ 2.25 m + 1.25`.**  The minimum always begins a run of length two, so
the greatest point of a cycle exceeds `9/4` of its least point — an improvement
on `CycleExtremes.two_mul_min_le_cycleMax`. -/
theorem nine_mul_min_le_four_mul_cycleMax {n L m : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    9 * (m + 1) ≤ 4 * (cycleMax n L + 1) := by
  have hrun := min_oddRun_two hn hm hmin hgt
  have hb := cycleMax_ge_of_run h hm hrun
  have h9 : (3:Nat) ^ 2 = 9 := by decide
  have h4 : (2:Nat) ^ 2 = 4 := by decide
  rw [h9, h4] at hb
  exact hb

/-- Restated without the shift: the greatest point exceeds twice the least by a
positive margin proportional to the least. -/
theorem cycleMax_gt_two_mul_min {n L m : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    2 * m + (m + 5) / 4 ≤ cycleMax n L := by
  have := nine_mul_min_le_four_mul_cycleMax hn h hm hmin hgt
  omega

/-- On the class `m ≡ 7 (mod 8)` the run has length three, and the constant rises
to `27/8`. -/
theorem cycleMax_ge_of_mod_eight {n L m : Nat}
    (h : AccIsCycleOf n L) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (h8 : m % 8 = 7) :
    27 * (m + 1) ≤ 8 * (cycleMax n L + 1) := by
  have hrun := run_three_of_mod_eight h8
  have hb := cycleMax_ge_of_run h hm hrun
  have h27 : (3:Nat) ^ 3 = 27 := by decide
  have h8' : (2:Nat) ^ 3 = 8 := by decide
  rw [h27, h8'] at hb
  exact hb

/-- The dichotomy, quantified: whichever class the minimum lies in, the cycle's
greatest point is at least `9/4` of it, and on one of the two classes at least
`27/8`. -/
theorem cycleMax_dichotomy {n L m : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    (m % 8 = 3 ∧ 9 * (m + 1) ≤ 4 * (cycleMax n L + 1)) ∨
    (m % 8 = 7 ∧ 27 * (m + 1) ≤ 8 * (cycleMax n L + 1)) := by
  have hfour : m % 4 = 3 := min_mod_four_via_runs hn hm hmin hgt
  rcases mod_eight_run_dichotomy (m := m) hfour with ⟨h3, _⟩ | ⟨h7, _⟩
  · exact Or.inl ⟨h3, nine_mul_min_le_four_mul_cycleMax hn h hm hmin hgt⟩
  · exact Or.inr ⟨h7, cycleMax_ge_of_mod_eight h hm h7⟩

/-! ## The same bound for any orbit minimum -/

/-- The closed form applies to a divergent orbit's minimum too: the value `j`
steps on is exactly `(3/2) ^ j` times the minimum, shifted. -/
theorem min_climb {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    4 * (acceleratedOrbit 2 m + 1) = 9 * (m + 1) := by
  have hrun := min_oddRun_two hn hm hmin hgt
  have hval := oddRun_value 2 m hrun
  have h9 : (3:Nat) ^ 2 = 9 := by decide
  have h4 : (2:Nat) ^ 2 = 4 := by decide
  rw [h9, h4] at hval
  exact hval

/-- So every counterexample's orbit rises to at least `9/4` of its minimum
within two steps, cyclic or divergent alike. -/
theorem min_climb_bound {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    2 * m + (m + 5) / 4 ≤ acceleratedOrbit 2 m := by
  have := min_climb hn hm hmin hgt
  omega

end RunValue
end Collatz
