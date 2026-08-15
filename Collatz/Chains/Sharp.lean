import Collatz.Chains.Arithmetic
import Collatz.Structure.CycleLengthSharp

/-!
# Chains 61–75: the sharpened cycle bound

`Collatz.Structure.CycleLengthSharp` improves the cycle-length exclusion from
`L ≤ 20` to `L ≤ 26`, and it does so by *chaining two lemmas that were proved
independently*:

* the verified range says the least point of a nontrivial cycle exceeds `60 000`;
* `CycleExtremes.two_mul_min_le_cycleMax` says the greatest point is at least
  twice the least.

Applying the verified range at the small end and the size bound at the large end
doubles the effective constant for free.  That is the one place in this project
where combining lemmas beat what either gave alone, and it is what the chain
programme is supposed to produce.

The chains below are the same targets as before, restated against the stronger
bound, plus the refutations it makes available.

| chain | hypothesis                                          | status    |
|-------|-----------------------------------------------------|-----------|
| 61    | cycle lengths capped at `26`                         | open      |
| 62    | some nontrivial cycle has length `≤ 26`              | **false** |
| 63    | every cycle meets `[1, 60000]`                       | open      |
| 64    | every cycle's greatest point is `≤ 120000`           | open      |
| 65    | some nontrivial cycle meets `[1, 60000]`             | **false** |
| 66    | every counterexample is `≤ 60000`                    | open      |
| 67    | the least counterexample is `≤ 60000`                | **false** |
| 68    | the surviving classes mod `1024` drop                | open      |
| 69    | every cycle's least point is `≤ 60000`               | open      |
| 70    | cycles are short or contain a multiple of three      | open      |
| 71    | every cycle's least point is a multiple of three     | open      |
| 72    | every cycle's least point avoids `1, 5 mod 6`        | open      |
| 73    | counterexamples closed under adding two              | open      |
| 74    | a short cycle with greatest point above `120000`     | **false** |
| 75    | the sharpest surviving combination                   | open      |
-/

namespace Collatz
namespace Chains

open Reach Strategy AccCycle AccDivergence CycleExtremes CycleLengthSharp

/-! ## Chains 61–62: the length cap -/

/-- Hypothesis: cycle lengths are capped at `26`. -/
def H61_lengthCap26 : Prop := ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L ≤ 26

/-- **Chain 61.**  A cap of `26` now suffices, where before it had to be `20`. -/
theorem chain61 (h1 : H14a_noAccDivergence) (h2 : H61_lengthCap26) :
    CollatzConjecture :=
  collatz_of_cycles_reach h1 (fun n L hn hc =>
    reachesOne_of_short_accCycle hn hc (h2 n L hn hc))

/-- Hypothesis: a short nontrivial cycle exists. -/
def H62_shortNontrivial : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ L ≤ 26 ∧ ¬ ReachesOne n

/-- **Chain 62 is refuted** by the sharpened bound. -/
theorem chain62_refuted : ¬ H62_shortNontrivial := by
  intro ⟨n, L, hn, hc, hL, hnr⟩
  exact hnr (reachesOne_of_short_accCycle hn hc hL)

/-! ## Chains 63–65: size targets against the extended range -/

/-- Hypothesis: every cycle meets the extended verified range. -/
def H63_cycleMeetsRange : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → n ≤ 60000

/-- **Chain 63.**  A size bound at `60 000` closes the cycle half. -/
theorem chain63 (h1 : H14a_noAccDivergence) (h2 : H63_cycleMeetsRange) :
    CollatzConjecture :=
  collatz_of_cycles_reach h1 (fun n L hn hc =>
    reachesOne_of_le_60000 hn (h2 n L hn hc))

/-- Hypothesis: the greatest point of every cycle is bounded. -/
def H64_maxBounded : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → cycleMax n L ≤ 120000

/-- **Chain 64.**  Bounding only the greatest point suffices, since the greatest
point of a nontrivial cycle must exceed `120 000`. -/
theorem chain64 (h1 : H14a_noAccDivergence) (h2 : H64_maxBounded) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    have hgt := cycleMax_gt hn hc hr
    have hle := h2 n L hn hc
    omega

/-- Hypothesis: some nontrivial cycle meets the verified range. -/
def H65_nontrivialSmall : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ n ≤ 60000 ∧ ¬ ReachesOne n

/-- **Chain 65 is refuted** by the extended verified range. -/
theorem chain65_refuted : ¬ H65_nontrivialSmall := by
  intro ⟨n, L, hn, hc, hle, hnr⟩
  exact hnr (reachesOne_of_le_60000 hn hle)

/-! ## Chains 66–68: counterexamples against the extended range -/

/-- A counterexample now exceeds `60 000`. -/
theorem counterexample_gt_60000 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) : 60000 < n := by
  by_cases hle : n ≤ 60000
  · exact absurd (reachesOne_of_le_60000 hn hle) h
  · omega

/-- Hypothesis: every counterexample lies in the extended verified range. -/
def H66_allSmall : Prop := ∀ n : Nat, 0 < n → ¬ ReachesOne n → n ≤ 60000

/-- **Chain 66.**  Nothing in the extended range is a counterexample. -/
theorem chain66 (h : H66_allSmall) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exact absurd (reachesOne_of_le_60000 hn (h n hn hr)) hr

/-- Hypothesis: the least counterexample is small. -/
def H67_leastSmall : Prop := ∃ n : Nat, Minimal.MinimalCounterexample n ∧ n ≤ 60000

/-- **Chain 67 is refuted** by the extended verified range. -/
theorem chain67_refuted : ¬ H67_leastSmall := by
  intro ⟨n, hmin, hle⟩
  exact Minimal.not_reachesOne_of_minimal hmin
    (reachesOne_of_le_60000 (Minimal.pos_of_minimal hmin) hle)

/-- Hypothesis: the surviving classes drop, above the extended range. -/
def H68_survivorsSharp : Prop :=
  ∀ n : Nat, 60000 < n → Congruence.survives 10 (n % 2 ^ 10) = true →
    ∃ k : Nat, acceleratedOrbit k n < n

/-- **Chain 68.**  The residue reduction with the sharper starting point. -/
theorem chain68 (h : H68_survivorsSharp) : CollatzConjecture := by
  refine collatz_of_survivors (K := 10) (by omega) (fun n hn hs => ?_)
  by_cases hbig : 60000 < n
  · exact h n hbig hs
  · -- everything below the extended range already drops, by the verifier
    exact Search.exists_lt_of_dropsWithin
      (Search.dropsWithin_of_allDrop check_drop_60000 (by omega) (by omega))

/-! ## Chains 69–72: the least point of a cycle -/

/-- Hypothesis: the least point of every cycle is small. -/
def H69_minSmall : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m ≤ 60000

/-- **Chain 69.**  Bounding the least point suffices. -/
theorem chain69 (h1 : H14a_noAccDivergence) (h2 : H69_minSmall) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  have hmpos : 0 < m := accCycleMin_pos hn ⟨i, hi⟩
  have hmreach : ReachesOne m := reachesOne_of_le_60000 hmpos (h2 n m hn ⟨i, hi⟩ hmin)
  exact (reachesOne_accOrbit_iff hn i).mpr (by rw [hi]; exact hmreach)

/-- Hypothesis: cycles are short, or contain a multiple of three. -/
def H70_shortOrThree : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    L ≤ 26 ∨ ∃ i : Nat, 3 ∣ acceleratedOrbit i n

/-- **Chain 70.**  Both alternatives are already closed: short cycles are
excluded, and no cycle point is divisible by three. -/
theorem chain70 (h1 : H14a_noAccDivergence) (h2 : H70_shortOrThree) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  rcases h2 n L hn hc with hshort | ⟨i, hi⟩
  · exact reachesOne_of_short_accCycle hn hc hshort
  · exact absurd hi (CycleModThree.not_three_dvd_orbit hn hc i)

/-- Hypothesis: the least point of every cycle is a multiple of three. -/
def H71_minThree : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → 3 ∣ m

/-- **Chain 71.**  No cycle point is a multiple of three. -/
theorem chain71 (h1 : H14a_noAccDivergence) (h2 : H71_minThree) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  have hmcyc : AccIsCycleOf m L := by
    rw [← hi]; exact accIsCycleOf_orbit hc i
  have hmpos : 0 < m := accCycleMin_pos hn ⟨i, hi⟩
  exact absurd (h2 n m L hn hmcyc ⟨i, hi⟩ hmin)
    (CycleModThree.not_three_dvd_of_accCycle hmpos hmcyc)

/-- Hypothesis: the least point of every cycle avoids the classes `1` and `5`
modulo `6`. -/
def H72_minAvoids : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 6 ≠ 1 ∧ m % 6 ≠ 5

/-- **Chain 72.**  The least point of a cycle is odd and not a multiple of
three, so it lies in exactly those two classes. -/
theorem chain72 (h1 : H14a_noAccDivergence) (h2 : H72_minAvoids) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  have hmcyc : AccIsCycleOf m L := by
    rw [← hi]; exact accIsCycleOf_orbit hc i
  have hsix := CycleModThree.cycleMin_mod_six hn ⟨i, hi⟩ hmin hmcyc
  have havoid := h2 n m L hn hmcyc ⟨i, hi⟩ hmin
  rcases hsix with h | h
  · exact absurd h havoid.1
  · exact absurd h havoid.2

/-! ## Chains 73–75 -/

/-- Hypothesis: counterexamples are closed under adding two. -/
def H73_addTwoClosed : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n → ¬ ReachesOne (n + 2)

/-- **Chain 73.**  Closure under adding two implies Collatz: doubling a
counterexample gives an even one, and the even numbers above it then include a
power of two. -/
theorem chain73 (h : H73_addTwoClosed) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    -- pass to an even counterexample
    have hev : ¬ ReachesOne (2 * n) := not_reachesOne_two_mul hr
    have hall : ∀ j : Nat, ¬ ReachesOne (2 * n + 2 * j) := by
      intro j
      induction j with
      | zero => simpa using hev
      | succ j ih =>
        have hpos : 0 < 2 * n + 2 * j := by omega
        have hstep := h (2 * n + 2 * j) hpos ih
        have hidx : 2 * n + 2 * j + 2 = 2 * n + 2 * (j + 1) := by omega
        rwa [hidx] at hstep
    -- a power of two above `2n` has the same parity
    have hge : 2 * n ≤ 2 ^ (2 * n) := Nat.le_of_lt (Arith.lt_two_pow_self (2 * n))
    have heven : (2:Nat) ^ (2 * n) % 2 = 0 := Arith.two_pow_even (by omega)
    have hidx : 2 * n + 2 * ((2 ^ (2 * n) - 2 * n) / 2) = 2 ^ (2 * n) := by omega
    exact hall ((2 ^ (2 * n) - 2 * n) / 2) (by rw [hidx]; exact reachesOne_two_pow _)

/-- Hypothesis: a short cycle with a large greatest point. -/
def H74_shortBigMax : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ L ≤ 26 ∧ 120000 < cycleMax n L

/-- **Chain 74 is refuted**: the size bound caps the greatest point of any cycle
of length at most `26` at `120 000`. -/
theorem chain74_refuted : ¬ H74_shortBigMax := by
  intro ⟨n, L, hn, hc, hL, hgt⟩
  have hmax := CycleLength.le_of_accCycle (cycleMax_pos hn hc) (accIsCycleOf_cycleMax hc)
    (CycleLength.lengthExcluded_of_all check_twentysix hL)
  omega

/-- **Chain 75.**  The sharpest surviving combination: no divergence, plus any
one of a length cap at `26`, a size bound at `60 000`, or a bound on the
greatest point at `120 000`. -/
theorem chain75 (h1 : H14a_noAccDivergence) :
    (H61_lengthCap26 → CollatzConjecture) ∧
    (H63_cycleMeetsRange → CollatzConjecture) ∧
    (H64_maxBounded → CollatzConjecture) :=
  ⟨chain61 h1, chain63 h1, chain64 h1⟩

end Chains
end Collatz
