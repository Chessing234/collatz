import Collatz.Chains.Arithmetic
import Collatz.Structure.CycleLengthSharp

/-!
# Chains 61–80: the sharpened bounds

`Collatz.Structure.CycleLengthSharp` improves the cycle-length exclusion from
`L ≤ 20` to `L ≤ 26`, by chaining lemmas rather than computing harder:

* the sieve settles `960` of every `1024` residue classes, so verification
  covers `102 400` integers while explicitly checking only about `6 400`;
* the least point of a nontrivial cycle therefore exceeds `102 400`, and
  `CycleExtremes.two_mul_min_le_cycleMax` doubles that at the greatest point;
* the size bound then clears every length up to `26`.

The chains below restate the cycle and counterexample targets against those
stronger constants, and add the refutations they make available.

| chain | hypothesis                                          | status    |
|-------|-----------------------------------------------------|-----------|
| 61    | cycle lengths capped at `26`                         | open      |
| 62    | some nontrivial cycle has length `≤ 26`              | **false** |
| 63    | every cycle point is below `102 400`                 | open      |
| 64    | every cycle's greatest point is `≤ 200 000`          | open      |
| 65    | some nontrivial cycle point is below `102 400`       | **false** |
| 66    | every counterexample is below `102 400`              | open      |
| 67    | the least counterexample is below `102 400`          | **false** |
| 68    | the surviving classes drop above `102 400`           | open      |
| 69    | every cycle's least point is below `102 400`         | open      |
| 70    | cycles are short or contain a multiple of three      | open      |
| 71    | every cycle's least point is a multiple of three     | open      |
| 72    | every cycle's least point avoids `1, 5 mod 6`        | open      |
| 73    | counterexamples closed under adding two              | open      |
| 74    | a short cycle with greatest point above `200 000`    | **false** |
| 75    | every orbit descends below `102 400`                 | open      |
| 76    | cycles are short or meet the verified range          | open      |
| 77    | counterexample residues fail the sieve               | open      |
| 78    | counterexamples go subcritical in time               | open      |
| 79    | counterexamples above the range go subcritical       | open      |
| 80    | the sharpest surviving combination                   | open      |
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

/-- Hypothesis: every cycle point lies below the verified range. -/
def H63_cycleInRange : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → n < 102400

/-- **Chain 63.**  A size bound at `102 400` closes the cycle half. -/
theorem chain63 (h1 : H14a_noAccDivergence) (h2 : H63_cycleInRange) :
    CollatzConjecture :=
  collatz_of_cycles_reach h1 (fun n L hn hc =>
    Search.reachesOne_of_lt_102400 hn (h2 n L hn hc))

/-- Hypothesis: the greatest point of every cycle is bounded. -/
def H64_maxBounded : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → cycleMax n L ≤ 200000

/-- **Chain 64.**  Bounding only the greatest point suffices, since the greatest
point of a nontrivial cycle is at least `204 800`. -/
theorem chain64 (h1 : H14a_noAccDivergence) (h2 : H64_maxBounded) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
    have hge := cycleMax_ge hn hc hr
    have hle := h2 n L hn hc
    omega

/-- Hypothesis: some nontrivial cycle meets the verified range. -/
def H65_nontrivialSmall : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ n < 102400 ∧ ¬ ReachesOne n

/-- **Chain 65 is refuted** by the extended verified range. -/
theorem chain65_refuted : ¬ H65_nontrivialSmall := by
  intro ⟨n, L, hn, hc, hlt, hnr⟩
  exact hnr (Search.reachesOne_of_lt_102400 hn hlt)

/-! ## Chains 66–68: counterexamples against the extended range -/

/-- Hypothesis: every counterexample lies below the verified range. -/
def H66_allSmall : Prop := ∀ n : Nat, 0 < n → ¬ ReachesOne n → n < 102400

/-- **Chain 66.**  Nothing below `102 400` is a counterexample. -/
theorem chain66 (h : H66_allSmall) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exact absurd (Search.reachesOne_of_lt_102400 hn (h n hn hr)) hr

/-- Hypothesis: the least counterexample is small. -/
def H67_leastSmall : Prop := ∃ n : Nat, Minimal.MinimalCounterexample n ∧ n < 102400

/-- **Chain 67 is refuted** by the extended verified range. -/
theorem chain67_refuted : ¬ H67_leastSmall := by
  intro ⟨n, hmin, hlt⟩
  exact Minimal.not_reachesOne_of_minimal hmin
    (Search.reachesOne_of_lt_102400 (Minimal.pos_of_minimal hmin) hlt)

/-- Hypothesis: the surviving classes drop, above the extended range. -/
def H68_survivorsSharp : Prop :=
  ∀ n : Nat, 102400 ≤ n → Congruence.survives 10 (n % 2 ^ 10) = true →
    ∃ k : Nat, acceleratedOrbit k n < n

/-- **Chain 68.**  The residue reduction, with the sharper starting point given
free by the sieve-accelerated verification. -/
theorem chain68 (h : H68_survivorsSharp) : CollatzConjecture := by
  refine Minimum.no_pos_counterexample_of_descent (P := ReachesOne) ?_
  intro n hn hnr
  have hge : 102400 ≤ n := Search.counterexample_ge_102400 hn hnr
  have hdrop : ∃ k : Nat, acceleratedOrbit k n < n := by
    by_cases hs : Congruence.survives 10 (n % 2 ^ 10) = true
    · exact h n hge hs
    · exact exists_drop_of_not_survives (by omega) (by omega) hs
  obtain ⟨k, hk⟩ := hdrop
  exact ⟨acceleratedOrbit k n, acceleratedOrbit_positive hn k, hk,
    fun hc => hnr (reachesOne_of_accOrbit hn hc)⟩

/-! ## Chains 69–72: the least point of a cycle -/

/-- Hypothesis: the least point of every cycle is small. -/
def H69_minSmall : Prop :=
  ∀ n m : Nat, 0 < n → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m < 102400

/-- **Chain 69.**  Bounding the least point suffices. -/
theorem chain69 (h1 : H14a_noAccDivergence) (h2 : H69_minSmall) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  have hmpos : 0 < m := accCycleMin_pos hn ⟨i, hi⟩
  have hmreach : ReachesOne m :=
    Search.reachesOne_of_lt_102400 hmpos (h2 n m hn ⟨i, hi⟩ hmin)
  exact (reachesOne_accOrbit_iff hn i).mpr (by rw [hi]; exact hmreach)

/-- Hypothesis: cycles are short, or contain a multiple of three. -/
def H70_shortOrThree : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    L ≤ 26 ∨ ∃ i : Nat, 3 ∣ acceleratedOrbit i n

/-- **Chain 70.**  Both alternatives are already closed. -/
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

/-- Hypothesis: the least point of every cycle avoids `1` and `5` modulo `6`. -/
def H72_minAvoids : Prop :=
  ∀ n m L : Nat, 0 < n → AccIsCycleOf m L → (∃ i : Nat, acceleratedOrbit i n = m) →
    (∀ j : Nat, m ≤ acceleratedOrbit j n) → m % 6 ≠ 1 ∧ m % 6 ≠ 5

/-- **Chain 72.**  The least point is odd and not a multiple of three, so it
lies in exactly those two classes. -/
theorem chain72 (h1 : H14a_noAccDivergence) (h2 : H72_minAvoids) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  have hmcyc : AccIsCycleOf m L := by
    rw [← hi]; exact accIsCycleOf_orbit hc i
  have hsix := CycleModThree.cycleMin_mod_six hn ⟨i, hi⟩ hmin hmcyc
  have havoid := h2 n m L hn hmcyc ⟨i, hi⟩ hmin
  rcases hsix with hcase | hcase
  · exact absurd hcase havoid.1
  · exact absurd hcase havoid.2

/-! ## Chains 73–75 -/

/-- Hypothesis: counterexamples are closed under adding two. -/
def H73_addTwoClosed : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n → ¬ ReachesOne (n + 2)

/-- **Chain 73.**  Closure under adding two implies Collatz. -/
theorem chain73 (h : H73_addTwoClosed) : CollatzConjecture := by
  intro n hn
  by_cases hr : ReachesOne n
  · exact hr
  · exfalso
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
    have hge : 2 * n ≤ 2 ^ (2 * n) := Nat.le_of_lt (Arith.lt_two_pow_self (2 * n))
    have heven : (2:Nat) ^ (2 * n) % 2 = 0 := Arith.two_pow_even (by omega)
    have hidx : 2 * n + 2 * ((2 ^ (2 * n) - 2 * n) / 2) = 2 ^ (2 * n) := by omega
    exact hall ((2 ^ (2 * n) - 2 * n) / 2) (by rw [hidx]; exact reachesOne_two_pow _)

/-- Hypothesis: a short cycle with a large greatest point. -/
def H74_shortBigMax : Prop :=
  ∃ n L : Nat, 0 < n ∧ AccIsCycleOf n L ∧ L ≤ 26 ∧ 200000 < cycleMax n L

/-- **Chain 74 is refuted**: the size bound caps the greatest point of any cycle
of length at most `26`. -/
theorem chain74_refuted : ¬ H74_shortBigMax := by
  intro ⟨n, L, hn, hc, hL, hgt⟩
  have hmax := CycleLength.le_of_accCycle (cycleMax_pos hn hc) (accIsCycleOf_cycleMax hc)
    (CycleLength.lengthExcluded_of_all check_twentysix hL)
  omega

/-- Hypothesis: every orbit descends below the verified range. -/
def H75_entersRange : Prop :=
  ∀ n : Nat, 0 < n → ∃ k : Nat, acceleratedOrbit k n < 102400

/-- **Chain 75.**  Entering the verified range closes the problem. -/
theorem chain75 (h : H75_entersRange) : CollatzConjecture := by
  intro n hn
  obtain ⟨k, hk⟩ := h n hn
  have hpos : 0 < acceleratedOrbit k n := acceleratedOrbit_positive hn k
  exact (reachesOne_accOrbit_iff hn k).mpr (Search.reachesOne_of_lt_102400 hpos hk)

/-! ## Chains 76–80: combining the closed routes -/

/-- Hypothesis: every cycle is short or meets the verified range. -/
def H76_shortOrSmall : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → L ≤ 26 ∨ n < 102400

/-- **Chain 76.**  A disjunction of two already-closed routes still closes the
cycle half, so only cycles that are *both* long and large remain. -/
theorem chain76 (h1 : H14a_noAccDivergence) (h2 : H76_shortOrSmall) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  rcases h2 n L hn hc with hshort | hsmall
  · exact reachesOne_of_short_accCycle hn hc hshort
  · exact Search.reachesOne_of_lt_102400 hn hsmall

/-- Hypothesis: every counterexample fails the sieve at level `10`. -/
def H77_sieveCatches : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n → Congruence.survives 10 (n % 2 ^ 10) = false

/-- **Chain 77.**  If the sieve catches every counterexample, there are none:
failing the sieve produces a drop, and the dropped value is a smaller
counterexample. -/
theorem chain77 (h : H77_sieveCatches) : CollatzConjecture := by
  refine Minimum.no_pos_counterexample_of_descent (P := ReachesOne) ?_
  intro n hn hnr
  have hge : 102400 ≤ n := Search.counterexample_ge_102400 hn hnr
  have hfail := h n hn hnr
  have hns : ¬ Congruence.survives 10 (n % 2 ^ 10) = true := by rw [hfail]; simp
  obtain ⟨k, hk⟩ := exists_drop_of_not_survives (by omega) (by omega) hns
  exact ⟨acceleratedOrbit k n, acceleratedOrbit_positive hn k, hk,
    fun hc => hnr (reachesOne_of_accOrbit hn hc)⟩

/-- Hypothesis: every counterexample goes subcritical in time. -/
def H78_counterexampleSubcritical : Prop :=
  ∀ n : Nat, 0 < n → ¬ ReachesOne n →
    ∃ k : Nat, 1 ≤ k ∧ 2 * oddCount n k < k ∧ 3 ^ k < n + 2 ^ k

/-- **Chain 78.**  The subcriticality condition is only needed for
counterexamples, not for every number — a genuine weakening of Chain 52. -/
theorem chain78 (h : H78_counterexampleSubcritical) : CollatzConjecture := by
  refine Minimum.no_pos_counterexample_of_descent (P := ReachesOne) ?_
  intro n hn hnr
  obtain ⟨k, hk, hhalf, hsize⟩ := h n hn hnr
  obtain ⟨b, heq, hb⟩ := AffineBound.exists_affine_bounded n k
  have hsub : 3 ^ oddCount n k < 2 ^ k := subcritical_of_half hhalf
  have hbn : b < n := by omega
  have hstep : (3 ^ oddCount n k + 1) * n ≤ 2 ^ k * n :=
    Nat.mul_le_mul_right n (by omega)
  have hexp : (3 ^ oddCount n k + 1) * n = 3 ^ oddCount n k * n + n := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hexp] at hstep
  have hlt : 2 ^ k * acceleratedOrbit k n < 2 ^ k * n := by omega
  have hdrop : acceleratedOrbit k n < n := Nat.lt_of_mul_lt_mul_left hlt
  exact ⟨acceleratedOrbit k n, acceleratedOrbit_positive hn k, hdrop,
    fun hc => hnr (reachesOne_of_accOrbit hn hc)⟩

/-- Hypothesis: counterexamples above the verified range go subcritical.  The
size hypothesis `768 000 ≤ n` comes free. -/
def H79_largeSubcritical : Prop :=
  ∀ n : Nat, 102400 ≤ n → ¬ ReachesOne n →
    ∃ k : Nat, 1 ≤ k ∧ 2 * oddCount n k < k ∧ 3 ^ k < n + 2 ^ k

/-- **Chain 79.**  The weakest form of the subcriticality target: it need only
be established for counterexamples beyond the verified range. -/
theorem chain79 (h : H79_largeSubcritical) : CollatzConjecture := by
  refine chain78 (fun n hn hnr => ?_)
  exact h n (Search.counterexample_ge_102400 hn hnr) hnr

/-- **Chain 80.**  The sharpest surviving combination.  Each of these closes the
problem on its own, and none is refuted. -/
theorem chain80 (h1 : H14a_noAccDivergence) :
    (H61_lengthCap26 → CollatzConjecture) ∧
    (H64_maxBounded → CollatzConjecture) ∧
    (H76_shortOrSmall → CollatzConjecture) ∧
    (H79_largeSubcritical → CollatzConjecture) ∧
    (H77_sieveCatches → CollatzConjecture) :=
  ⟨chain61 h1, chain64 h1, chain76 h1, chain79, chain77⟩

end Chains
end Collatz
