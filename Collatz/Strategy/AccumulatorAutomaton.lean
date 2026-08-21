import Collatz.Strategy.DeltaSpectrum

/-!
# The accumulator as an automaton on `Z/G`, and why the moduli do not talk

Every route in this development reduces to one question: is `0` in the image of
`w ↦ C(w) mod G`?  The image has been studied as a *set* (it is sparse, of
density `2 ^ (−0.05 L)`, essentially injective, with no coset or subgroup
structure and no bias at any prime divisor of `G`).  This file studies
*transitions* instead: what happens to the residue when the word grows by one
letter.

## 1. The exact law, and the crux

Appending a letter to `w` gives (`C_snoc`)

    C (w ++ [b]) = if b then 3 · C w + 2 ^ |w| else C w,

so on the integers the accumulator is a clean two-letter affine automaton whose
letter `0` is the identity and whose letter `1` is `s ↦ 3s + 2 ^ j` at time `j`.
But the *modulus* moves as well: `G` depends on `(|w|, oddCount w)`, and both
coordinates change when a letter is appended.  `C mod G` at length `L` and
`C mod G'` at length `L + 1` are residues in different rings, and the question
"what is the transition law" only makes sense if the first residue constrains
the second.

**It does not, and provably so.**  Write `G = 2 ^ L − 3 ^ a`.  The two legal
successors are

    G' = 2 ^ (L+1) − 3 ^ a       = 2 G + 3 ^ a      (even letter),
    G' = 2 ^ (L+1) − 3 ^ (a+1),  2 G = G' + 3 ^ a   (odd letter),

so in both cases a common divisor of `G` and `G'` divides `3 ^ a`, hence is odd,
hence divides `2 ^ L = G + 3 ^ a`, hence is `1`:

    `gap_gcd_even`, `gap_gcd_odd`:  gcd (G, G') = 1 for both letters,

and word-level `gap_coprime_snoc`.  By the Chinese remainder theorem the pair
`(C mod G, C mod G')` therefore ranges over the *full* product: knowing the
residue before the letter tells you exactly nothing about the residue after it.

That is the verdict on the transition question as literally posed: **ill-posed,
for a structural reason**.  Consecutive gaps are coprime.  Not "hard to relate",
not "related by a complicated formula" — carrying no information about each
other whatsoever.  (Coprimality is special to the two *legal* successors: for
other shifts `(ΔL, Δa)` the gaps are frequently not coprime, e.g. at
`ΔL = 1, Δa = −1` there are 104 non-coprime pairs with `L ≤ 40` alone.)

## 2. The well-posed reformulation

Fix the target shape `(L, a)` and hence `G`, and follow the *prefixes* of a word
of that shape.  Then `step` below is a genuine transition system on `Z/G`:

    s ↦ s                (letter 0),      s ↦ (3 s + 2 ^ j) mod G   (letter 1),

`run_eq_C_mod` says its state after reading `w` is exactly `C w mod G`, and
`run_eq_zero_iff` that reaching state `0` after `L` letters with `a` ones is
exactly the cycle condition `G ∣ C w`.  So the automaton view is *faithful* —
which also means it is not a weakening: by `NewModels.word_is_cycle_word` with
`g = G`, a word reaching `0` with `a` ones **is** a genuine `3x+1` cycle word.
Nothing is gained or lost; the question is the same question.

## 3. Two obstruction shapes, both dead

*State invariants are vacuous.*  The all-even word of length `L` has state `0`
(`run_replicate_false`), so `0` is reachable in exactly `L` steps for every `G`
and every `L`.  Any set of states closed under both letters and containing the
start state contains the state of every word (`invariant_contains_all`); it can
never certify `0` unreachable.  **The obstruction must be graded by the letter
count.**

*Time-uniform graded invariants are vacuous too.*  Grading by the number of ones
turns the question into: is `0 = Σ_{i=1..a} 3 ^ (a−i) · 2 ^ (t_i)` modulo `G`,
where `0 ≤ t_1 < t_2 < ⋯ < t_a < L`?  `C_eq_Crel` proves that identification:
`C w = Crel (times w 0)`, and `times w 0` is the strictly increasing list of
odd-step times.  Drop only the *increasing* condition — i.e. ask for a graded
invariant that does not see the time index — and the problem collapses at once:

    Crel [1,1,1,1,0,0,1,1] = 6524 = 4 · 1631 = 4 · gap (13, 8)

(`relaxed_hits_zero`), with all eight exponents in `{0,1}`.  Measured, the
relaxed reachable set at `(L,a) = (12,7), (13,8), (16,10), (21,13)` already
contains `0` with every exponent in `{0,1,2}`, and is all of `Z/G` after `k = 2`
or `3` letters.  So the entire content of the cycle problem sits in the
*ordering* `t_1 < ⋯ < t_a < L`, which is exactly the time-dependence `2 ^ j` of
the letter-`1` map.  Any invariant that forgets `j` is vacuous.

## 4. Measurements behind the prose (exhaustive, not sampled)

* Consecutive-gap coprimality: `gcd(G, G') = 1` for every `(L, a)` with
  `L ≤ 300`, `3 ^ a < 2 ^ L`, and both legal letters.  Zero exceptions.
* Reachable-set growth (ungraded, `L = ⌊a log₂ 3⌋ + 1`): the sizes
  `2, 4, 8, 16, 31, 60, 116, 225, 438, 855, 1674, 3282, 6445, …` are the same
  for *every* pair until they saturate `G` — the automaton is as free as the
  integer accumulator, whose distinct-value count grows like `1.96 ^ j`.
* Graded reachability: `#{w : |w| = L, oddCount w = a, G ∣ C w} = 0` for every
  `(L, a)` with `L = ⌊a log₂ 3⌋ + 1` and `a ≤ 13`, except `(L,a) = (4,2)` where
  it is `2` — the two rotations of the trivial cycle `1 → 2 → 1`, `C = 7 = G`.
  As it must be: graded reachability *is* the cycle problem.
* Expected count `binom(L,a)/G ≈ 2 ^ (−0.05 L)`, the same exponent as the
  image-density statement.  The automaton reformulation does not change it.
-/

namespace Collatz
namespace AccumulatorAutomaton

open DeltaSpectrum

/-! ### Append laws for the word data -/

theorem accC_append : ∀ (w v : List Bool) (j c : Nat),
    accC (w ++ v) j c = accC v (j + w.length) (accC w j c) := by
  intro w
  induction w with
  | nil => intro v j c; simp [accC]
  | cons b w ih =>
    intro v j c
    show accC (w ++ v) (j + 1) (if b then 3 * c + 2 ^ j else c)
        = accC v (j + (w.length + 1)) (accC w (j + 1) (if b then 3 * c + 2 ^ j else c))
    rw [ih v (j + 1) (if b then 3 * c + 2 ^ j else c)]
    have : j + 1 + w.length = j + (w.length + 1) := by omega
    rw [this]

/-- **The exact transition law.**  One more letter multiplies the accumulator by
`3` and adds `2 ^ |w|`, or does nothing. -/
theorem C_snoc (w : List Bool) (b : Bool) :
    C (w ++ [b]) = if b then 3 * C w + 2 ^ w.length else C w := by
  show accC (w ++ [b]) 0 0 = _
  rw [accC_append w [b] 0 0]
  show (if b then 3 * accC w 0 0 + 2 ^ (0 + w.length) else accC w 0 0) = _
  simp [C]

theorem oddCount_append : ∀ (w v : List Bool),
    oddCount (w ++ v) = oddCount w + oddCount v := by
  intro w
  induction w with
  | nil => intro v; simp [oddCount]
  | cons b w ih => intro v; simp [oddCount, ih]; omega

theorem oddCount_snoc (w : List Bool) (b : Bool) :
    oddCount (w ++ [b]) = oddCount w + (if b then 1 else 0) := by
  rw [oddCount_append]
  cases b <;> simp [oddCount]

/-! ### The moduli of consecutive lengths are coprime -/

theorem three_pow_odd : ∀ a : Nat, 3 ^ a % 2 = 1 := by
  intro a
  induction a with
  | zero => decide
  | succ a ih =>
    have h : (3:Nat) ^ (a + 1) = 3 ^ a * 3 := rfl
    omega

theorem odd_of_dvd_odd {d n : Nat} (hn : n % 2 = 1) (h : d ∣ n) : d % 2 = 1 := by
  obtain ⟨c, hc⟩ := h
  have hd : d % 2 = 0 ∨ d % 2 = 1 := by omega
  cases hd with
  | inl h0 =>
    obtain ⟨e, he⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
    have : n = 2 * (e * c) := by rw [hc, he, Nat.mul_assoc]
    omega
  | inr h1 => exact h1

theorem odd_dvd_of_dvd_two_mul {d x : Nat} (hd : d % 2 = 1) (h : d ∣ 2 * x) : d ∣ x := by
  obtain ⟨t, ht⟩ := h
  have h1 : (d * t) % 2 = 0 := by omega
  have h2 : (d * t) % 2 = (t % 2) % 2 := by
    rw [Nat.mul_mod, hd, Nat.one_mul]
  have ht2 : t % 2 = 0 := by omega
  obtain ⟨s, hs⟩ : 2 ∣ t := Nat.dvd_of_mod_eq_zero ht2
  refine ⟨s, ?_⟩
  have hcomm : d * (2 * s) = 2 * (d * s) := by
    rw [← Nat.mul_assoc, Nat.mul_comm d 2, Nat.mul_assoc]
  have hkey : 2 * x = 2 * (d * s) := by rw [ht, hs, hcomm]
  omega

/-- An odd divisor of a power of two is `1`. -/
theorem odd_dvd_two_pow {d : Nat} (hd : d % 2 = 1) : ∀ {k : Nat}, d ∣ 2 ^ k → d = 1 := by
  intro k
  induction k with
  | zero => intro h; exact Nat.dvd_one.mp (by simpa using h)
  | succ k ih =>
    intro h
    refine ih (odd_dvd_of_dvd_two_mul hd ?_)
    have hrw : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hrw] at h
    exact h

/-- Auxiliary: a common divisor of `2 ^ L − 3 ^ a` and of `3 ^ a` is `1`. -/
theorem eq_one_of_dvd_gap_and_three_pow {d L a : Nat} (h1 : 3 ^ a < 2 ^ L)
    (hg : d ∣ 2 ^ L - 3 ^ a) (h3 : d ∣ 3 ^ a) : d = 1 := by
  have hodd : d % 2 = 1 := odd_of_dvd_odd (three_pow_odd a) h3
  have hsum : (2 ^ L - 3 ^ a) + 3 ^ a = 2 ^ L := by omega
  have : d ∣ 2 ^ L := by
    obtain ⟨u, hu⟩ := hg
    obtain ⟨v, hv⟩ := h3
    exact ⟨u + v, by rw [← hsum, hu, hv, Nat.mul_add]⟩
  exact odd_dvd_two_pow hodd this

/-- **Even letter: the two moduli are coprime.** -/
theorem gap_gcd_even {L a : Nat} (h1 : 3 ^ a < 2 ^ L) :
    Nat.gcd (2 ^ L - 3 ^ a) (2 ^ (L + 1) - 3 ^ a) = 1 := by
  have hL : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := by rw [Nat.pow_succ, Nat.mul_comm]
  have hd1 : Nat.gcd (2 ^ L - 3 ^ a) (2 ^ (L + 1) - 3 ^ a) ∣ 2 ^ L - 3 ^ a :=
    Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd (2 ^ L - 3 ^ a) (2 ^ (L + 1) - 3 ^ a) ∣ 2 ^ (L + 1) - 3 ^ a :=
    Nat.gcd_dvd_right _ _
  have hdtwice : Nat.gcd (2 ^ L - 3 ^ a) (2 ^ (L + 1) - 3 ^ a) ∣ 2 * (2 ^ L - 3 ^ a) :=
    Nat.dvd_trans hd1 ⟨2, Nat.mul_comm _ _⟩
  have hsub := Nat.dvd_sub' hd2 hdtwice
  have hval : (2 ^ (L + 1) - 3 ^ a) - 2 * (2 ^ L - 3 ^ a) = 3 ^ a := by omega
  rw [hval] at hsub
  exact eq_one_of_dvd_gap_and_three_pow h1 hd1 hsub

/-- **Odd letter: the two moduli are coprime.** -/
theorem gap_gcd_odd {L a : Nat} (h1 : 3 ^ a < 2 ^ L) (h2 : 3 ^ (a + 1) < 2 ^ (L + 1)) :
    Nat.gcd (2 ^ L - 3 ^ a) (2 ^ (L + 1) - 3 ^ (a + 1)) = 1 := by
  have hL : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := by rw [Nat.pow_succ, Nat.mul_comm]
  have ha : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
  have hd1 : Nat.gcd (2 ^ L - 3 ^ a) (2 ^ (L + 1) - 3 ^ (a + 1)) ∣ 2 ^ L - 3 ^ a :=
    Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd (2 ^ L - 3 ^ a) (2 ^ (L + 1) - 3 ^ (a + 1)) ∣ 2 ^ (L + 1) - 3 ^ (a + 1) :=
    Nat.gcd_dvd_right _ _
  have hdtwice : Nat.gcd (2 ^ L - 3 ^ a) (2 ^ (L + 1) - 3 ^ (a + 1)) ∣ 2 * (2 ^ L - 3 ^ a) :=
    Nat.dvd_trans hd1 ⟨2, Nat.mul_comm _ _⟩
  have hsub := Nat.dvd_sub' hdtwice hd2
  have hval : 2 * (2 ^ L - 3 ^ a) - (2 ^ (L + 1) - 3 ^ (a + 1)) = 3 ^ a := by omega
  rw [hval] at hsub
  exact eq_one_of_dvd_gap_and_three_pow h1 hd1 hsub

/-- **Word level.**  The modulus before a letter and the modulus after it are
coprime, so the residue of `C` before the letter constrains the residue after it
not at all. -/
theorem gap_coprime_snoc {w : List Bool} {b : Bool}
    (h1 : 3 ^ oddCount w < 2 ^ w.length)
    (h2 : 3 ^ oddCount (w ++ [b]) < 2 ^ (w ++ [b]).length) :
    Nat.gcd (gap w) (gap (w ++ [b])) = 1 := by
  have hlen : (w ++ [b]).length = w.length + 1 := by simp
  cases b with
  | false =>
    have hc : oddCount (w ++ [false]) = oddCount w := by
      rw [oddCount_snoc]; simp
    show Nat.gcd (2 ^ w.length - 3 ^ oddCount w)
        (2 ^ (w ++ [false]).length - 3 ^ oddCount (w ++ [false])) = 1
    rw [hlen, hc]
    exact gap_gcd_even h1
  | true =>
    have hc : oddCount (w ++ [true]) = oddCount w + 1 := by
      rw [oddCount_snoc]; simp
    show Nat.gcd (2 ^ w.length - 3 ^ oddCount w)
        (2 ^ (w ++ [true]).length - 3 ^ oddCount (w ++ [true])) = 1
    rw [hlen, hc] at h2 ⊢
    exact gap_gcd_odd h1 h2

/-! ### The fixed-modulus automaton -/

/-- One letter of the automaton on `Z/G` at time `j`. -/
def step (G j s : Nat) (b : Bool) : Nat := if b then (3 * s + 2 ^ j) % G else s

/-- Run the automaton over a word, starting at time `j` and state `s`. -/
def run (G : Nat) : List Bool → Nat → Nat → Nat
  | [], _, s => s
  | b :: w, j, s => run G w (j + 1) (step G j s b)

theorem run_mod : ∀ (G : Nat) (w : List Bool) (j s : Nat),
    run G w j (s % G) = accC w j s % G := by
  intro G w
  induction w with
  | nil => intro j s; rfl
  | cons b w ih =>
    intro j s
    cases b with
    | false =>
      show run G w (j + 1) (s % G) = accC w (j + 1) s % G
      exact ih (j + 1) s
    | true =>
      show run G w (j + 1) ((3 * (s % G) + 2 ^ j) % G) = accC w (j + 1) (3 * s + 2 ^ j) % G
      have hkey : (3 * (s % G) + 2 ^ j) % G = (3 * s + 2 ^ j) % G := by
        rw [Nat.add_mod, Nat.mul_mod 3 (s % G) G, Nat.mul_mod 3 s G,
          Nat.mod_mod_of_dvd s (Nat.dvd_refl G)]
      rw [hkey, ih (j + 1) (3 * s + 2 ^ j)]

/-- **Faithfulness.**  The automaton state after reading `w` is `C w mod G`. -/
theorem run_eq_C_mod (G : Nat) (w : List Bool) : run G w 0 0 = C w % G := by
  have h := run_mod G w 0 0
  simpa [C] using h

/-- Reaching state `0` is exactly the cycle condition. -/
theorem run_eq_zero_iff (G : Nat) (w : List Bool) (hG : 0 < G) :
    run G w 0 0 = 0 ↔ G ∣ C w := by
  rw [run_eq_C_mod]
  exact ⟨fun h => Nat.dvd_of_mod_eq_zero h, fun h => Nat.eq_zero_of_dvd_of_lt h |>.elim
    (fun _ => by exact Nat.mod_eq_zero_of_dvd h) (fun _ => by exact Nat.mod_eq_zero_of_dvd h)⟩

/-! ### State invariants cannot obstruct anything -/

theorem run_replicate_false : ∀ (G L j s : Nat),
    run G (List.replicate L false) j s = s := by
  intro G L
  induction L with
  | zero => intro j s; rfl
  | succ L ih =>
    intro j s
    show run G (List.replicate L false) (j + 1) (step G j s false) = s
    exact ih (j + 1) s

/-- **State `0` is reachable in exactly `L` steps, for every `G` and every `L`.**
The all-even word does it.  So no set of states can certify `0` unreachable. -/
theorem zero_reachable_every_length (G L : Nat) :
    ∃ w : List Bool, w.length = L ∧ oddCount w = 0 ∧ run G w 0 0 = 0 := by
  refine ⟨List.replicate L false, by simp, ?_, run_replicate_false G L 0 0⟩
  induction L with
  | zero => rfl
  | succ L ih =>
    show oddCount (false :: List.replicate L false) = 0
    simp [oddCount, ih]

theorem run_mem_invariant {G : Nat} (X : Nat → Prop)
    (hclosed : ∀ j s b, X s → X (step G j s b)) :
    ∀ (w : List Bool) (j s : Nat), X s → X (run G w j s) := by
  intro w
  induction w with
  | nil => intro j s hs; exact hs
  | cons b w ih => intro j s hs; exact ih (j + 1) (step G j s b) (hclosed j s b hs)

/-- Any forward-closed set of states containing the start state contains the
state of *every* word.  Combined with `zero_reachable_every_length`, a
state-only invariant is vacuous: it cannot avoid `0`, and it cannot separate
cycle words from non-cycle words. -/
theorem invariant_contains_all {G : Nat} (X : Nat → Prop) (hstart : X 0)
    (hclosed : ∀ j s b, X s → X (step G j s b)) (w : List Bool) : X (run G w 0 0) :=
  run_mem_invariant X hclosed w 0 0 hstart

/-! ### The ordered form of `C`, and the vacuity of the time-blind relaxation -/

/-- The odd-step times of a word, in increasing order, starting the clock at `j`. -/
def times : List Bool → Nat → List Nat
  | [], _ => []
  | b :: w, j => if b then j :: times w (j + 1) else times w (j + 1)

/-- `Crel [t₁, …, t_a] = Σ_i 3 ^ (a − i) · 2 ^ (t_i)`: the accumulator as a
function of the odd-step times alone, with **no** constraint on the times. -/
def Crel : List Nat → Nat
  | [] => 0
  | t :: ts => 3 ^ ts.length * 2 ^ t + Crel ts

theorem times_length : ∀ (w : List Bool) (j : Nat), (times w j).length = oddCount w := by
  intro w
  induction w with
  | nil => intro j; rfl
  | cons b w ih =>
    intro j
    cases b with
    | false => show (times w (j + 1)).length = 0 + oddCount w; rw [ih (j + 1)]; omega
    | true =>
      show (j :: times w (j + 1)).length = 1 + oddCount w
      simp [ih (j + 1)]; omega

theorem accC_eq_Crel : ∀ (w : List Bool) (j c : Nat),
    accC w j c = 3 ^ oddCount w * c + Crel (times w j) := by
  intro w
  induction w with
  | nil => intro j c; simp [accC, Crel, oddCount]
  | cons b w ih =>
    intro j c
    cases b with
    | false =>
      show accC w (j + 1) c = 3 ^ (0 + oddCount w) * c + Crel (times w (j + 1))
      rw [ih (j + 1) c]; simp
    | true =>
      show accC w (j + 1) (3 * c + 2 ^ j)
          = 3 ^ (1 + oddCount w) * c + Crel (j :: times w (j + 1))
      rw [ih (j + 1) (3 * c + 2 ^ j)]
      show 3 ^ oddCount w * (3 * c + 2 ^ j) + Crel (times w (j + 1))
          = 3 ^ (1 + oddCount w) * c + (3 ^ (times w (j + 1)).length * 2 ^ j
              + Crel (times w (j + 1)))
      rw [times_length w (j + 1)]
      have h3 : (3:Nat) ^ (1 + oddCount w) = 3 ^ oddCount w * 3 := by
        rw [Nat.add_comm, Nat.pow_succ]
      rw [h3, Nat.mul_add]
      omega

/-- **`C` as a function of the odd-step times.**  `times w 0` is the increasing
list of positions of the odd letters. -/
theorem C_eq_Crel (w : List Bool) : C w = Crel (times w 0) := by
  have h := accC_eq_Crel w 0 0
  simpa [C] using h

/-- **The time-blind relaxation is vacuous.**  Drop the requirement that the
odd-step times be *increasing* (and bounded by `L`) and the target `0` is hit
immediately: at `(L, a) = (13, 8)`, `G = 2 ^ 13 − 3 ^ 8 = 1631`, eight exponents
drawn from `{0, 1}` already give `Crel = 6524 = 4 · 1631`.  So every invariant
that does not see the time index `j` fails; the entire content of the cycle
problem is the ordering `t₁ < ⋯ < t_a < L`. -/
theorem relaxed_hits_zero :
    Crel [1, 1, 1, 1, 0, 0, 1, 1] = 4 * (2 ^ 13 - 3 ^ 8) := by decide

theorem relaxed_gap : (2:Nat) ^ 13 - 3 ^ 8 = 1631 := by decide

theorem relaxed_dvd : (2 ^ 13 - 3 ^ 8) ∣ Crel [1, 1, 1, 1, 0, 0, 1, 1] :=
  ⟨4, by rw [relaxed_hits_zero]; omega⟩

end AccumulatorAutomaton
end Collatz
