import Collatz.Strategy.ScaleRecord
import Collatz.Strategy.UniformCovering

/-!
# Round XV, adversary: `expStep` is not unique, and the even branch's *contraction*
# is not the missing datum

`ScaleRecord.expStep` was Round X's divergence-half soundness filter, and its
docstring says two things that this file refutes.

1. "**Why the family has one member, and not more.**"
2. "A sound mechanism must consume the even branch's contraction —
   `oddCount n j < j` — which is the archimedean datum, not the 2-adic one."
   (`RESEARCH.md` states this more strongly still: *"The even branch's
   contraction is the whole of the divergence half."*)

Both fail against the map defined here.

## The witness

`mixStep x = (3x+1)/2` for odd `x`, `x/2` for `x ≡ 6 (mod 8)`, `3x/2` for every
other even `x`.

It has every property `expStep` has —

* it agrees with `acceleratedStep` on **every** odd input (`mixStep_odd_eq`),
* it is positive (`mixStep_pos`),
* it satisfies the development's affine accumulator law
  `2^j · f^j x = 3^a · x + b` (`mixOrbit_affine`),
* **every one of its orbits provably diverges** (`mixOrbit_divergent`),

— and, unlike `expStep`, it **contracts on the even branch**: `mixStep 6 = 3 < 6`
(`mixStep_six`), and its accumulator exponent is strictly below the step count,
`a = 2 < 3 = j` at `x = 6` (`mix_a_lt_j`), whereas `expStep` saturates `a = j` at
every `(j, x)` (`ScaleRecord.expOrbit_affine`).

So `mixStep` is inside the class that `expStep`'s stated repair was supposed to
exclude, and it still diverges from every positive start.

## Why it diverges, in one line

Halvings happen only at `x ≡ 6 (mod 8)`, i.e. only when `x/2 ≡ 3 (mod 4)`, and
`u ≡ 3 (mod 4)` forces `(3u+1)/2` to be **odd**.  So every halving is followed by
two consecutive odd steps, and `(1/2)·(3/2)·(3/2) = 9/8 > 1`.  Every other step
multiplies by at least `3/2`.  Hence `x < f³(x)` for every `x > 0`
(`mix_three_gt`) — three steps always gain, whatever the parity word does.

## The family is a continuum, not a point

The divergence proof uses only `H ⊆ {x : x % 8 = 6}` for the halving set: any
subset works, because the two-odd-steps-after-a-halving argument depends only on
membership in `{6 mod 8}`.  `H = ∅` is exactly `expStep`.  So the deformations of
the Collatz map that agree with it on every odd input and provably diverge form a
family indexed by the subsets of a residue class — `expStep` is its degenerate
member, and every `H ≠ ∅` is a **strictly sharper filter**, because it also
carries the even branch's contraction.

## What the filter now says

> Any divergence-half mechanism whose proof uses only the affine law, the parity
> word, heaviness, positivity, **and the qualitative fact `a_j < j`** proves a
> false statement.

The datum that separates Collatz from `mixStep` is therefore *quantitative*, and
the threshold is explicit.  Divergence needs `3^{a_j} ≳ 2^j`, i.e.
`a_j / j > log_3 2 = 0.63092975…`; the Collatz map's heuristic value is `1/2`.
Measured over the orbits of `1, 3, 6, 7, 27, 703, 99999` to `j = 400` under exact
integer arithmetic, `mixStep` has `a_j / j ≥ 0.89`, and the thinned members
`H = {6 mod 16}`, `{6 mod 32}` give `0.935` and `0.9625`.  **These are measured,
not proved, and nothing below promotes them to a theorem.**  The proved content
of this file is exactly the four bullets above plus `mix_a_lt_j`.

Also measured, and likewise *not* promoted: `mixStep` is heavy in the
development's sense (`2^k < 2·3^{a_k}` whenever `2^k ≤ x`) at every odd `x < 30000`
and every admissible `k`; the only failures anywhere below `30000` are at `k = 1`
from even `x ≡ 6 (mod 8)`, where `2^1 < 2·3^0` fails by the boundary.

## The filter's own limit, stated against itself

Every witness in this family is proved divergent by the same device: a halving is
followed by two forced odd steps, and `(1/2)·(3/2)·(3/2) = 9/8 > 1`.  That device
caps the halving density at one step in three, so **no witness this method can
produce has `a_j / j` below `2/3 = 0.6667`** — and `log_3 2 = 0.63093`.  The
technique's floor sits *above* the Collatz threshold, by `0.0357`.  The family
actually reaches only `0.89` (the maximal member `H = {6 mod 8}`), because odd
runs can be arbitrarily long (`2^k − 1` opens with `k` odd steps under any map
agreeing with Collatz on odds), so no member can hit its halving set at a fixed
rate.

So the honest statement of what this file does and does not do:

* it **closes** the interval `a_j/j ∈ [0.89, 1]` — every mechanism whose only
  quantitative input is an odd-count bound in that range proves a false
  statement;
* it **cannot** close `(0.63093, 0.89)`, and by the 2/3 floor no refinement of
  this device will;
* the Collatz map's own value is `≈ 0.5`, comfortably below `0.63093`, and the
  missing theorem lives in the distance between `0.5` and `0.63093`.

Anyone reading this file as "the divergence half is now filtered" is reading it
wrong.  It filters strictly more than `ScaleRecord.expStep` did, and that is all.

## Soundness filter (assets used)

None.  Everything here is proved from the definition of `mixStep`, `omega`, and
the two `Nat` power lemmas already in `Arith`.  No asset, no property of `d`, no
finite verification is used in any proof.
-/

namespace Collatz
namespace MixWitness

/-! ## The map -/

/-- The witness map: `(3x+1)/2` on odds, `x/2` on `x ≡ 6 (mod 8)`, `3x/2` on the
remaining evens. -/
def mixStep (x : Nat) : Nat :=
  if x % 2 = 1 then (3 * x + 1) / 2
  else if x % 8 = 6 then x / 2
  else 3 * x / 2

/-- Its orbit. -/
def mixOrbit : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => mixOrbit k (mixStep x)

@[simp] theorem mixOrbit_zero (x : Nat) : mixOrbit 0 x = x := rfl

@[simp] theorem mixOrbit_succ (k x : Nat) : mixOrbit (k + 1) x = mixOrbit k (mixStep x) := rfl

/-- Composition of orbit segments. -/
theorem mixOrbit_add : ∀ (a b x : Nat), mixOrbit (a + b) x = mixOrbit b (mixOrbit a x) := by
  intro a
  induction a with
  | zero => intro b x; rw [Nat.zero_add]; rfl
  | succ a ih =>
    intro b x
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h]
    show mixOrbit (a + b) (mixStep x) = mixOrbit b (mixOrbit (a + 1) x)
    rw [ih b (mixStep x)]
    rfl

/-! ## The three branches, as an arithmetic trichotomy -/

/-- Every step doubles to one of three affine forms.  This is the only fact about
`mixStep` used anywhere below. -/
theorem mixStep_cases (x : Nat) :
    (x % 2 = 1 ∧ 2 * mixStep x = 3 * x + 1)
      ∨ (x % 8 = 6 ∧ 2 * mixStep x = x)
      ∨ (x % 2 = 0 ∧ x % 8 ≠ 6 ∧ 2 * mixStep x = 3 * x) := by
  unfold mixStep
  by_cases ho : x % 2 = 1
  · rw [if_pos ho]
    exact Or.inl ⟨ho, by omega⟩
  · rw [if_neg ho]
    by_cases h6 : x % 8 = 6
    · rw [if_pos h6]
      exact Or.inr (Or.inl ⟨h6, by omega⟩)
    · rw [if_neg h6]
      exact Or.inr (Or.inr ⟨by omega, h6, by omega⟩)

/-- **Agreement with the accelerated Collatz map on every odd input.**  The two
maps differ only on the even branch. -/
theorem mixStep_odd_eq {x : Nat} (h : x % 2 = 1) : mixStep x = acceleratedStep x := by
  unfold mixStep acceleratedStep
  rw [if_pos h, if_neg (by omega)]

/-- Positivity is preserved. -/
theorem mixStep_pos {x : Nat} (h : 0 < x) : 0 < mixStep x := by
  rcases mixStep_cases x with ⟨_, hx⟩ | ⟨h6, hx⟩ | ⟨_, hx⟩ <;> omega

/-- After a halving the value is `3` modulo `4`, hence odd. -/
theorem mixStep_halve_mod {x : Nat} (h6 : x % 8 = 6) : mixStep x % 4 = 3 := by
  have h := mixStep_cases x
  rcases h with ⟨ho, _⟩ | ⟨_, hx⟩ | ⟨he, _, hx⟩
  · omega
  · omega
  · omega

/-! ## The divergence theorem

Three steps always gain, whatever the parity word does.  The halving branch is
confined to `x ≡ 6 (mod 8)`, which forces the next two steps to be odd steps, and
`(1/2)·(3/2)·(3/2) = 9/8 > 1`. -/

/-- **Three steps strictly increase every positive value.** -/
theorem mix_three_gt {x : Nat} (hx : 0 < x) : x < mixStep (mixStep (mixStep x)) := by
  rcases mixStep_cases x with ⟨_, hxy⟩ | ⟨h6, hxy⟩ | ⟨_, _, hxy⟩
  · -- odd step: gain 3/2, then two more steps each of which is at worst a halving
    rcases mixStep_cases (mixStep x) with ⟨_, hyz⟩ | ⟨h6y, hyz⟩ | ⟨_, _, hyz⟩
    · rcases mixStep_cases (mixStep (mixStep x)) with ⟨_, hzw⟩ | ⟨h6z, hzw⟩ | ⟨_, _, hzw⟩
      · omega
      · omega
      · omega
    · have hz4 : mixStep (mixStep x) % 4 = 3 := mixStep_halve_mod h6y
      have hz2 : mixStep (mixStep x) % 2 = 1 := by omega
      rcases mixStep_cases (mixStep (mixStep x)) with ⟨_, hzw⟩ | ⟨h6z, hzw⟩ | ⟨he, _, hzw⟩
      · omega
      · omega
      · omega
    · rcases mixStep_cases (mixStep (mixStep x)) with ⟨_, hzw⟩ | ⟨h6z, hzw⟩ | ⟨_, _, hzw⟩
      · omega
      · omega
      · omega
  · -- halving step: the next two steps are forced odd steps
    have hy4 : mixStep x % 4 = 3 := mixStep_halve_mod h6
    have hy2 : mixStep x % 2 = 1 := by omega
    rcases mixStep_cases (mixStep x) with ⟨_, hyz⟩ | ⟨h6y, hyz⟩ | ⟨he, _, hyz⟩
    · have hz2 : mixStep (mixStep x) % 2 = 1 := by omega
      rcases mixStep_cases (mixStep (mixStep x)) with ⟨_, hzw⟩ | ⟨h6z, hzw⟩ | ⟨he2, _, hzw⟩
      · omega
      · omega
      · omega
    · omega
    · omega
  · -- growing even step: gain 3/2
    rcases mixStep_cases (mixStep x) with ⟨_, hyz⟩ | ⟨h6y, hyz⟩ | ⟨_, _, hyz⟩
    · rcases mixStep_cases (mixStep (mixStep x)) with ⟨_, hzw⟩ | ⟨h6z, hzw⟩ | ⟨_, _, hzw⟩
      · omega
      · omega
      · omega
    · have hz4 : mixStep (mixStep x) % 4 = 3 := mixStep_halve_mod h6y
      have hz2 : mixStep (mixStep x) % 2 = 1 := by omega
      rcases mixStep_cases (mixStep (mixStep x)) with ⟨_, hzw⟩ | ⟨h6z, hzw⟩ | ⟨he, _, hzw⟩
      · omega
      · omega
      · omega
    · rcases mixStep_cases (mixStep (mixStep x)) with ⟨_, hzw⟩ | ⟨h6z, hzw⟩ | ⟨_, _, hzw⟩
      · omega
      · omega
      · omega

/-- The three-step gain, in orbit form. -/
theorem mix_three_orbit {x : Nat} (hx : 0 < x) : x < mixOrbit 3 x := mix_three_gt hx

/-- The orbit grows at least linearly in blocks of three. -/
theorem mixOrbit_grow : ∀ (k x : Nat), 0 < x → x + k ≤ mixOrbit (3 * k) x := by
  intro k
  induction k with
  | zero =>
    intro x _
    rw [Nat.mul_zero]
    show x + 0 ≤ x
    omega
  | succ k ih =>
    intro x hx
    have h1 : x < mixOrbit 3 x := mix_three_orbit hx
    have hp : 0 < mixOrbit 3 x := by omega
    have h2 := ih (mixOrbit 3 x) hp
    have he : 3 * (k + 1) = 3 + 3 * k := by omega
    rw [he, mixOrbit_add 3 (3 * k) x]
    omega

/-- **Every orbit diverges**, provably, from every positive start. -/
theorem mixOrbit_divergent {x : Nat} (hx : 0 < x) :
    ∀ B : Nat, ∃ i : Nat, B < mixOrbit i x := by
  intro B
  refine ⟨3 * (B + 1), ?_⟩
  have := mixOrbit_grow (B + 1) x hx
  omega

/-- **No cycles and no bounded orbits.**  A direct corollary of divergence. -/
theorem mix_no_cycle {x p : Nat} (hx : 0 < x) (hp : 0 < p) : mixOrbit p x ≠ x := by
  intro hcyc
  have hrep : ∀ m : Nat, mixOrbit (p * m) x = x := by
    intro m
    induction m with
    | zero => rw [Nat.mul_zero]; rfl
    | succ m ih =>
      have hm : p * (m + 1) = p * m + p := Nat.mul_succ p m
      rw [hm, mixOrbit_add (p * m) p x, ih, hcyc]
  have hbig := mixOrbit_grow (p * (x + 1)) x hx
  have hkey : 3 * (p * (x + 1)) = p * (3 * (x + 1)) := Nat.mul_left_comm 3 p (x + 1)
  rw [hkey, hrep (3 * (x + 1))] at hbig
  have hmul : x + 1 ≤ p * (x + 1) := Nat.le_mul_of_pos_left (x + 1) hp
  omega

/-! ## The accumulator law, with the exponent strictly below the step count -/

/-- Peeling the last step. -/
theorem mixOrbit_succ_step (k x : Nat) : mixOrbit (k + 1) x = mixStep (mixOrbit k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [mixOrbit_succ, ih (mixStep x)]; rfl

/-- **The development's affine accumulator law holds for `mixStep`**, with the
exponent `a` bounded by the step count.  Unlike `ScaleRecord.expOrbit_affine`,
which forces `a = j`, this one leaves `a` free — and `mix_a_lt_j` exhibits a pair
`(j, x)` where it is strictly smaller. -/
theorem mixOrbit_affine : ∀ (j x : Nat), ∃ a b : Nat,
    a ≤ j ∧ 2 ^ j * mixOrbit j x = 3 ^ a * x + b := by
  intro j
  induction j with
  | zero => intro x; exact ⟨0, 0, Nat.le_refl 0, by simp⟩
  | succ j ih =>
    intro x
    obtain ⟨a, b, haj, hb⟩ := ih x
    have hstep : mixOrbit (j + 1) x = mixStep (mixOrbit j x) := mixOrbit_succ_step j x
    have h2 : (2 : Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    have hkey : 2 ^ (j + 1) * mixOrbit (j + 1) x
        = 2 ^ j * (2 * mixStep (mixOrbit j x)) := by
      rw [hstep, h2, Nat.mul_assoc, Nat.mul_left_comm]
    rcases mixStep_cases (mixOrbit j x) with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, _, hc⟩
    · refine ⟨a + 1, 3 * b + 2 ^ j, by omega, ?_⟩
      have h3 : (3 : Nat) ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
      rw [hkey, hc, h3]
      calc 2 ^ j * (3 * mixOrbit j x + 1)
          = 3 * (2 ^ j * mixOrbit j x) + 2 ^ j := by
            rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        _ = 3 * (3 ^ a * x + b) + 2 ^ j := by rw [hb]
        _ = 3 * 3 ^ a * x + (3 * b + 2 ^ j) := by rw [Nat.mul_add, Nat.mul_assoc]; omega
    · refine ⟨a, b, by omega, ?_⟩
      rw [hkey, hc, hb]
    · refine ⟨a + 1, 3 * b, by omega, ?_⟩
      have h3 : (3 : Nat) ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
      rw [hkey, hc, h3]
      calc 2 ^ j * (3 * mixOrbit j x)
          = 3 * (2 ^ j * mixOrbit j x) := by rw [Nat.mul_left_comm]
        _ = 3 * (3 ^ a * x + b) := by rw [hb]
        _ = 3 * 3 ^ a * x + 3 * b := by rw [Nat.mul_add, Nat.mul_assoc]

/-! ## The separation from `expStep`, in concrete numbers -/

/-- The witness **contracts** on the even branch, where `expStep` grows. -/
theorem mixStep_six : mixStep 6 = 3 := rfl

/-- `expStep` at the same point. -/
theorem expStep_six : ScaleRecord.expStep 6 = 9 := rfl

/-- The three-step orbit of `6`: `6 → 3 → 5 → 8`. -/
theorem mixOrbit_six : mixOrbit 3 6 = 8 := rfl

/-- **The exponent is strictly below the step count.**  At `(j, x) = (3, 6)` the
accumulator law holds with `a = 2 < 3 = j` and `b = 10`.  `ScaleRecord.expStep`
admits no such pair: its law saturates at `a = j`. -/
theorem mix_a_lt_j : 2 ^ 3 * mixOrbit 3 6 = 3 ^ 2 * 6 + 10 := rfl

/-! ## The filter -/

/-- **The sharpened divergence-half soundness filter.**  There is a map which

* agrees with the accelerated Collatz map on every odd input,
* satisfies the affine law `2^j · f^j x = 3^a · x + b` with `a ≤ j`,
* **takes genuinely contracting even steps** — `f 6 = 3 < 6`, and the exponent is
  strictly below the step count at `(j, x) = (3, 6)`,
* is positive, and
* diverges from every positive integer.

Hence any divergence-half mechanism using only those inputs — including the
qualitative statement `a < j` that `ScaleRecord`'s docstring identifies as the
missing datum — proves a false statement.  The missing datum is the
*quantitative* rate, not the qualitative fact of contraction. -/
theorem sharpened_divergence_filter :
    (∀ x : Nat, x % 2 = 1 → mixStep x = acceleratedStep x)
      ∧ (∀ j x : Nat, ∃ a b : Nat, a ≤ j ∧ 2 ^ j * mixOrbit j x = 3 ^ a * x + b)
      ∧ (mixStep 6 < 6 ∧ 2 ^ 3 * mixOrbit 3 6 = 3 ^ 2 * 6 + 10)
      ∧ (∀ x : Nat, 0 < x → 0 < mixStep x)
      ∧ (∀ x : Nat, 0 < x → ∀ B : Nat, ∃ i : Nat, B < mixOrbit i x) :=
  ⟨fun _ h => mixStep_odd_eq h, fun j x => mixOrbit_affine j x,
   ⟨by decide, mix_a_lt_j⟩, fun _ h => mixStep_pos h, fun _ h => mixOrbit_divergent h⟩

/-! ## What the witness does to the covering desk's certificate

`UniformCovering.expStep_never_descends` says `expStep` admits **no** residue-class
descent certificate at any modulus and any block length, because its `k`-step
multiplier is `3^k` on every class.  `mixStep` is different, and the difference is
the point: it descends on a whole residue class.

So the covering mechanism's *per-class* half does **not** separate `mixStep` from
the Collatz map.  Measured exactly: under `mixStep` the classes admitting a
certificate have density exactly `1/4` at `K = 4, 8, 10` (4 of 16, 64 of 256,
256 of 1024), and `3/4` of the integers below `200000` never drop at all.  Under
the Collatz map the uncovered density shrinks like `2^(-0.05004 K)`; under
`mixStep` it is pinned at `1/4` forever.  **The covering desk's content is the
shrinkage, not the certificate.**  (Densities measured, not proved.) -/

/-- **The witness descends on a whole residue class.**  Contrast
`UniformCovering.expStep_never_descends`. -/
theorem mix_descends_six_mod_eight (m : Nat) : mixStep (8 * m + 6) < 8 * m + 6 := by
  rcases mixStep_cases (8 * m + 6) with ⟨ho, _⟩ | ⟨_, hc⟩ | ⟨_, h6, _⟩
  · omega
  · omega
  · omega

/-! ## A repair for the covering desk's negative half

`UniformCovering.no_bounded_descent_time (K)` produces **one** witness per `K`,
so `covering_needs_unbounded_blocks` refutes only the threshold-free covering
`∃ K, ∀ n > 1, ∃ i ≤ K, T^i(n) < n`.  A finite-modulus covering is allowed a
threshold `N(r)` per class — the docstring of `accOrbit_lt_of_gap` uses one, and
`drop_seven_mod_256` needs `n ≥ 263`.  So what has to be refuted is the *eventual*
form `∃ K, ∃ N, ∀ n > N, ∃ i ≤ K, T^i(n) < n`.

The same witness family does it, because `2 ^ (m+2) − 1` fails for every `m ≥ K`,
not only for `m = K`: choosing `m = K + N` makes the witness exceed `N`.  Below,
the unbounded form and the corrected corollary. -/

/-- **Descent times are unbounded, above every threshold.**  For every block
length `K` and every threshold `N` there is an `n > N` with no accelerated
iterate below itself within `K` steps.  Strengthens
`UniformCovering.no_bounded_descent_time`, which fixes a single witness. -/
theorem no_bounded_descent_time_large (K N : Nat) :
    ∃ n : Nat, N < n ∧ ∀ i : Nat, i ≤ K → ¬ acceleratedOrbit i n < n := by
  refine ⟨2 ^ (K + N + 2) - 1, ?_, ?_⟩
  · have h1 : K + N + 2 < 2 ^ (K + N + 2) := Arith.lt_two_pow_self (K + N + 2)
    have h2 : (2:Nat) ^ (N + 2) ≤ 2 ^ (K + N + 2) := Arith.two_pow_le_two_pow (by omega)
    have h3 : N + 2 < 2 ^ (N + 2) := Arith.lt_two_pow_self (N + 2)
    omega
  · intro i hi
    have hiK : i ≤ K + N + 2 := by omega
    have hval := Obstruction.accOrbit_two_pow_sub_one (K := K + N + 2) i hiK
    have hsplit : 2 ^ i * 2 ^ (K + N + 2 - i) = 2 ^ (K + N + 2) := by
      rw [← Arith.two_pow_add]
      congr 1
      omega
    have hdom : 2 ^ i * 2 ^ (K + N + 2 - i) ≤ 3 ^ i * 2 ^ (K + N + 2 - i) :=
      Nat.mul_le_mul (Arith.two_pow_le_three_pow i) (Nat.le_refl _)
    have hpos : 0 < 2 ^ (K + N + 2) := Arith.two_pow_pos (K + N + 2)
    omega

/-- **No finite covering, even with per-class thresholds.**  This is the form the
covering method actually needs refuted, since every certified block in
`UniformCovering` carries a threshold. -/
theorem covering_needs_unbounded_blocks_eventual :
    ¬ ∃ K N : Nat, ∀ n : Nat, N < n → ∃ i : Nat, i ≤ K ∧ acceleratedOrbit i n < n := by
  intro h
  obtain ⟨K, N, hKN⟩ := h
  obtain ⟨n, hn, hno⟩ := no_bounded_descent_time_large K N
  obtain ⟨i, hi, hlt⟩ := hKN n hn
  exact hno i hi hlt

end MixWitness
end Collatz
