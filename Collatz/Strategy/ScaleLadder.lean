import Collatz.Strategy.AffineExact
import Collatz.Core.Pigeonhole

/-!
# The scale ladder — a divergence-half object

Every device in this development so far is indexed by the **parity word**, a
fixed-length object.  A parity word is a cycle-side coordinate: it has a length,
and a divergent orbit has none.  This file replaces it with a **scale-to-scale**
coordinate.

## The object

Fix a scale `k`.  Say the orbit of `n` has a *floor* at `2 ^ k` from index `i`
if `2 ^ k ≤ T^j(n)` for every `j ≥ i`.  A divergent orbit has a floor at every
scale (its values are unbounded, so it is below `2 ^ k` only finitely often),
and a **cycle has a floor at no scale above its own maximum**: this is the
first reason the object below is not a cycle detector.

The *rung* at scale `k` is the least index `e` at which the floor takes hold.
`exists_entry` produces it, and the rung is pinned:

* `entry_window` — the rung value lies in the **lower three quarters of the
  octave**: `2 ^ k ≤ T^e(n)` and `2 · T^e(n) < 3 · 2 ^ k`;
* `entry_odd` — the rung value is **odd**;
* `annulus_odd` — in fact *every* orbit value in `[2 ^ k, 2 ^ (k+1))` after the
  rung is odd, and
* `double_odd` — if the rung value is below `(4/3) · 2 ^ k` then its successor
  is odd too.

These are statements about the pair `(x mod 2, log₂ x)` — the fibre the closure
map calls "not a word invariant" — and they are consumed by no existing file.

## The renormalisation, and its exact error

The block between the rung at `k` and the rung at `k + 1` gives
`2 ^ ℓ · y' = 3 ^ a · y + C`.  `coupling_bound` is the sharp statement about
`C` on a floored block:

> `3 · 2 ^ k · C ≤ a · (2 ^ ℓ · y')`,

i.e. the additive datum contributes a relative error at most `a / (3 · 2 ^ k)`.
That is the coupling `r` of `Coupling.lean` measured across one scale, and it
**decays in the scale**.  Two consequences are proved: `block_upper`
(`3 ^ a < 3 · 2 ^ ℓ`, needing only `C ≥ 0`) and `block_lower`
(`(3m - 1) · 2 ^ (ℓ+2) < 9 · m · 3 ^ a` whenever `m · a ≤ 2 ^ k`), a uniform
two-sided window on the block multiplier that holds at *every* rung with no
averaging and no counting.

## The negative theorem

`no_finite_scale_invariant` is the round's kill.  Explicit orbit segments —
`climb`, the orbit of `2 ^ M - 1` — rise through arbitrarily many scales without
ever dropping.  So the scale-transition graph on **any finite alphabet** repeats
a state at two different scales, hence contains a cycle, hence an infinite
admissible path.  Acyclicity is unreachable, and well-foundedness with it: a
scale-based divergence proof must use an unbounded alphabet.
-/

namespace Collatz
namespace ScaleLadder

open Reach AffineExact

/-! ## Floors and rungs -/

/-- The orbit of `n` stays at or above `2 ^ k` from index `i` onwards. -/
def Floor (n i k : Nat) : Prop := ∀ j : Nat, i ≤ j → 2 ^ k ≤ acceleratedOrbit j n

/-- A floor at `i` is a floor at any later index. -/
theorem Floor.mono {n i i' k : Nat} (h : Floor n i k) (hle : i ≤ i') : Floor n i' k :=
  fun j hj => h j (Nat.le_trans hle hj)

/-- **Every value in the octave `[2^k, 2^(k+1))` above a floor is odd.**
An even one would halve to something below the floor. -/
theorem annulus_odd {n i k j : Nat} (hf : Floor n i k) (hij : i ≤ j)
    (hlt : acceleratedOrbit j n < 2 ^ (k + 1)) :
    acceleratedOrbit j n % 2 = 1 := by
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j n) with he | ho
  · exfalso
    have hstep : acceleratedOrbit (j + 1) n = acceleratedOrbit j n / 2 := by
      rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos he]
    have hge : 2 ^ k ≤ acceleratedOrbit (j + 1) n := hf (j + 1) (Nat.le_trans hij (by omega))
    rw [hstep] at hge
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ]; omega
    omega
  · exact ho

/-! ## The rung -/

/-- **Extraction of the rung.**  If the orbit is below `2 ^ k` at index `i` and
has a floor at `2 ^ k` from index `i + m`, then some index `e` in between is a
genuine *entry*: the floor holds from `e` and the orbit was below `2 ^ k` at
`e - 1`. -/
theorem exists_entry {n k : Nat} : ∀ m i : Nat,
    acceleratedOrbit i n < 2 ^ k → Floor n (i + m) k →
      ∃ e : Nat, i < e ∧ acceleratedOrbit (e - 1) n < 2 ^ k ∧ Floor n e k := by
  intro m
  induction m with
  | zero =>
    intro i hlow hf
    exact absurd (hf i (by omega)) (by omega)
  | succ m ih =>
    intro i hlow hf
    rcases Nat.lt_or_ge (acceleratedOrbit (i + m) n) (2 ^ k) with hb | hb
    · refine ⟨i + m + 1, by omega, ?_, ?_⟩
      · have : i + m + 1 - 1 = i + m := by omega
        rw [this]; exact hb
      · intro j hj; exact hf j (by omega)
    · refine ih i hlow ?_
      intro j hj
      rcases Nat.lt_or_ge j (i + m + 1) with h1 | h1
      · have : j = i + m := by omega
        rw [this]; exact hb
      · exact hf j h1

/-- **The rung window.**  The value at an entry lies in the lower three quarters
of its octave: the step into it is an odd step from below `2 ^ k`. -/
theorem entry_window {n e k : Nat} (hprev : acceleratedOrbit (e - 1) n < 2 ^ k)
    (he : 0 < e) (hge : 2 ^ k ≤ acceleratedOrbit e n) :
    2 * acceleratedOrbit e n < 3 * 2 ^ k := by
  have hE : e - 1 + 1 = e := by omega
  have hstep : acceleratedOrbit e n = acceleratedStep (acceleratedOrbit (e - 1) n) := by
    have h := acceleratedOrbit_succ_step (e - 1) n
    rw [hE] at h
    exact h
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit (e - 1) n) with hev | hod
  · exfalso
    rw [acceleratedStep, if_pos hev] at hstep
    omega
  · rw [acceleratedStep, if_neg (by omega)] at hstep
    have h2 : 2 * ((3 * acceleratedOrbit (e - 1) n + 1) / 2)
        = 3 * acceleratedOrbit (e - 1) n + 1 := by omega
    rw [hstep]
    omega

/-- **The rung value is odd.** -/
theorem entry_odd {n e k : Nat} (hf : Floor n e k)
    (hw : 2 * acceleratedOrbit e n < 3 * 2 ^ k) :
    acceleratedOrbit e n % 2 = 1 := by
  refine annulus_odd hf (Nat.le_refl e) ?_
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ k := Arith.two_pow_pos k
  omega

/-- **The rung's successor is odd too**, whenever the rung sits below
`(4/3) · 2 ^ k` — the successor then lands back inside the same octave. -/
theorem double_odd {n e k : Nat} (hf : Floor n e k)
    (hodd : acceleratedOrbit e n % 2 = 1)
    (hsmall : 3 * acceleratedOrbit e n + 1 < 2 * 2 ^ (k + 1)) :
    acceleratedOrbit (e + 1) n % 2 = 1 := by
  have hstep : acceleratedOrbit (e + 1) n = (3 * acceleratedOrbit e n + 1) / 2 := by
    rw [acceleratedOrbit_succ_step, acceleratedStep, if_neg (by omega)]
  refine annulus_odd hf (by omega : e ≤ e + 1) ?_
  rw [hstep]
  omega

/-! ## The coupling across one block -/

/-- **The additive datum is small above a floor.**  On a segment of `j` steps
all of whose values are at least `2 ^ k`, the accumulator obeys

`3 · 2 ^ k · C_j ≤ a_j · (2 ^ j · T^j x)`,

so the relative contribution of `C` is at most `a / (3 · 2 ^ k)`: the coupling
`r` decays in the scale.  This is the one estimate in the file that needs the
floor at *every* interior index, not just at the ends. -/
theorem coupling_bound {x k : Nat} : ∀ j : Nat,
    (∀ t : Nat, t ≤ j → 2 ^ k ≤ acceleratedOrbit t x) →
      3 * 2 ^ k * affineC j x ≤ oddCount x j * (2 ^ j * acceleratedOrbit j x) := by
  intro j
  induction j with
  | zero => intro _; simp [affineC]
  | succ j ih =>
    intro hf
    have ihx := ih (fun t ht => hf t (by omega))
    have hy : 2 ^ k ≤ acceleratedOrbit j x := hf j (by omega)
    have hlast := Density.oddCount_succ_last x j
    have hstep : acceleratedOrbit (j + 1) x = acceleratedStep (acceleratedOrbit j x) :=
      acceleratedOrbit_succ_step j x
    have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with hev | hod
    · have hC : affineC (j + 1) x = affineC j x := affineC_even hev
      have hval : acceleratedOrbit (j + 1) x = acceleratedOrbit j x / 2 := by
        rw [hstep, acceleratedStep, if_pos hev]
      have hcnt : oddCount x (j + 1) = oddCount x j := by omega
      have hkey : 2 ^ (j + 1) * acceleratedOrbit (j + 1) x = 2 ^ j * acceleratedOrbit j x := by
        have h2 : 2 * (acceleratedOrbit j x / 2) = acceleratedOrbit j x := by omega
        rw [hval, hp, Nat.mul_assoc, Nat.mul_left_comm, h2]
      rw [hC, hcnt, hkey]
      exact ihx
    · have hC : affineC (j + 1) x = 3 * affineC j x + 2 ^ j := affineC_odd hod
      have hval : acceleratedOrbit (j + 1) x = (3 * acceleratedOrbit j x + 1) / 2 := by
        rw [hstep, acceleratedStep, if_neg (by omega)]
      have hcnt : oddCount x (j + 1) = oddCount x j + 1 := by omega
      have hkey : 2 ^ (j + 1) * acceleratedOrbit (j + 1) x
          = 2 ^ j * (3 * acceleratedOrbit j x + 1) := by
        have h2 : 2 * ((3 * acceleratedOrbit j x + 1) / 2) = 3 * acceleratedOrbit j x + 1 := by
          omega
        rw [hval, hp, Nat.mul_assoc, Nat.mul_left_comm, h2]
      rw [hC, hcnt, hkey]
      -- goal: 3·2^k·(3C + 2^j) ≤ (a+1)·(2^j·(3y+1))
      have hpk : 2 ^ k ≤ acceleratedOrbit j x := hy
      have hmul : 2 ^ j * 2 ^ k ≤ 2 ^ j * acceleratedOrbit j x :=
        Nat.mul_le_mul_left _ hpk
      have hexp : 3 * (3 * 2 ^ k * affineC j x)
          ≤ 3 * (oddCount x j * (2 ^ j * acceleratedOrbit j x)) :=
        Nat.mul_le_mul_left 3 ihx
      have hslack : 3 * (2 ^ k * 2 ^ j) ≤ 3 * (2 ^ j * acceleratedOrbit j x) := by
        have : 2 ^ k * 2 ^ j = 2 ^ j * 2 ^ k := Nat.mul_comm _ _
        rw [this]
        exact Nat.mul_le_mul_left 3 hmul
      have hlhs : 3 * 2 ^ k * (3 * affineC j x + 2 ^ j)
          = 3 * (3 * 2 ^ k * affineC j x) + 3 * (2 ^ k * 2 ^ j) := by
        rw [Nat.mul_add]
        have h1 : 3 * 2 ^ k * (3 * affineC j x) = 3 * (3 * 2 ^ k * affineC j x) := by
          rw [Nat.mul_left_comm, Nat.mul_assoc]
        have h2 : 3 * 2 ^ k * 2 ^ j = 3 * (2 ^ k * 2 ^ j) := by rw [Nat.mul_assoc]
        rw [h1, h2]
      have hrhs : (oddCount x j + 1) * (2 ^ j * (3 * acceleratedOrbit j x + 1))
          = 3 * (oddCount x j * (2 ^ j * acceleratedOrbit j x))
            + (oddCount x j * 2 ^ j + (3 * (2 ^ j * acceleratedOrbit j x) + 2 ^ j)) := by
        have e1 : 2 ^ j * (3 * acceleratedOrbit j x + 1)
            = 3 * (2 ^ j * acceleratedOrbit j x) + 2 ^ j := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        rw [e1, Nat.add_mul, Nat.one_mul, Nat.mul_add]
        have e2 : oddCount x j * (3 * (2 ^ j * acceleratedOrbit j x))
            = 3 * (oddCount x j * (2 ^ j * acceleratedOrbit j x)) := by
          rw [Nat.mul_left_comm]
        rw [e2]
        omega
      rw [hlhs, hrhs]
      omega

/-! ## The block window -/

/-- **Upper half of the block window.**  From a rung at scale `k` to a rung at
scale `k + 1` in `ℓ` steps with `a` odd steps, `3 ^ a < 3 · 2 ^ ℓ`.  Only
`C ≥ 0` is used, so this half is unconditional. -/
theorem block_upper {y k l : Nat} (hy : 2 ^ k ≤ y)
    (hw' : 2 * acceleratedOrbit l y < 3 * 2 ^ (k + 1)) :
    3 ^ oddCount y l < 3 * 2 ^ l := by
  have haff := affine_exact y l
  have h1 : 3 ^ oddCount y l * 2 ^ k ≤ 2 ^ l * acceleratedOrbit l y := by
    have : 3 ^ oddCount y l * 2 ^ k ≤ 3 ^ oddCount y l * y := Nat.mul_le_mul_left _ hy
    omega
  have h2 : 2 * (3 ^ oddCount y l * 2 ^ k) < 3 * 2 ^ (k + 1) * 2 ^ l := by
    have hstep : 2 * (2 ^ l * acceleratedOrbit l y) < 3 * 2 ^ (k + 1) * 2 ^ l := by
      have := Nat.mul_lt_mul_of_pos_right hw' (Arith.two_pow_pos l)
      calc 2 * (2 ^ l * acceleratedOrbit l y)
          = 2 * acceleratedOrbit l y * 2 ^ l := by
            rw [Nat.mul_assoc, Nat.mul_comm (2 ^ l)]
        _ < 3 * 2 ^ (k + 1) * 2 ^ l := this
    omega
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [hk1] at h2
  have hpos : 0 < 2 ^ k := Arith.two_pow_pos k
  have h3 : 2 ^ k * (2 * 3 ^ oddCount y l) < 2 ^ k * (2 * (3 * 2 ^ l)) := by
    calc 2 ^ k * (2 * 3 ^ oddCount y l)
        = 2 * (3 ^ oddCount y l * 2 ^ k) := by
          rw [Nat.mul_left_comm, Nat.mul_comm (3 ^ oddCount y l)]
      _ < 3 * (2 * 2 ^ k) * 2 ^ l := h2
      _ = 2 ^ k * (2 * (3 * 2 ^ l)) := by
          rw [Nat.mul_comm 3 (2 * 2 ^ k), Nat.mul_assoc, Nat.mul_assoc,
            Nat.mul_left_comm 2 (2 ^ k)]
  have h4 := Nat.lt_of_mul_lt_mul_left h3
  omega

/-- **Lower half of the block window.**  With the floor holding throughout the
block and `m · a ≤ 2 ^ k` (the block's odd-step count small against the scale),
the multiplier is bounded below: `(3m - 1) · 2 ^ (ℓ+2) < 9 · m · 3 ^ a`.
At `m = 1` this reads `8 · 2 ^ ℓ < 9 · 3 ^ a`, and the bound tends to the sharp
`4 · 2 ^ ℓ < 3 · 3 ^ a` as `m` grows.  Unlike the upper half this needs the
coupling estimate: it is exactly where the archimedean datum is consumed. -/
theorem block_lower {y k l m' : Nat} (hy : 2 ^ k ≤ y) (hw : 2 * y < 3 * 2 ^ k)
    (hw2 : 2 ^ (k + 1) ≤ acceleratedOrbit l y)
    (hfl : ∀ t : Nat, t ≤ l → 2 ^ k ≤ acceleratedOrbit t y)
    (hma : (m' + 1) * oddCount y l ≤ 2 ^ k) :
    (3 * m' + 2) * 2 ^ (l + 2) < 9 * (m' + 1) * 3 ^ oddCount y l := by
  have haff := affine_exact y l
  have hcoup := coupling_bound (x := y) (k := k) l hfl
  -- abbreviations
  have hP : 0 < 2 ^ k := Arith.two_pow_pos k
  -- step 1 : 3·2^k·Y ≤ 3·2^k·(3^a·y) + a·Y
  have h1 : 3 * 2 ^ k * (2 ^ l * acceleratedOrbit l y)
      = 3 * 2 ^ k * (3 ^ oddCount y l * y) + 3 * 2 ^ k * affineC l y := by
    rw [haff, Nat.mul_add]
  have h2 : 3 * 2 ^ k * (2 ^ l * acceleratedOrbit l y)
      ≤ 3 * 2 ^ k * (3 ^ oddCount y l * y)
        + oddCount y l * (2 ^ l * acceleratedOrbit l y) := by
    omega
  -- step 2 : multiply by m'+1 and absorb the coupling term
  have h3 : (m' + 1) * (oddCount y l * (2 ^ l * acceleratedOrbit l y))
      ≤ 2 ^ k * (2 ^ l * acceleratedOrbit l y) := by
    have : (m' + 1) * oddCount y l * (2 ^ l * acceleratedOrbit l y)
        ≤ 2 ^ k * (2 ^ l * acceleratedOrbit l y) :=
      Nat.mul_le_mul_right _ hma
    rw [Nat.mul_assoc] at this
    exact this
  have h4 : (m' + 1) * (3 * 2 ^ k * (2 ^ l * acceleratedOrbit l y))
      ≤ (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * y))
        + 2 ^ k * (2 ^ l * acceleratedOrbit l y) := by
    have := Nat.mul_le_mul_left (m' + 1) h2
    rw [Nat.mul_add] at this
    omega
  -- rearrange the left side as (3m'+2)·(2^k·Y) + 2^k·Y
  have h5 : (m' + 1) * (3 * 2 ^ k * (2 ^ l * acceleratedOrbit l y))
      = (3 * m' + 2) * (2 ^ k * (2 ^ l * acceleratedOrbit l y))
        + 2 ^ k * (2 ^ l * acceleratedOrbit l y) := by
    have e : 3 * 2 ^ k * (2 ^ l * acceleratedOrbit l y)
        = 3 * (2 ^ k * (2 ^ l * acceleratedOrbit l y)) := by rw [Nat.mul_assoc]
    rw [e, ← Nat.mul_assoc]
    have : (m' + 1) * 3 = 3 * m' + 2 + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have h6 : (3 * m' + 2) * (2 ^ k * (2 ^ l * acceleratedOrbit l y))
      ≤ (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * y)) := by omega
  -- double, then use the two window bounds
  have h7 : (3 * m' + 2) * (2 ^ k * (2 ^ l * (2 * acceleratedOrbit l y)))
      ≤ (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * (2 * y))) := by
    have e1 : (3 * m' + 2) * (2 ^ k * (2 ^ l * (2 * acceleratedOrbit l y)))
        = 2 * ((3 * m' + 2) * (2 ^ k * (2 ^ l * acceleratedOrbit l y))) := by
      rw [Nat.mul_left_comm (2 ^ l) 2, Nat.mul_left_comm (2 ^ k) 2,
        Nat.mul_left_comm (3 * m' + 2) 2]
    have e2 : (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * (2 * y)))
        = 2 * ((m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * y))) := by
      rw [Nat.mul_left_comm (3 ^ oddCount y l) 2, Nat.mul_left_comm (3 * 2 ^ k) 2,
        Nat.mul_left_comm (m' + 1) 2]
    rw [e1, e2]
    exact Nat.mul_le_mul_left 2 h6
  -- lower bound the left side
  have h8 : 2 ^ (k + 2) ≤ 2 * acceleratedOrbit l y := by
    have e : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    omega
  have h9 : (3 * m' + 2) * (2 ^ k * (2 ^ l * 2 ^ (k + 2)))
      ≤ (3 * m' + 2) * (2 ^ k * (2 ^ l * (2 * acceleratedOrbit l y))) := by
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h8))
  -- upper bound the right side
  have h10 : 3 ^ oddCount y l * (2 * y) < 3 ^ oddCount y l * (3 * 2 ^ k) :=
    Nat.mul_lt_mul_of_pos_left hw (Arith.three_pow_pos _)
  have h11 : (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * (2 * y)))
      < (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * (3 * 2 ^ k))) := by
    have hpos : 0 < (m' + 1) * (3 * 2 ^ k) := by
      have := Arith.two_pow_pos k
      exact Nat.mul_pos (by omega) (by omega)
    have e1 : (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * (2 * y)))
        = (m' + 1) * (3 * 2 ^ k) * (3 ^ oddCount y l * (2 * y)) :=
      (Nat.mul_assoc _ _ _).symm
    have e2 : (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * (3 * 2 ^ k)))
        = (m' + 1) * (3 * 2 ^ k) * (3 ^ oddCount y l * (3 * 2 ^ k)) :=
      (Nat.mul_assoc _ _ _).symm
    rw [e1, e2]
    exact Nat.mul_lt_mul_of_pos_left h10 hpos
  -- assemble and cancel 2^k twice
  have h12 : (3 * m' + 2) * (2 ^ k * (2 ^ l * 2 ^ (k + 2)))
      < (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * (3 * 2 ^ k))) := by omega
  have e3 : (3 * m' + 2) * (2 ^ k * (2 ^ l * 2 ^ (k + 2)))
      = 2 ^ k * (2 ^ k * ((3 * m' + 2) * 2 ^ (l + 2))) := by
    have hk2 : 2 ^ (k + 2) = 2 ^ k * 2 ^ 2 := by rw [Nat.pow_add]
    have hl2 : 2 ^ (l + 2) = 2 ^ l * 2 ^ 2 := by rw [Nat.pow_add]
    rw [hk2, hl2]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have e4 : (m' + 1) * (3 * 2 ^ k * (3 ^ oddCount y l * (3 * 2 ^ k)))
      = 2 ^ k * (2 ^ k * (9 * (m' + 1) * 3 ^ oddCount y l)) := by
    have hx : 3 * (3 * 3 ^ oddCount y l) = 3 ^ oddCount y l * 9 := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_comm _ _
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, hx]
  rw [e3, e4] at h12
  have h13 := Nat.lt_of_mul_lt_mul_left h12
  exact Nat.lt_of_mul_lt_mul_left h13

/-! ## The negative theorem: no finite alphabet -/

/-- One accelerated step on the shape `2E - 1`. -/
theorem climb_step {E : Nat} (hE : 0 < E) : acceleratedStep (2 * E - 1) = 3 * E - 1 := by
  have hodd : (2 * E - 1) % 2 = 1 := by omega
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- **The climbing family.**  `T^j (2^j·E - 1) = 3^j·E - 1`: the orbit of a
number one below a large power of two rises by a factor `3/2` at every step,
for as many steps as there are factors of two. -/
theorem climb : ∀ j E : Nat, 0 < E → acceleratedOrbit j (2 ^ j * E - 1) = 3 ^ j * E - 1 := by
  intro j
  induction j with
  | zero => intro E _; simp
  | succ j ih =>
    intro E hE
    have hp : 2 ^ (j + 1) * E = 2 * (2 ^ j * E) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
    have hpos : 0 < 2 ^ j * E := Nat.mul_pos (Arith.two_pow_pos j) hE
    have hstep : acceleratedStep (2 ^ (j + 1) * E - 1) = 2 ^ j * (3 * E) - 1 := by
      rw [hp, climb_step hpos]
      have : 3 * (2 ^ j * E) = 2 ^ j * (3 * E) := by
        rw [Nat.mul_left_comm]
      rw [this]
    rw [acceleratedOrbit_succ, hstep, ih (3 * E) (by omega)]
    have hcomm : 3 ^ j * (3 * E) = 3 ^ (j + 1) * E := by
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]
      exact Nat.mul_left_comm _ _ _
    rw [hcomm]

/-- The climbing family read off the single start `2 ^ M - 1`. -/
theorem climb_val {M j : Nat} (hj : j ≤ M) :
    acceleratedOrbit j (2 ^ M - 1) = 3 ^ j * 2 ^ (M - j) - 1 := by
  have hsplit : 2 ^ j * 2 ^ (M - j) = 2 ^ M := by
    rw [← Nat.pow_add]
    have : j + (M - j) = M := by omega
    rw [this]
  have := climb j (2 ^ (M - j)) (Arith.two_pow_pos _)
  rw [hsplit] at this
  exact this

/-- The climb is monotone: each step multiplies by `3/2`. -/
theorem climb_mono {M : Nat} : ∀ j i : Nat, i ≤ j → j ≤ M →
    3 ^ i * 2 ^ (M - i) ≤ 3 ^ j * 2 ^ (M - j) := by
  intro j
  induction j with
  | zero =>
    intro i hi _
    have hz : i = 0 := by omega
    rw [hz]
    exact Nat.le_refl _
  | succ j ih =>
    intro i hi hj
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hstep : 3 ^ j * 2 ^ (M - j) ≤ 3 ^ (j + 1) * 2 ^ (M - (j + 1)) := by
        have hd : M - j = (M - (j + 1)) + 1 := by omega
        rw [hd, Nat.pow_succ 2, Nat.pow_succ 3]
        have e1 : 3 ^ j * (2 ^ (M - (j + 1)) * 2)
            = 2 * (3 ^ j * 2 ^ (M - (j + 1))) := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        have e2 : 3 ^ j * 3 * 2 ^ (M - (j + 1))
            = 3 * (3 ^ j * 2 ^ (M - (j + 1))) := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        rw [e1, e2]
        exact Nat.mul_le_mul_right _ (by omega)
      exact Nat.le_trans (ih i (by omega) (by omega)) hstep
    · have hij : i = j + 1 := by omega
      rw [hij]
      exact Nat.le_refl _

/-- Two steps of the climb gain at least one scale: `9 ≥ 8`. -/
theorem climb_scale {N s : Nat} (hs : 2 * s ≤ 2 * N) :
    2 ^ (2 * N + s) ≤ 3 ^ (2 * s) * 2 ^ (2 * N - 2 * s) := by
  have h9 : 3 ^ (2 * s) = 9 ^ s := by
    have hb : (3 : Nat) ^ 2 = 9 := by decide
    rw [Nat.pow_mul, hb]
  have h8 : 2 ^ (3 * s) = 8 ^ s := by
    have hb : (2 : Nat) ^ 3 = 8 := by decide
    rw [Nat.pow_mul, hb]
  have hle : (8 : Nat) ^ s ≤ 9 ^ s := Nat.pow_le_pow_left (by omega) s
  have hsum : 3 * s + (2 * N - 2 * s) = 2 * N + s := by omega
  have hexp : 2 ^ (2 * N + s) = 2 ^ (3 * s) * 2 ^ (2 * N - 2 * s) := by
    rw [← Nat.pow_add, hsum]
  rw [hexp, h9, h8]
  exact Nat.mul_le_mul_right _ hle

/-- **No finite alphabet suffices.**  Let `state k y` be *any* assignment of
fewer than `N` symbols to a scale together with the orbit value sitting on it.
Then there is a single orbit and two **different** scales `k₁ < k₂` on it,
joined by a segment that never falls below `2 ^ k₁`, carrying the *same* symbol.

So the scale-transition graph on a finite alphabet contains a repeated vertex,
hence a cycle, hence an infinite admissible path — no matter how the alphabet is
designed.  A scale-based divergence argument cannot be a finite-state argument;
its well-foundedness, if any, has to come from an unbounded coordinate. -/
theorem no_finite_scale_invariant (N : Nat) (hN : 0 < N) (state : Nat → Nat → Nat)
    (hb : ∀ k y : Nat, state k y < N) :
    ∃ k₁ k₂ j₁ j₂ : Nat,
      k₁ < k₂ ∧ j₁ < j₂ ∧
      2 ^ k₁ ≤ acceleratedOrbit j₁ (2 ^ (2 * N) - 1) ∧
      2 ^ k₂ ≤ acceleratedOrbit j₂ (2 ^ (2 * N) - 1) ∧
      (∀ j : Nat, j₁ ≤ j → j ≤ j₂ → 2 ^ k₁ ≤ acceleratedOrbit j (2 ^ (2 * N) - 1)) ∧
      state k₁ (acceleratedOrbit j₁ (2 ^ (2 * N) - 1))
        = state k₂ (acceleratedOrbit j₂ (2 ^ (2 * N) - 1)) := by
  -- the scale reached at step `j` of the climb
  have hfloor : ∀ s j : Nat, 2 * s ≤ j → j ≤ 2 * N →
      2 ^ (2 * N - 1 + s) ≤ acceleratedOrbit j (2 ^ (2 * N) - 1) := by
    intro s j hsj hjN
    have hsN : 2 * s ≤ 2 * N := by omega
    have hstep : 2 ^ (2 * N + s) ≤ 3 ^ (2 * s) * 2 ^ (2 * N - 2 * s) := climb_scale hsN
    have hmono : 3 ^ (2 * s) * 2 ^ (2 * N - 2 * s)
        ≤ 3 ^ j * 2 ^ (2 * N - j) := climb_mono (M := 2 * N) j (2 * s) hsj hjN
    have hv : acceleratedOrbit j (2 ^ (2 * N) - 1) = 3 ^ j * 2 ^ (2 * N - j) - 1 :=
      climb_val hjN
    have hdbl : 2 ^ (2 * N + s) = 2 * 2 ^ (2 * N - 1 + s) := by
      have he : 2 * N + s = (2 * N - 1 + s) + 1 := by omega
      rw [he, Nat.pow_succ]
      omega
    have hpos : 0 < 2 ^ (2 * N - 1 + s) := Arith.two_pow_pos _
    omega
  obtain ⟨s₁, s₂, hlt, hle, heq⟩ :=
    Pigeonhole.exists_repeat
      (f := fun s => state (2 * N - 1 + s) (acceleratedOrbit (2 * s) (2 ^ (2 * N) - 1)))
      (B := N) (N := N) (fun i _ => hb _ _) (Nat.le_refl N)
  refine ⟨2 * N - 1 + s₁, 2 * N - 1 + s₂, 2 * s₁, 2 * s₂, by omega, by omega, ?_, ?_, ?_, heq⟩
  · exact hfloor s₁ (2 * s₁) (Nat.le_refl _) (by omega)
  · exact hfloor s₂ (2 * s₂) (Nat.le_refl _) (by omega)
  · intro j hj1 hj2
    exact hfloor s₁ j hj1 (by omega)

end ScaleLadder
end Collatz
