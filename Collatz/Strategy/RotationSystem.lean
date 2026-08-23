import Collatz.Strategy.CycleCode
import Collatz.Strategy.AccumulatorCap

/-!
# The conjugation identity, the rotation recurrence, and the collapse of the
# rotation system

Round XIV, sections 46–49.  The question was whether **cyclicity used globally**
— imposing the integrality condition at all `L` rotations of a cycle word at once
— is stronger than imposing it at one.  The answer proved here is **no**, and the
proof is a single exact identity valid for every word and every factorization,
with no cycle hypothesis anywhere.

## 1. The exact `C(uv)` ↔ `C(vu)` identity

For any two words `u, v`, with `L = |u| + |v|` and `a = ones u + ones v`,

    `2 ^ |v| · wC (u ++ v)  +  3 ^ a · wC v  =  3 ^ (ones v) · wC (v ++ u)  +  2 ^ L · wC v`

(`wC_swap`).  Over `ℤ` this reads

    **`2 ^ |v| · C(uv)  −  3 ^ (ones v) · C(vu)  =  G · C(v)`,   `G = 2 ^ L − 3 ^ a`.**

Two words conjugate in the free monoid have accumulators that agree after the
covariance twist `2 ^ |v| / 3 ^ (ones v)`, and the **entire defect is `G` times
the accumulator of the transposed block** — not of the whole word, not of a
minimum, but of `v` alone.  The brief asked whether the difference "contains
exactly the minimum point information".  It does not: it contains `G · wC v`.
What is true is the weaker statement recovered in §4 — since `wC v` runs over the
prefix accumulators as `v` runs over the prefixes, and the cycle points are
`C_r / G`, the identity divided by `G` is exactly `affine_exact` for the orbit.
The minimum is recoverable from the family, but no single conjugation isolates it.

This identity strictly generalises the two rotation identities already in the
repository: `CycleCode.wC_rot_zero` is the case `v = [0]` and `CycleCode.wC_rot_one`
is the case `v = [1]`.  Both are re-derived below as one-line corollaries
(`rot_zero_of_swap`, `rot_one_of_swap`) to certify that no new mechanism has been
introduced.

## 2. The rotation recurrence

Write `C_r = wC (ρ ^ r w)` for the rotations of a fixed word.  The one-step
recurrence (`wC_rot_step`) is

    **`2 · C_{r+1} = 3 ^ (b_r) · C_r + b_r · G`,     `b_r = w_r ∈ {0,1}`,**

i.e. `C_{r+1} = C_r / 2` after an even letter and `C_{r+1} = (3 C_r + G) / 2`
after an odd one.  So the `L` accumulators are **not** `L` independent numbers:
they are the orbit of `C_0` under the *same* accelerated map, with the gap `G` in
place of the offset `d`.  Rotating the word is running the map on the
accumulator.  The closed form (`wC_rot_closed`) is

    **`2 ^ r · C_r = 3 ^ (ones (take r w)) · C_0 + G · wC (take r w)`,**

the word-level twin of `AccumulatorCap.affineC_shift_gap` — same shape, but with
no cycle hypothesis and no orbit.

## 3. The rotation system collapses (the round's assigned question, answered)

Because `2 ^ r` and `3 ^ k` are both invertible modulo any `g ∣ G` (`g` is odd
since `G` is, and `3 ∤ g` since `3 ∤ 2 ^ L`), the closed form gives an honest
**iff**:

    **`g ∣ C_0  ↔  g ∣ C_r`   for every `r`   (`rot_dvd_iff`, `rot_dvd_iff_take`).**

Imposing the integrality condition at all `L` rotations is *exactly* imposing it
at one.  The system is not overdetermined; it carries one bit, not `L`.  This
closes the branch.  `Rotation.lean` asserted this in prose from
`AccumulatorCap.dvd_affineC_shift`, which needs `AccIsCycleOf`; the version here
is purely combinatorial — it holds for every word of every shape, cycle or not,
and in both directions.

Independent exhaustive check (exact integer arithmetic, not floats): for every
word of every length `L ≤ 14` with `2 ^ L ≠ 3 ^ a`, and every divisor `g` of
`|G|` — `156656` (word, divisor) pairs — the set `{ r : g ∣ C_r }` was either
empty or all of `[0, L)`.  No exceptions.  COMPUTATIONAL.

## 4. The minimum, and why the prefix cap is vacuous there

Dividing the closed form by `G` on a genuine cycle (`G · x_r = d · C_r`) gives
`2 ^ r · x_r = 3 ^ (a_r) · x_0 + d · wC (take r w)`.  Minimality of `x_0` among
the cycle points is therefore *equivalent* to the prefix system

    `(2 ^ r − 3 ^ (a_r)) · x_0  ≤  d · wC (take r w)`  for all `r < L`.

Call a rotation **fully heavy** when `2 ^ r ≤ 3 ^ (a_r)` at every proper prefix.
`heavy_rot_min` proves: *a fully heavy rotation has the smallest accumulator of
all rotations* — because then every left side above is `≤ 0`.  LEAN_PROVED.

The negative half is the point.  Measured over every genuine cycle available
(`3x−1` at `17` and `5`; `3x+5` at `5, 19, 23, 187, 347`; `3x+7` at `5`; `3x+13`
at `131`; `3x+59` at `133` and `229`; `3x+1` at `1`): in **every** case the
minimum rotation is fully heavy, so **it has no light proper prefix at all**, and
every inequality of the system is `≤ 0 ≤ something`.  The prefix cap on `x_min`
that one hopes to compare with `Bcap` therefore has *no instances* at the
minimum.  Any light prefix that does exist belongs to some other rotation `s`,
and there the inequality runs the wrong way: it bounds `x_s` from **below**, not
`x_min` from above.  So there is no route from rotation data to a `Bcap`-style
ceiling on `x_min`; the cap and the rotation system meet only at `r = L`, where
the cap reads `x_0 = d · C_0 / G` and is a definition.  COMPUTATIONAL + the above
proof.

Two further exhaustive facts, both COMPUTATIONAL (`L ≤ 18`, exact arithmetic):

* the number of fully heavy rotations of a word with `2 ^ L > 3 ^ a` is always
  `0` or `1`, never more — a cycle-lemma statement, and the word-level reason a
  cycle has a *unique* minimum, with no arithmetic used;
* whenever a fully heavy rotation exists it is exactly the unique `argmin_r C_r`
  (`29188 / 29188` words).  This completes Round XIII's observation, which had
  tested `a = 8, 20, 50, 200, 1000` only: heaviness is minimality, and the
  converse holds too.  Only the forward direction is proved below.

## Soundness and scope

Everything here is an identity between `wC` values of finite words; nothing uses
positivity of `d`, a cycle hypothesis, or a measurement.  By
`DenominatorScalar`, `wC (w, d) = d · wC (w, 1)`, so every statement is `d`-free
and cannot distinguish `d = 1` from `d = 5` — as the collapse in §3 makes
unavoidable.  Nothing in this file bears on `δ(w) > 1`, which is the cycle half of
Collatz restated (`CLOSURE.md:203`) and is not attacked here.
-/

namespace Collatz
namespace RotationSystem

open RepetitionDescent

/-! ## 1. The conjugation identity -/

/-- **The exact `C(uv)` ↔ `C(vu)` identity.**  Over `ℤ` this is
`2 ^ |v| · C(uv) − 3 ^ (ones v) · C(vu) = G · C(v)` with `G = 2 ^ L − 3 ^ a`;
stated additively so it holds in `Nat` whatever the sign of the gap. -/
theorem wC_swap (u v : List Nat) :
    2 ^ v.length * wC (u ++ v) + 3 ^ (ones u + ones v) * wC v
      = 3 ^ ones v * wC (v ++ u) + 2 ^ (u.length + v.length) * wC v := by
  rw [wC_append u v, wC_append v u]
  have h3 : (3:Nat) ^ (ones u + ones v) = 3 ^ ones v * 3 ^ ones u := by
    rw [Nat.pow_add, Nat.mul_comm]
  have h2 : (2:Nat) ^ (u.length + v.length) = 2 ^ v.length * 2 ^ u.length := by
    rw [Nat.pow_add, Nat.mul_comm]
  rw [h3, h2, Nat.mul_add, Nat.mul_add]
  generalize (3:Nat) ^ ones v = A
  generalize (3:Nat) ^ ones u = B
  generalize (2:Nat) ^ v.length = P
  generalize (2:Nat) ^ u.length = Q
  generalize wC u = X
  generalize wC v = Y
  have e1 : P * (A * X) = A * (P * X) := by
    rw [Nat.mul_left_comm]
  have e2 : P * (Q * Y) = P * Q * Y := by rw [Nat.mul_assoc]
  have e3 : A * B * Y = A * (B * Y) := by rw [Nat.mul_assoc]
  omega

/-- The same identity in gap form: when the word is light (`3 ^ a ≤ 2 ^ L`) the
defect is exactly `G · wC v`. -/
theorem wC_swap_gap {u v : List Nat} {G : Nat}
    (hG : G + 3 ^ (ones u + ones v) = 2 ^ (u.length + v.length)) :
    2 ^ v.length * wC (u ++ v) = 3 ^ ones v * wC (v ++ u) + G * wC v := by
  have h := wC_swap u v
  have hexp : 2 ^ (u.length + v.length) * wC v
      = G * wC v + 3 ^ (ones u + ones v) * wC v := by
    rw [← hG, Nat.add_mul]
  omega

/-! ### The two existing rotation identities are the cases `v = [0]`, `v = [1]` -/

/-- `CycleCode.wC_rot_zero` recovered from `wC_swap`. -/
theorem rot_zero_of_swap (t : List Nat) : wC (0 :: t) = 2 * wC (t ++ [0]) := by
  have h := wC_swap t [0]
  have hl : ([0] : List Nat).length = 1 := rfl
  have ho : ones ([0] : List Nat) = 0 := rfl
  have hw : wC ([0] : List Nat) = 0 := by decide
  rw [hl, ho, hw] at h
  have hcons : ([0] : List Nat) ++ t = 0 :: t := rfl
  rw [hcons] at h
  simpa using h.symm

/-- `CycleCode.wC_rot_one` recovered from `wC_swap`. -/
theorem rot_one_of_swap (t : List Nat) :
    2 * wC (t ++ [1]) + 3 ^ ones (1 :: t) = 3 * wC (1 :: t) + 2 ^ (1 :: t).length := by
  have h := wC_swap t [1]
  have hl : ([1] : List Nat).length = 1 := rfl
  have ho : ones ([1] : List Nat) = 1 := rfl
  have hw : wC ([1] : List Nat) = 1 := by decide
  rw [hl, ho, hw] at h
  have hcons : ([1] : List Nat) ++ t = 1 :: t := rfl
  rw [hcons] at h
  have hones : ones (1 :: t) = ones t + 1 := by
    rw [ones_cons]; simp [Nat.add_comm]
  have hlen : (1 :: t).length = t.length + 1 := by simp
  rw [hones, hlen]
  have hp3 : (3:Nat) ^ (ones t + 1) = 3 ^ (ones t) * 3 := by rw [Nat.pow_succ]
  have hp2 : (2:Nat) ^ (t.length + 1) = 2 ^ t.length * 2 := by rw [Nat.pow_succ]
  rw [hp3, hp2]
  simpa [Nat.pow_succ, Nat.mul_comm] using h

/-! ## 2. The rotation recurrence -/

/-- **The one-step rotation recurrence, even letter.**  `2 · C_{r+1} = C_r`. -/
theorem wC_rot_step_zero (t : List Nat) : 2 * wC (t ++ [0]) = wC (0 :: t) :=
  (rot_zero_of_swap t).symm

/-- **The one-step rotation recurrence, odd letter.**  Over `ℤ`,
`2 · C_{r+1} = 3 · C_r + G`. -/
theorem wC_rot_step_one {t : List Nat} {G : Nat}
    (hG : G + 3 ^ ones (1 :: t) = 2 ^ (1 :: t).length) :
    2 * wC (t ++ [1]) = 3 * wC (1 :: t) + G := by
  have h := rot_one_of_swap t
  omega

/-- **The closed form.**  `2 ^ r · C_r = 3 ^ (ones prefix) · C_0 + G · C(prefix)`,
where `C_r` is the rotation that cuts `w` after `r` letters.  No cycle
hypothesis: this is an identity between words. -/
theorem wC_rot_closed {w : List Nat} {r G : Nat}
    (hG : G + 3 ^ ones w = 2 ^ w.length) :
    2 ^ (w.take r).length * wC (w.drop r ++ w.take r)
      = 3 ^ ones (w.take r) * wC w + G * wC (w.take r) := by
  have hsplit : w.take r ++ w.drop r = w := List.take_append_drop r w
  have h := wC_swap_gap (u := w.drop r) (v := w.take r) (G := G) ?_
  · rw [hsplit] at h
    exact h
  · rw [Nat.add_comm (ones (w.drop r)), Nat.add_comm (w.drop r).length]
    have ho : ones (w.take r) + ones (w.drop r) = ones w := by
      rw [← ones_append]; rw [hsplit]
    have hl : (w.take r).length + (w.drop r).length = w.length := by
      rw [← List.length_append]; rw [hsplit]
    rw [ho, hl]
    exact hG

/-! ## 3. The rotation system collapses to a single condition -/

/-! ### Small arithmetic helpers (no Mathlib) -/

/-- Every power of three is odd. -/
theorem three_pow_odd : ∀ k : Nat, 3 ^ k % 2 = 1
  | 0 => rfl
  | k + 1 => by
      have ih := three_pow_odd k
      rw [Arith.three_pow_succ]
      omega

/-- No power of two is divisible by three. -/
theorem two_pow_mod_three : ∀ k : Nat, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2
  | 0 => Or.inl rfl
  | k + 1 => by
      have ih := two_pow_mod_three k
      rw [Arith.two_pow_succ]
      omega

/-- A divisor of a light gap is odd. -/
theorem gap_divisor_odd {G g : Nat} {w : List Nat}
    (hG : G + 3 ^ ones w = 2 ^ w.length) (hL : 0 < w.length) (hg : g ∣ G) :
    g % 2 = 1 := by
  have h2 : (2:Nat) ^ w.length = 2 * 2 ^ (w.length - 1) := by
    have hw : w.length = (w.length - 1) + 1 := by omega
    rw [hw, Arith.two_pow_succ]
    simp
  have h3 := three_pow_odd (ones w)
  have hGodd : G % 2 = 1 := by omega
  obtain ⟨c, hc⟩ := hg
  rcases Arith.mod_two_eq_zero_or_one g with he | ho
  · exfalso
    have hgk : g = 2 * (g / 2) := by omega
    have hgc : G = 2 * ((g / 2) * c) := by
      rw [hc, ← Nat.mul_assoc, ← hgk]
    omega
  · exact ho

/-- A divisor of a light gap of a word with at least one odd letter is prime to
three.  The hypothesis `0 < ones w` is necessary: at `ones w = 0` the gap is
`2 ^ L − 1`, which is a multiple of three whenever `L` is even. -/
theorem gap_divisor_not_three {G g : Nat} {w : List Nat}
    (hG : G + 3 ^ ones w = 2 ^ w.length) (ha : 0 < ones w) (hg : g ∣ G) :
    g % 3 ≠ 0 := by
  intro hgz
  have hgG : (3:Nat) ∣ G := by
    obtain ⟨c, hc⟩ := hg
    refine ⟨(g / 3) * c, ?_⟩
    rw [hc, ← Nat.mul_assoc]
    have : 3 * (g / 3) = g := by omega
    rw [this]
  have h3 : (3:Nat) ∣ 3 ^ ones w := by
    refine ⟨3 ^ (ones w - 1), ?_⟩
    have hw : ones w = (ones w - 1) + 1 := by omega
    rw [hw, Arith.three_pow_succ]
    simp
  obtain ⟨p, hp⟩ := hgG
  obtain ⟨q, hq⟩ := h3
  have hd : (2:Nat) ^ w.length = 3 * (p + q) := by rw [Nat.mul_add]; omega
  have := two_pow_mod_three w.length
  omega

/-- **The rotation system collapses.**  For any divisor `g` of the gap, the
integrality condition at the rotation cutting after `r` letters is *equivalent*
to the condition at the original word.  Not an implication in one direction and
not a cycle statement: an identity-level equivalence for every word. -/
theorem rot_dvd_iff {w : List Nat} {r G g : Nat}
    (hG : G + 3 ^ ones w = 2 ^ w.length) (hL : 0 < w.length) (ha : 0 < ones w)
    (hg : g ∣ G) :
    g ∣ wC w ↔ g ∣ wC (w.drop r ++ w.take r) := by
  have hodd := gap_divisor_odd hG hL hg
  have h3 := gap_divisor_not_three hG ha hg
  have hkey := wC_rot_closed (w := w) (r := r) hG
  have hGdvd : g ∣ G * wC (w.take r) := by
    obtain ⟨c, hc⟩ := hg
    exact ⟨c * wC (w.take r), by rw [hc, Nat.mul_assoc]⟩
  constructor
  · intro h
    have h1 : g ∣ 3 ^ ones (w.take r) * wC w := by
      obtain ⟨t, ht⟩ := h
      exact ⟨3 ^ ones (w.take r) * t, by rw [ht, Nat.mul_left_comm]⟩
    have h2 : g ∣ 2 ^ (w.take r).length * wC (w.drop r ++ w.take r) := by
      rw [hkey]
      obtain ⟨x, hx⟩ := h1
      obtain ⟨y, hy⟩ := hGdvd
      exact ⟨x + y, by rw [hx, hy, Nat.mul_add]⟩
    exact AccumulatorCap.dvd_cancel_two_pow hodd _ _ h2
  · intro h
    have h2 : g ∣ 2 ^ (w.take r).length * wC (w.drop r ++ w.take r) := by
      obtain ⟨t, ht⟩ := h
      exact ⟨2 ^ (w.take r).length * t, by rw [ht, Nat.mul_left_comm]⟩
    rw [hkey] at h2
    have h1 : g ∣ 3 ^ ones (w.take r) * wC w := by
      obtain ⟨y, hy⟩ := hGdvd
      obtain ⟨z, hz⟩ := h2
      refine ⟨z - y, ?_⟩
      have hle : g * y ≤ g * z := by omega
      rw [Nat.mul_sub]
      omega
    exact AccumulatorCap.dvd_cancel_three_pow h3 _ _ h1

/-- The same, phrased for an arbitrary factorization: conjugate words have
`g`-divisible accumulators together. -/
theorem swap_dvd_iff {u v : List Nat} {G g : Nat}
    (hG : G + 3 ^ ones (u ++ v) = 2 ^ (u ++ v).length) (hL : 0 < (u ++ v).length)
    (ha : 0 < ones (u ++ v)) (hg : g ∣ G) :
    g ∣ wC (u ++ v) ↔ g ∣ wC (v ++ u) := by
  have hd : (u ++ v).drop u.length = v := by simp
  have ht : (u ++ v).take u.length = u := by simp
  have h := rot_dvd_iff (w := u ++ v) (r := u.length) hG hL ha hg
  rw [hd, ht] at h
  exact h

/-! ## 4. Fully heavy rotations are the minimal ones -/

/-- **A fully heavy rotation minimises the accumulator.**  If every proper
prefix of `w` is heavy (`2 ^ r ≤ 3 ^ (ones (take r w))`), then `wC w` is at most
`wC` of every rotation of `w`.  This is the word-level form of "the cycle
minimum is the heavy point", proved with no arithmetic beyond the closed form. -/
theorem heavy_rot_min {w : List Nat} {r G : Nat}
    (hG : G + 3 ^ ones w = 2 ^ w.length)
    (hheavy : 2 ^ (w.take r).length ≤ 3 ^ ones (w.take r)) :
    2 ^ (w.take r).length * wC w ≤ 2 ^ (w.take r).length * wC (w.drop r ++ w.take r) := by
  have hkey := wC_rot_closed (w := w) (r := r) hG
  have hmul : 2 ^ (w.take r).length * wC w ≤ 3 ^ ones (w.take r) * wC w :=
    Nat.mul_le_mul_right _ hheavy
  omega

/-- The clean consequence: a fully heavy word has the smallest accumulator among
its rotations. -/
theorem heavy_rot_le {w : List Nat} {r G : Nat}
    (hG : G + 3 ^ ones w = 2 ^ w.length)
    (hheavy : 2 ^ (w.take r).length ≤ 3 ^ ones (w.take r)) :
    wC w ≤ wC (w.drop r ++ w.take r) := by
  have h := heavy_rot_min hG hheavy
  exact Nat.le_of_mul_le_mul_left h (Arith.two_pow_pos _)

/-! ## 5. Witnesses on a genuine cycle of `3x + 59`

The minimum of the `3x+59` cycle is `133`, with `L = 10`, `a = 6`,
`G = 2 ^ 10 − 3 ^ 6 = 295` and parity word `w59` below.  Because `G · x = d · C`,
the divisor that must divide every rotation accumulator is
`g = G / gcd(G, d) = 295 / 59 = 5`.  Each of the following is `decide`-checked.
-/

/-- The parity word of the `3x+59` cycle read from its minimum `133`. -/
def w59 : List Nat := [1, 1, 1, 1, 1, 1, 0, 0, 0, 0]

/-- Shape and gap of `w59`. -/
theorem w59_shape : w59.length = 10 ∧ ones w59 = 6 ∧ 295 + 3 ^ ones w59 = 2 ^ w59.length := by
  decide

/-- The ten rotation accumulators of `w59`, in order.  They are `5 ×` the ten
points of the cycle: `133, 229, 373, 589, 913, 1399, 2128, 1064, 532, 266`. -/
theorem w59_rotations :
    (List.range 10).map (fun r => wC (w59.drop r ++ w59.take r))
      = [665, 1145, 1865, 2945, 4565, 6995, 10640, 5320, 2660, 1330] := by
  decide

/-- **The rotation system collapses, seen on a real cycle.**  `5` divides every
one of the ten rotation accumulators — one condition, ten times, exactly as
`rot_dvd_iff` predicts. -/
theorem w59_all_rotations_div :
    ((List.range 10).map (fun r => wC (w59.drop r ++ w59.take r) % 5)).all (· == 0) := by
  decide

/-- **`w59` is fully heavy** at every proper prefix, and its accumulator `665` is
the smallest of the ten — the measured content of `heavy_rot_le`. -/
theorem w59_fully_heavy :
    ((List.range 9).map (fun r => decide (2 ^ (r + 1) ≤ 3 ^ ones (w59.take (r + 1))))).all (· == true) ∧
      ((List.range 10).map (fun r => decide (665 ≤ wC (w59.drop r ++ w59.take r)))).all (· == true) := by
  decide

/-- The `3x+5` cycle at `19`: word `[1,1,1,0,0]`, `G = 5`, rotation accumulators
`19, 31, 49, 76, 38` — the cycle points themselves, since `d = G = 5`.  Here
`g = 1` and the collapse is vacuous, which is the point: the collapse is a
theorem about `g`, and small `g` carries no information. -/
theorem w5_rotations :
    (List.range 5).map (fun r => wC (([1,1,1,0,0] : List Nat).drop r ++ ([1,1,1,0,0] : List Nat).take r))
      = [19, 31, 49, 76, 38] := by
  decide

end RotationSystem
end Collatz
