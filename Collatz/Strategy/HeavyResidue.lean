import Collatz.Strategy.HeavyWord
import Collatz.Strategy.CycleCriterion

/-!
# Heaviness pins the accumulator modulo four — and what that was worth

A measurement made this round looked like the one piece of structure nobody could
explain: on *heavy* words — Terras survivors, the words a never-dropper is
confined to — the map `w ↦ C(w)` appeared to be injective, exhaustively to length
28, while on arbitrary words it collides constantly.  If it were true, the
accumulator alone would determine a never-dropper's residue class, which would be
a genuinely new invariant.

It is false.  The first collision is at length **83**:

`r  = 682585550255899720490087`  with `a  = 53`,
`r' = 5448846481649007412081903` with `a' = 55`,

both heavy at all 83 prefixes, sharing the accumulator
`212525282698140465463422331`.  Five collisions at that length, twenty more at
86.  Injectivity is *proved* below length 58 and exhausted by search to 82, so
the measurement was not wrong — the search was too short.

## Why it held so long, and why it had to fail

Two facts, both proved here, explain the whole shape of the phenomenon.

**Heaviness pins `C` modulo four.**  Heaviness at `i = 2` needs `4 ≤ 3 ^ a₂`, so a
heavy word begins with *two* odd steps; from there every later odd step
contributes `2 ^ j` with `j ≥ 2`, invisible mod 4, and multiplies `C` by three
exactly as it multiplies `3 ^ a`.  So `C ≡ 3 ^ a (mod 4)` (`affineC_mod_four`) —
the accumulator knows the odd-step count *modulo two*.  A collision therefore
needs `a' − a` even, and the cheapest case `a' = a + 1` is excluded outright.

**Size then closes the window, but only for a while.**  Normalising,
`C / 3 ^ (a−1) = Σ 2 ^ tᵢ / 3 ^ (i−1)`, heaviness makes every term at most one, so
the sum is at most about `0.7213 a`; ordering makes it at least three.  A
collision with `a' = a + 2` needs two such sums differing by a factor of nine
while both live in `[3, 0.7213a]`.  That is impossible until `a ≈ 37`, which is
`j ≈ 58` — and the margin shrinks *linearly*, because the ceiling grows with `a`
while the target stays the constant 27.  The window opens at 58 and the first
collision lands in it at 83.  Nothing structural was ever protecting the map.

## The by-product worth keeping

The factor of two that `HeavyWord` removes from the older window bound is exactly
what makes the mod-four law available: relaxing heaviness to `2 ^ i ≤ c · 3 ^ aᵢ`
survives to length 24 at `c = 3/2` but breaks at `c = 2` — and breaks with an
*odd* difference `a' − a = 1`, because `c = 2` is precisely the constant that
admits a word beginning `OE` and destroys `r ≡ 3 (mod 4)`.

Also proved here: `heavy_accumulator_bound_sharp`, a factor `3/2` improvement on
`HeavyWord.heavy_accumulator_bound`, by the same one-line induction — the odd
step needs only `2 ^ j ≤ 3 ^ a`, which heaviness supplies at `j` rather than at
`j + 1`.

The negative conclusion is worth stating plainly, because it constrains future
work: `C` is **not** a complete invariant of a heavy window.  Anything carrying
window data must keep carrying the pair `(oddCount, affineC)`, as
`CycleAccumulator` and `ClassCap` already do.
-/

namespace Collatz
namespace HeavyResidue

open Congruence AffineExact

/-! ## A heavy word begins with two odd steps -/

/-- Heaviness at the first step forces the start to be odd: `2 ≤ 3 ^ a₁` fails
for `a₁ = 0`. -/
theorem odd_start_of_heavy {x : Nat} (h : 2 ^ 1 ≤ 3 ^ oddCount x 1) : x % 2 = 1 := by
  have hlast := Density.oddCount_succ_last x 0
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit 0 x) with he | ho
  · exfalso
    rw [acceleratedOrbit_zero] at he
    have hzero : oddCount x 1 = 0 := by simpa [he] using hlast
    rw [hzero] at h
    simp at h
  · rw [acceleratedOrbit_zero] at ho
    exact ho

/-- Heaviness at the second step forces the *second* step to be odd as well:
`4 ≤ 3 ^ a₂` fails for `a₂ ≤ 1`. -/
theorem second_odd_of_heavy {x : Nat} (h1 : 2 ^ 1 ≤ 3 ^ oddCount x 1)
    (h2 : 2 ^ 2 ≤ 3 ^ oddCount x 2) : acceleratedOrbit 1 x % 2 = 1 := by
  have hx := odd_start_of_heavy h1
  have hlast0 := Density.oddCount_succ_last x 0
  have hlast1 := Density.oddCount_succ_last x 1
  rw [acceleratedOrbit_zero, hx] at hlast0
  have hone : oddCount x 1 = 1 := by simpa using hlast0
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit 1 x) with he | ho
  · exfalso
    rw [he, hone] at hlast1
    rw [hlast1] at h2
    simp at h2
  · exact ho

/-! ## The accumulator modulo four -/

/-- With the first two steps odd, the accumulator tracks `3 ^ a` modulo four for
the rest of the window: every later odd step adds `2 ^ j` with `j ≥ 2`, which is
invisible mod 4, and multiplies both sides by three. -/
theorem affineC_mod_four_of_two_odd {x : Nat} (h0 : x % 2 = 1)
    (h1 : acceleratedOrbit 1 x % 2 = 1) :
    ∀ k : Nat, affineC (2 + k) x % 4 = 3 ^ oddCount x (2 + k) % 4 := by
  intro k
  induction k with
  | zero =>
    have hC1 : affineC 1 x = 1 := by
      have h0' : acceleratedOrbit 0 x % 2 = 1 := by rw [acceleratedOrbit_zero]; exact h0
      rw [affineC_odd h0', affineC_zero]
    have hC2 : affineC 2 x = 5 := by
      rw [show (2:Nat) = 1 + 1 from rfl, affineC_odd h1, hC1]
    have hlast0 := Density.oddCount_succ_last x 0
    have hlast1 := Density.oddCount_succ_last x 1
    rw [acceleratedOrbit_zero, h0] at hlast0
    rw [h1] at hlast1
    have h01 : oddCount x 1 = 1 := by simpa using hlast0
    have h12 : oddCount x 2 = oddCount x 1 + 1 := by simpa using hlast1
    have hcount : oddCount x 2 = 2 := by omega
    rw [hC2, hcount]
  | succ k ih =>
    have hlast := Density.oddCount_succ_last x (2 + k)
    have hpow : (2:Nat) ^ (2 + k) % 4 = 0 := by
      have hsplit : (2:Nat) ^ (2 + k) = 4 * 2 ^ k := by
        rw [Nat.pow_add]
      omega
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit (2 + k) x) with he | ho
    · have hcount : oddCount x (2 + k + 1) = oddCount x (2 + k) := by omega
      rw [show 2 + (k + 1) = 2 + k + 1 from rfl, hcount, affineC_even he]
      exact ih
    · have hcount : oddCount x (2 + k + 1) = oddCount x (2 + k) + 1 := by omega
      rw [show 2 + (k + 1) = 2 + k + 1 from rfl, hcount, affineC_odd ho,
        Arith.three_pow_succ]
      generalize hA : affineC (2 + k) x = A at ih
      generalize hB : (3:Nat) ^ oddCount x (2 + k) = B at ih
      omega

/-- **`C ≡ 3 ^ a (mod 4)` on every heavy window of length at least two.**  So the
accumulator determines the odd-step count modulo two — which is why the cheapest
possible collision, with counts differing by one, cannot occur. -/
theorem affineC_mod_four {x j : Nat} (hj : 2 ≤ j)
    (hheavy : ∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount x i) :
    affineC j x % 4 = 3 ^ oddCount x j % 4 := by
  have h1 := hheavy 1 (by omega)
  have h2 := hheavy 2 (by omega)
  have hx := odd_start_of_heavy h1
  have hsecond := second_odd_of_heavy h1 h2
  obtain ⟨k, hk⟩ : ∃ k : Nat, j = 2 + k := ⟨j - 2, by omega⟩
  subst hk
  exact affineC_mod_four_of_two_odd hx hsecond k

/-! ## The sharper accumulator bound -/

/-- **A factor `3/2` on `HeavyWord.heavy_accumulator_bound`.**  The same
induction, but the odd step needs heaviness only at `j`, not at `j + 1`. -/
theorem heavy_accumulator_bound_sharp (x : Nat) : ∀ j : Nat,
    (∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount x i) →
    3 * affineC j x ≤ oddCount x j * 3 ^ oddCount x j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hheavy
    have ihb := ih (fun i hi => hheavy i (Nat.le_succ_of_le hi))
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hcount : oddCount x (j + 1) = oddCount x j := by omega
      rw [hcount, affineC_even he]
      exact ihb
    · have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      have hheavy_j : 2 ^ j ≤ 3 ^ oddCount x j := hheavy j (Nat.le_succ _)
      rw [hcount, affineC_odd ho, Arith.three_pow_succ]
      have hmul : 3 * (3 * affineC j x) ≤ 3 * (oddCount x j * 3 ^ oddCount x j) :=
        Nat.mul_le_mul_left _ ihb
      have hassoc : 3 * (oddCount x j * 3 ^ oddCount x j)
          = oddCount x j * (3 * 3 ^ oddCount x j) := by
        rw [Nat.mul_left_comm]
      have hgoal : (oddCount x j + 1) * (3 * 3 ^ oddCount x j)
          = oddCount x j * (3 * 3 ^ oddCount x j) + 3 * 3 ^ oddCount x j := by
        rw [Nat.add_mul, Nat.one_mul]
      omega

/-! ## What the accumulator does determine -/

/-- **The pair, not the accumulator alone.**  `(oddCount, affineC)` determines the
residue class of the window: `3 ^ a · x + C` is a multiple of `2 ^ j`, and `3 ^ a`
is invertible there.  The refutation above says the second coordinate cannot be
dropped. -/
theorem class_of_count_and_accumulator {x y j : Nat}
    (hcount : oddCount x j = oddCount y j) (hC : affineC j x = affineC j y) :
    x % 2 ^ j = y % 2 ^ j := by
  have hx := CycleCriterion.two_pow_dvd_affine x j
  have hy := CycleCriterion.two_pow_dvd_affine y j
  rw [← hcount, ← hC] at hy
  have hodd : (3:Nat) ^ oddCount x j % 2 = 1 := Arith.three_pow_odd _
  rcases Nat.le_total y x with hle | hle
  · obtain ⟨c, hc⟩ := hx
    obtain ⟨e, he⟩ := hy
    have hmono : 3 ^ oddCount x j * y ≤ 3 ^ oddCount x j * x := Nat.mul_le_mul_left _ hle
    have hce : e ≤ c := by
      have hle2 : 2 ^ j * e ≤ 2 ^ j * c := by omega
      exact Nat.le_of_mul_le_mul_left hle2 (Arith.two_pow_pos j)
    have hd : 2 ^ j ∣ (3 ^ oddCount x j * x - 3 ^ oddCount x j * y) := by
      refine ⟨c - e, ?_⟩
      rw [Nat.mul_sub]
      omega
    obtain ⟨t, ht⟩ := CycleCriterion.cancel_odd_mod_two_pow hodd hle hd
    have hxy : x = y + 2 ^ j * t := by omega
    rw [hxy, Nat.add_mul_mod_self_left]
  · obtain ⟨c, hc⟩ := hx
    obtain ⟨e, he⟩ := hy
    have hmono : 3 ^ oddCount x j * x ≤ 3 ^ oddCount x j * y := Nat.mul_le_mul_left _ hle
    have hce : c ≤ e := by
      have hle2 : 2 ^ j * c ≤ 2 ^ j * e := by omega
      exact Nat.le_of_mul_le_mul_left hle2 (Arith.two_pow_pos j)
    have hd : 2 ^ j ∣ (3 ^ oddCount x j * y - 3 ^ oddCount x j * x) := by
      refine ⟨e - c, ?_⟩
      rw [Nat.mul_sub]
      omega
    obtain ⟨t, ht⟩ := CycleCriterion.cancel_odd_mod_two_pow hodd hle hd
    have hxy : y = x + 2 ^ j * t := by omega
    rw [hxy, Nat.add_mul_mod_self_left]

end HeavyResidue
end Collatz
