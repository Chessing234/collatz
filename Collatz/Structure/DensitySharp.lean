import Collatz.Structure.Density
import Collatz.Structure.OrbitMin

/-!
# A sharper density rate

`Density.three_mul_le_five_mul_of_heavy` derives `3k ≤ 5a` from heaviness, using
only `3 ^ 3 < 2 ^ 5` — that is, `27 < 32`.  The rate it delivers is `a ≥ 3k/5 =
0.600 k`.

The true threshold is `a ≥ k · log 2 / log 3 = 0.63093 k`, so `3/5` leaves real
room.  Any fraction `p/q` with `3 ^ p < 2 ^ q` gives a valid rate, and the
question is how close to `log 2 / log 3` such a fraction can get with `q` small
enough for the powers to stay manageable.

The convergents of `log 2 / log 3` are `1/2, 3/5, 12/19, 17/27, …`.  The
convergent `12/19` fails — `3 ^ 12 = 531441` exceeds `2 ^ 19 = 524288`, which is
the same near-miss that makes the Collatz problem hard in the first place.  The
next one works:

`3 ^ 17 = 129 140 163  <  134 217 728 = 2 ^ 27`.

So heaviness forces `17k ≤ 27a`, i.e. `a ≥ 0.62963 k` — within `0.0013` of the
true threshold, against `0.031` for `3/5`.

Propagating it through the same weight argument sharpens the density theorem
from

`heavyCount k ^ 5 · 8 ^ k ≤ 243 ^ k`   (heavy fraction `≲ 0.98965 ^ k`)

to

`heavyCount k ^ 27 · (2 ^ 17) ^ k ≤ (3 ^ 27) ^ k`   (heavy fraction `≲ 0.9695 ^ k`),

roughly tripling the decay exponent.  It still does not prove anything about
Collatz — the heavy set remains nonempty at every level, and `2 ^ k − 1` is in
it — but it is the sharpest rate this argument can give without a fraction of
much larger height.
-/

namespace Collatz
namespace DensitySharp

open Reach Congruence _root_.Collatz.Sum Density

/-! ## The sharpened exponent bound -/

/-- The near-miss that rules out the convergent `12/19`. -/
theorem twelve_nineteen_fails : (2:Nat) ^ 19 < 3 ^ 12 := by decide

/-- The inequality that makes `17/27` work. -/
theorem seventeen_twentyseven_holds : (3:Nat) ^ 17 < 2 ^ 27 := by decide

/-- **The sharpened exponent bound.**  A heavy residue has `17k ≤ 27a`, a rate of
`0.62963` against the `0.600` of `Density.three_mul_le_five_mul_of_heavy`. -/
theorem seventeen_mul_le_twentyseven_mul_of_heavy {k a : Nat} (h : 2 ^ k ≤ 3 ^ a) :
    17 * k ≤ 27 * a := by
  cases k with
  | zero => omega
  | succ m =>
    by_cases hle : 17 * (m + 1) ≤ 27 * a
    · exact hle
    · exfalso
      have hlt : 27 * a + 1 ≤ 17 * (m + 1) := by omega
      -- `(2 ^ 27) ^ k ≤ 3 ^ (27 a)`
      have hA : ((2:Nat) ^ 27) ^ (m + 1) ≤ 3 ^ (27 * a) := by
        have h1 : ((2:Nat) ^ (m + 1)) ^ 27 ≤ ((3:Nat) ^ a) ^ 27 := Nat.pow_le_pow_left h 27
        have h2 : ((2:Nat) ^ (m + 1)) ^ 27 = (2 ^ 27) ^ (m + 1) := by
          rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
        have h3 : ((3:Nat) ^ a) ^ 27 = 3 ^ (27 * a) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
        rw [h2, h3] at h1
        exact h1
      -- `3 ^ (27 a) · 3 ≤ (3 ^ 17) ^ k`
      have hB : (3:Nat) ^ (27 * a) * 3 ≤ (3 ^ 17) ^ (m + 1) := by
        have h1 : (3:Nat) ^ (27 * a + 1) ≤ 3 ^ (17 * (m + 1)) :=
          Arith.three_pow_le_three_pow hlt
        have h2 : (3:Nat) ^ (17 * (m + 1)) = (3 ^ 17) ^ (m + 1) := by
          rw [Nat.pow_mul]
        have h3 : (3:Nat) ^ (27 * a + 1) = 3 ^ (27 * a) * 3 := by
          rw [Nat.pow_succ]
        rw [h3, h2] at h1
        exact h1
      have hgt : ((3:Nat) ^ 17) ^ (m + 1) < ((2:Nat) ^ 27) ^ (m + 1) :=
        Nat.pow_lt_pow_left seventeen_twentyseven_holds (by omega)
      have h3pos : 0 < (3:Nat) ^ (27 * a) := Arith.three_pow_pos _
      omega

/-- Every heavy residue carries weight at least `2 ^ ⌈17k/27⌉`. -/
theorem two_pow_le_weight_of_heavy_sharp {k r : Nat} (h : heavyB k r = true) :
    2 ^ ((17 * k + 26) / 27) ≤ 2 ^ oddCount r k := by
  have h1 : 2 ^ k ≤ 3 ^ oddCount r k := by simpa [heavyB] using h
  have h2 : 17 * k ≤ 27 * oddCount r k := seventeen_mul_le_twentyseven_mul_of_heavy h1
  exact Arith.two_pow_le_two_pow (by omega)

/-- The counted weight bound at the sharper rate. -/
theorem mul_heavyCount_le_sharp (k : Nat) :
    2 ^ ((17 * k + 26) / 27) * heavyCount k ≤ 3 ^ k := by
  have h := mul_countRange_le (n := 2 ^ k) (w := 2 ^ ((17 * k + 26) / 27))
    (p := heavyB k) (f := fun r => 2 ^ oddCount r k)
    (fun i _ hi => two_pow_le_weight_of_heavy_sharp hi)
  have hw : sumRange (2 ^ k) (fun r => 2 ^ oddCount r k) = 3 ^ k := weightSum_eq k
  rw [heavyCount]
  omega

/-! ## The sharpened density theorem -/

/-- **The density theorem, sharpened.**  `heavyCount k ^ 27 · (2 ^ 17) ^ k ≤
(3 ^ 27) ^ k`.

Against the total `(2 ^ k) ^ 27` this says the heavy fraction `δ k` satisfies
`δ k ^ 27 ≤ (3 ^ 27 / 2 ^ 44) ^ k`, and `3 ^ 27 / 2 ^ 44 ≈ 0.4334`, so
`δ k ≲ 0.9695 ^ k`.  The rate from `Density.heavyCount_pow_five` is `0.98965 ^ k`;
the decay exponent roughly triples. -/
theorem heavyCount_pow_twentyseven (k : Nat) :
    heavyCount k ^ 27 * (2 ^ 17) ^ k ≤ (3 ^ 27) ^ k := by
  have hbase := mul_heavyCount_le_sharp k
  have hpow : (2 ^ ((17 * k + 26) / 27) * heavyCount k) ^ 27 ≤ (3 ^ k) ^ 27 :=
    Nat.pow_le_pow_left hbase 27
  have hleft : (2 ^ ((17 * k + 26) / 27) * heavyCount k) ^ 27
      = 2 ^ (27 * ((17 * k + 26) / 27)) * heavyCount k ^ 27 := by
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm ((17 * k + 26) / 27) 27]
  have hright : ((3:Nat) ^ k) ^ 27 = (3 ^ 27) ^ k := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  rw [hleft, hright] at hpow
  have h17 : ((2:Nat) ^ 17) ^ k ≤ 2 ^ (27 * ((17 * k + 26) / 27)) := by
    have h1 : ((2:Nat) ^ 17) ^ k = 2 ^ (17 * k) := by
      rw [← Nat.pow_mul]
    rw [h1]
    exact Arith.two_pow_le_two_pow (by omega)
  calc heavyCount k ^ 27 * (2 ^ 17) ^ k
      ≤ heavyCount k ^ 27 * 2 ^ (27 * ((17 * k + 26) / 27)) :=
        Nat.mul_le_mul_left _ h17
    _ = 2 ^ (27 * ((17 * k + 26) / 27)) * heavyCount k ^ 27 := Nat.mul_comm _ _
    _ ≤ (3 ^ 27) ^ k := hpow

/-- Restated against the total number of classes: the heavy fraction to the
twenty-seventh power is at most `(3 ^ 27 / 2 ^ 44) ^ k`. -/
theorem heavyCount_pow_twentyseven_ratio (k : Nat) :
    heavyCount k ^ 27 * (2 ^ 44) ^ k ≤ (3 ^ 27) ^ k * (2 ^ k) ^ 27 := by
  have hmain := heavyCount_pow_twentyseven k
  have h44 : ((2:Nat) ^ 44) ^ k = (2 ^ 17) ^ k * (2 ^ k) ^ 27 := by
    have e1 : ((2:Nat) ^ 44) ^ k = 2 ^ (44 * k) := (Nat.pow_mul 2 44 k).symm
    have e2 : ((2:Nat) ^ 17) ^ k = 2 ^ (17 * k) := (Nat.pow_mul 2 17 k).symm
    have e3 : ((2:Nat) ^ k) ^ 27 = 2 ^ (k * 27) := (Nat.pow_mul 2 k 27).symm
    rw [e1, e2, e3, ← Nat.pow_add]
    congr 1
    omega
  rw [h44, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ hmain

/-- The new rate genuinely exceeds the old: `17/27 > 3/5`, since
`3 · 27 = 81 < 85 = 17 · 5`. -/
theorem sharper_rate : (3:Nat) * 27 < 17 * 5 := by decide

/-- And it stays below the true threshold, as it must: `17/27 < log 2 / log 3`
is exactly `3 ^ 17 < 2 ^ 27`. -/
theorem rate_below_threshold : (3:Nat) ^ 17 < 2 ^ 27 := seventeen_twentyseven_holds

/-! ## The rate at the orbit minimum -/

/-- The orbit minimum of a counterexample satisfies the sharper rate at every
scale below itself. -/
theorem rate_sharp {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat} (hk : 2 ^ k ≤ m) :
    17 * (k - 1) ≤ 27 * oddCount m k := by
  have hlt := OrbitMin.heavy hn hm hmin hk
  have hle : 2 ^ (k - 1) ≤ 3 ^ oddCount m k := by
    cases k with
    | zero =>
      have h3 := Arith.three_pow_pos (oddCount m 0)
      simp
    | succ j =>
      have hsplit : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
      have hidx : j + 1 - 1 = j := by omega
      rw [hidx]
      omega
  exact seventeen_mul_le_twentyseven_mul_of_heavy hle

end DensitySharp
end Collatz
