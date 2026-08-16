import Collatz.Structure.DensitySharp

/-!
# The density rate, parameterised

`Density` proves the rate `3k ≤ 5a` from `3 ^ 3 < 2 ^ 5`, and `DensitySharp`
proves `17k ≤ 27a` from `3 ^ 17 < 2 ^ 27`.  Both proofs are the same proof.  This
file states it once, for any pair `(p, q)`:

**If `3 ^ p < 2 ^ q`, then heaviness forces `p k ≤ q a`, and
`heavyCount k ^ q · (2 ^ p) ^ k ≤ (3 ^ q) ^ k`.**

Everything reduces to choosing a fraction `p / q` below `log 2 / log 3`, and the
two existing theorems become instances (`rate_three_five`, `rate_seventeen_
twentyseven`).  A third instance, `41 / 65`, is included because it is the best
convergent whose powers are still small enough to state comfortably.

## The ceiling

Writing `δ k` for the heavy fraction, the bound says
`δ k ^ q ≤ (3 ^ q / 2 ^ (p + q)) ^ k`, so

`δ k ≲ (3 / 2 ^ (1 + p/q)) ^ k = 2 ^ ((log₂ 3 − 1 − p/q) k)`.

The exponent is `1.58496 − 1 − p/q = 0.58496 − p/q`, and `p/q` is capped by
`log 2 / log 3 = 0.63093`.  So **no choice of rate beats `2 ^ (−0.04597 k)`,
i.e. `0.96863 ^ k`** — that is the ceiling of the entire method, and it does not
depend on how cleverly the fraction is chosen.

| rate | value | resulting decay |
|---|---|---|
| `3/5` | 0.60000 | `0.98965 ^ k` |
| `17/27` | 0.62963 | `0.96953 ^ k` |
| `41/65` | 0.63077 | `0.96882 ^ k` |
| ceiling | 0.63093 | `0.96863 ^ k` |

So `17/27` already sits within `0.1%` of what the method can ever give.  Pushing
the fraction further is not where any remaining gain lies, and there is no
sequence of refinements of this kind that reaches density bounds strong enough
to bear on the conjecture — the heavy set is nonempty at every level regardless,
since `2 ^ k − 1` is always in it.
-/

namespace Collatz
namespace DensityRate

open Reach Congruence _root_.Collatz.Sum Density

/-! ## Ceiling division with a variable divisor

`omega` handles division only by literals, and the divisor here is the
parameter `q`, so the two facts about `⌈n/q⌉ = (n + q − 1)/q` are proved once by
hand from `Nat.div_add_mod`. -/

/-- `q · ⌈n/q⌉ ≥ n`. -/
theorem le_mul_ceil_div (n q : Nat) (hq : 0 < q) : n ≤ q * ((n + (q - 1)) / q) := by
  have hdm := Nat.div_add_mod (n + (q - 1)) q
  have hlt : (n + (q - 1)) % q < q := Nat.mod_lt _ hq
  generalize hc : (n + (q - 1)) / q = c at hdm ⊢
  generalize hr : (n + (q - 1)) % q = r at hdm hlt
  omega

/-- `⌈n/q⌉ ≤ a` whenever `n ≤ q · a`. -/
theorem ceil_div_le {n q a : Nat} (hq : 0 < q) (h : n ≤ q * a) :
    (n + (q - 1)) / q ≤ a := by
  have hdm := Nat.div_add_mod (n + (q - 1)) q
  have hlt : (n + (q - 1)) % q < q := Nat.mod_lt _ hq
  have hexp : q * (a + 1) = q * a + q := by rw [Nat.mul_add, Nat.mul_one]
  generalize hc : (n + (q - 1)) / q = c at hdm ⊢
  generalize hr : (n + (q - 1)) % q = r at hdm hlt
  have hkey : q * c < q * (a + 1) := by omega
  have := Nat.lt_of_mul_lt_mul_left hkey
  omega

/-! ## The rate, for any admissible fraction -/

/-- **The exponent bound, parameterised.**  Any fraction `p / q` with
`3 ^ p < 2 ^ q` converts heaviness into `p k ≤ q a`. -/
theorem mul_le_mul_of_heavy {p q k a : Nat} (hpq : 3 ^ p < 2 ^ q) (h : 2 ^ k ≤ 3 ^ a) :
    p * k ≤ q * a := by
  cases k with
  | zero => omega
  | succ m =>
    by_cases hle : p * (m + 1) ≤ q * a
    · exact hle
    · exfalso
      have hlt : q * a + 1 ≤ p * (m + 1) := by omega
      -- `(2 ^ q) ^ k ≤ 3 ^ (q a)`
      have hA : ((2:Nat) ^ q) ^ (m + 1) ≤ 3 ^ (q * a) := by
        have h1 : ((2:Nat) ^ (m + 1)) ^ q ≤ ((3:Nat) ^ a) ^ q := Nat.pow_le_pow_left h q
        have h2 : ((2:Nat) ^ (m + 1)) ^ q = (2 ^ q) ^ (m + 1) := by
          rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
        have h3 : ((3:Nat) ^ a) ^ q = 3 ^ (q * a) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
        rw [h2, h3] at h1
        exact h1
      -- `3 ^ (q a) · 3 ≤ (3 ^ p) ^ k`
      have hB : (3:Nat) ^ (q * a) * 3 ≤ (3 ^ p) ^ (m + 1) := by
        have h1 : (3:Nat) ^ (q * a + 1) ≤ 3 ^ (p * (m + 1)) :=
          Arith.three_pow_le_three_pow hlt
        have h2 : (3:Nat) ^ (p * (m + 1)) = (3 ^ p) ^ (m + 1) := by
          rw [Nat.pow_mul]
        have h3 : (3:Nat) ^ (q * a + 1) = 3 ^ (q * a) * 3 := by
          rw [Nat.pow_succ]
        rw [h3, h2] at h1
        exact h1
      have hgt : ((3:Nat) ^ p) ^ (m + 1) < ((2:Nat) ^ q) ^ (m + 1) :=
        Nat.pow_lt_pow_left hpq (by omega)
      have h3pos : 0 < (3:Nat) ^ (q * a) := Arith.three_pow_pos _
      omega

/-- Every heavy residue carries weight at least `2 ^ ⌈p k / q⌉`. -/
theorem two_pow_le_weight {p q : Nat} (hq : 0 < q) (hpq : 3 ^ p < 2 ^ q)
    {k r : Nat} (h : heavyB k r = true) :
    2 ^ ((p * k + (q - 1)) / q) ≤ 2 ^ oddCount r k := by
  have h1 : 2 ^ k ≤ 3 ^ oddCount r k := by simpa [heavyB] using h
  have h2 : p * k ≤ q * oddCount r k := mul_le_mul_of_heavy hpq h1
  exact Arith.two_pow_le_two_pow (ceil_div_le hq h2)

/-- The counted weight bound at the rate `p / q`. -/
theorem mul_heavyCount_le {p q : Nat} (hq : 0 < q) (hpq : 3 ^ p < 2 ^ q) (k : Nat) :
    2 ^ ((p * k + (q - 1)) / q) * heavyCount k ≤ 3 ^ k := by
  have h := mul_countRange_le (n := 2 ^ k) (w := 2 ^ ((p * k + (q - 1)) / q))
    (p := heavyB k) (f := fun r => 2 ^ oddCount r k)
    (fun i _ hi => two_pow_le_weight hq hpq hi)
  have hw : sumRange (2 ^ k) (fun r => 2 ^ oddCount r k) = 3 ^ k := weightSum_eq k
  rw [heavyCount]
  omega

/-- **The density theorem, for any admissible rate.**  `heavyCount k ^ q ·
(2 ^ p) ^ k ≤ (3 ^ q) ^ k`, i.e. the heavy fraction satisfies
`δ k ^ q ≤ (3 ^ q / 2 ^ (p + q)) ^ k`. -/
theorem heavyCount_pow {p q : Nat} (hq : 0 < q) (hpq : 3 ^ p < 2 ^ q) (k : Nat) :
    heavyCount k ^ q * (2 ^ p) ^ k ≤ (3 ^ q) ^ k := by
  have hbase := mul_heavyCount_le hq hpq k
  have hpow : (2 ^ ((p * k + (q - 1)) / q) * heavyCount k) ^ q ≤ (3 ^ k) ^ q :=
    Nat.pow_le_pow_left hbase q
  have hleft : (2 ^ ((p * k + (q - 1)) / q) * heavyCount k) ^ q
      = 2 ^ (q * ((p * k + (q - 1)) / q)) * heavyCount k ^ q := by
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm ((p * k + (q - 1)) / q) q]
  have hright : ((3:Nat) ^ k) ^ q = (3 ^ q) ^ k := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  rw [hleft, hright] at hpow
  have hp : ((2:Nat) ^ p) ^ k ≤ 2 ^ (q * ((p * k + (q - 1)) / q)) := by
    have h1 : ((2:Nat) ^ p) ^ k = 2 ^ (p * k) := by rw [← Nat.pow_mul]
    rw [h1]
    exact Arith.two_pow_le_two_pow (le_mul_ceil_div (p * k) q hq)
  calc heavyCount k ^ q * (2 ^ p) ^ k
      ≤ heavyCount k ^ q * 2 ^ (q * ((p * k + (q - 1)) / q)) :=
        Nat.mul_le_mul_left _ hp
    _ = 2 ^ (q * ((p * k + (q - 1)) / q)) * heavyCount k ^ q := Nat.mul_comm _ _
    _ ≤ (3 ^ q) ^ k := hpow

/-! ## The three instances -/

/-- `3 / 5`, the rate of `Density.heavyCount_pow_five`. -/
theorem rate_three_five (k : Nat) : heavyCount k ^ 5 * (2 ^ 3) ^ k ≤ (3 ^ 5) ^ k :=
  heavyCount_pow (by omega) (by decide) k

/-- `17 / 27`, the rate of `DensitySharp.heavyCount_pow_twentyseven`. -/
theorem rate_seventeen_twentyseven (k : Nat) :
    heavyCount k ^ 27 * (2 ^ 17) ^ k ≤ (3 ^ 27) ^ k :=
  heavyCount_pow (by omega) (by decide) k

/-- `41 / 65 = 0.630769`, within `0.00016` of `log 2 / log 3`.  The underlying
inequality is `3 ^ 41 = 36472996377170786403 < 36893488147419103232 = 2 ^ 65`. -/
theorem fortyone_sixtyfive_holds : (3:Nat) ^ 41 < 2 ^ 65 := by decide

theorem rate_fortyone_sixtyfive (k : Nat) :
    heavyCount k ^ 65 * (2 ^ 41) ^ k ≤ (3 ^ 65) ^ k :=
  heavyCount_pow (by omega) fortyone_sixtyfive_holds k

/-! ## The ceiling -/

/-- **No admissible rate reaches `2 / 3`.**  Any `p / q` usable here has
`3 ^ p < 2 ^ q`, and `2 / 3` fails that: `3 ^ 2 = 9 > 8 = 2 ^ 3`.  So every rate
this method can use lies strictly below `log 2 / log 3`, and the decay it yields
is strictly worse than the ceiling `2 ^ (−0.04597 k)`. -/
theorem two_thirds_fails : (2:Nat) ^ 3 < 3 ^ 2 := by decide

/-- The near-miss that caps the practical rates: `12 / 19` is the first
convergent above the threshold, and it fails by `0.14%`. -/
theorem twelve_nineteen_fails : (2:Nat) ^ 19 < 3 ^ 12 :=
  DensitySharp.twelve_nineteen_fails

/-- The next convergent above the threshold also fails: `53 / 84`. -/
theorem fiftythree_eightyfour_fails : (2:Nat) ^ 84 < 3 ^ 53 := by decide

/-- **The rates in order.**  Each admissible fraction improves on the last, and
each failing one shows where the ceiling is.  The gap between `41 / 65` and the
threshold is under `0.0002`, so the method is effectively exhausted. -/
theorem rate_ladder :
    (3:Nat) ^ 3 < 2 ^ 5 ∧ (3:Nat) ^ 17 < 2 ^ 27 ∧ (3:Nat) ^ 41 < 2 ^ 65 ∧
    (2:Nat) ^ 3 < 3 ^ 2 ∧ (2:Nat) ^ 19 < 3 ^ 12 ∧ (2:Nat) ^ 84 < 3 ^ 53 :=
  ⟨by decide, DensitySharp.seventeen_twentyseven_holds, fortyone_sixtyfive_holds,
   two_thirds_fails, twelve_nineteen_fails, fiftythree_eightyfour_fails⟩

end DensityRate
end Collatz
