import Collatz.Structure.Congruence
import Collatz.Core.Sum
import Collatz.Structure.Obstruction

/-!
# The density theorem

Terras (1976) proved that almost every integer has a finite stopping time.  The
combinatorial heart of that theorem is a statement about residues: of the `2^k`
residue classes modulo `2^k`, only a vanishing fraction have a parity vector
heavy enough to prevent descent in `k` steps.

This file proves that statement, from scratch, with an explicit geometric rate
and no real analysis at all.

## The device

The usual proof counts parity vectors by weight and estimates a binomial tail.
That route needs binomial coefficients, an entropy bound, and real logarithms.
The route taken here needs none of them.

Define the **weight sum**

`W k = Σ_{r < 2^k} 2^{a(r,k)}`,   `a(r,k)` = number of odd steps in `k` steps from `r`.

The key observation is that residues pair up.  For `r < 2^k`, the congruence
identity gives `T^k(2^k + r) = 3^{a(r,k)} + T^k(r)`, and `3^{a}` is odd, so
`T^k(r)` and `T^k(2^k + r)` have **opposite parities**.  Exactly one member of
the pair `{r, 2^k + r}` takes an odd step at time `k`, so

`2^{a(r,k+1)} + 2^{a(2^k+r,k+1)} = 2^{a(r,k)} + 2^{a(r,k)+1} = 3 · 2^{a(r,k)}`.

Summing over the pairs gives `W (k+1) = 3 · W k`, hence `W k = 3 ^ k`
(`weightSum_eq`).  A one-line induction replaces the entire binomial estimate.

## The bound

Call `r` **heavy** at level `k` when `2 ^ k ≤ 3 ^ {a(r,k)}` — exactly the
residues whose multiplier is too large to force a drop.  Heaviness forces
`3k ≤ 5a` (`three_mul_le_five_mul_of_heavy`, proved from `32 ^ k > 27 ^ k`
alone), so every heavy residue carries weight at least `2 ^ ⌈3k/5⌉`.  Comparing
that against `W k = 3 ^ k` gives the main theorem

`heavyCount k ^ 5 * 8 ^ k ≤ 243 ^ k`

equivalently `(heavyCount k / 2 ^ k) ^ 5 ≤ (243/256) ^ k`: the heavy fraction
decays geometrically.

## What this does not do

It does not prove Collatz, and cannot.  Density zero is not emptiness: by
`Obstruction.sieve_never_clears` the residue `2 ^ k − 1` is heavy at every
level, so the exceptional set is nonempty for every `k`.  A vanishing fraction
of counterexamples is still enough counterexamples to break the conjecture.
-/

namespace Collatz
namespace Density

open Reach Congruence _root_.Collatz.Sum

/-! ## The last parity bit -/

/-- The odd-step count grows by the parity of the current state. -/
theorem oddCount_succ_last (n k : Nat) :
    oddCount n (k + 1) = oddCount n k + acceleratedOrbit k n % 2 := by
  have h1 : parityVector n (k + 1) = parityVector n k ++ [acceleratedOrbit k n % 2] := by
    simp [parityVector, List.range_succ]
  rw [oddCount, h1, List.count_append, ← oddCount]
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with h | h <;> rw [h] <;> simp

/-- The odd-step count over `k` steps depends only on the residue modulo `2 ^ k`. -/
theorem oddCount_mod (n k : Nat) : oddCount n k = oddCount (n % 2 ^ k) k := by
  rw [oddCount, oddCount, parityVector_mod_pow_two]

/-- Shifting a residue by the modulus does not change its odd-step count. -/
theorem oddCount_two_pow_add {r k : Nat} (hr : r < 2 ^ k) :
    oddCount (2 ^ k + r) k = oddCount r k := by
  rw [oddCount_mod (2 ^ k + r) k]
  have hmod : (2 ^ k + r) % 2 ^ k = r := by
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hr
  rw [hmod]

/-- The congruence identity at `m = 1`: shifting by the modulus adds the
multiplier to the `k`-th iterate. -/
theorem accOrbit_two_pow_add (r k : Nat) :
    acceleratedOrbit k (2 ^ k + r) = 3 ^ oddCount r k + acceleratedOrbit k r := by
  have h := accOrbit_pow_two_mul_add k 1 r
  simp only [Nat.mul_one] at h
  exact h

/-- **The pairing lemma.**  A residue and its shift by the modulus take opposite
parity steps at time `k`, so their weights sum to three times the common weight
at level `k`. -/
theorem weight_pair (r k : Nat) (hr : r < 2 ^ k) :
    2 ^ oddCount r (k + 1) + 2 ^ oddCount (2 ^ k + r) (k + 1)
      = 3 * 2 ^ oddCount r k := by
  have hshift : oddCount (2 ^ k + r) k = oddCount r k := oddCount_two_pow_add hr
  have horb : acceleratedOrbit k (2 ^ k + r) = 3 ^ oddCount r k + acceleratedOrbit k r :=
    accOrbit_two_pow_add r k
  have hodd : 3 ^ oddCount r k % 2 = 1 := Arith.three_pow_odd _
  rw [oddCount_succ_last, oddCount_succ_last, hshift, horb]
  have hz : oddCount r k + 0 = oddCount r k := by omega
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k r) with he | ho
  · have h1 : (3 ^ oddCount r k + acceleratedOrbit k r) % 2 = 1 := by omega
    rw [he, h1, hz, Arith.two_pow_succ]
    omega
  · have h1 : (3 ^ oddCount r k + acceleratedOrbit k r) % 2 = 0 := by omega
    rw [ho, h1, hz, Arith.two_pow_succ]
    omega

/-! ## The weight sum -/

/-- `weightSum k = Σ_{r < 2^k} 2^{a(r,k)}`. -/
def weightSum (k : Nat) : Nat := sumRange (2 ^ k) (fun r => 2 ^ oddCount r k)

/-- **The weight identity.**  `Σ_{r < 2^k} 2^{a(r,k)} = 3 ^ k`.

This single identity replaces the binomial-tail estimate of the classical
proof. -/
theorem weightSum_eq (k : Nat) : weightSum k = 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hsplit : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := Arith.two_pow_succ k
    rw [weightSum, hsplit, sumRange_two_mul]
    have hcombine :
        sumRange (2 ^ k) (fun r => 2 ^ oddCount r (k + 1))
          + sumRange (2 ^ k) (fun i => 2 ^ oddCount (2 ^ k + i) (k + 1))
        = sumRange (2 ^ k) (fun r => 3 * 2 ^ oddCount r k) := by
      rw [← sumRange_add]
      refine sumRange_congr (fun i hi => ?_)
      exact weight_pair i k hi
    rw [hcombine, sumRange_const_mul]
    have : sumRange (2 ^ k) (fun r => 2 ^ oddCount r k) = 3 ^ k := ih
    rw [this, ← Arith.three_pow_succ]

/-! ## Heavy residues -/

/-- A residue is **heavy** at level `k` when its multiplier `3 ^ {a(r,k)}` is at
least the modulus, which is exactly the obstruction to descent. -/
def heavyB (k r : Nat) : Bool := decide (2 ^ k ≤ 3 ^ oddCount r k)

/-- `heavyCount k` counts the heavy residues below `2 ^ k`. -/
def heavyCount (k : Nat) : Nat := countRange (2 ^ k) (heavyB k)

/-- Heaviness is exactly the failure of the multiplier condition in the descent
criterion. -/
theorem not_descends_of_heavy {k r : Nat} (h : heavyB k r = true) :
    ¬ Descends k r := by
  intro hd
  have h1 : 2 ^ k ≤ 3 ^ oddCount r k := by simpa [heavyB] using h
  have h2 := hd.1
  omega

/-- **The exponent bound.**  A heavy residue has `3k ≤ 5a`.  The proof needs
only that `32 ^ k` exceeds `27 ^ k`. -/
theorem three_mul_le_five_mul_of_heavy {k a : Nat} (h : 2 ^ k ≤ 3 ^ a) :
    3 * k ≤ 5 * a := by
  cases k with
  | zero => omega
  | succ m =>
    by_cases hle : 3 * (m + 1) ≤ 5 * a
    · exact hle
    · exfalso
      -- `5a ≤ 3k - 1`, so `3 ^ (5a) ≤ 3 ^ (3k-1)`, while `3 ^ (5a) ≥ 32 ^ k`
      have hlt : 5 * a + 1 ≤ 3 * (m + 1) := by omega
      have h32 : (32:Nat) ^ (m + 1) ≤ 3 ^ (5 * a) := by
        have h1 : ((2:Nat) ^ (m + 1)) ^ 5 ≤ ((3:Nat) ^ a) ^ 5 := Nat.pow_le_pow_left h 5
        have h2 : ((2:Nat) ^ (m + 1)) ^ 5 = 32 ^ (m + 1) := by
          rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
        have h3 : ((3:Nat) ^ a) ^ 5 = 3 ^ (5 * a) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
        rw [h2, h3] at h1
        exact h1
      have h27 : (3:Nat) ^ (5 * a) * 3 ≤ 27 ^ (m + 1) := by
        have h1 : (3:Nat) ^ (5 * a + 1) ≤ 3 ^ (3 * (m + 1)) :=
          Arith.three_pow_le_three_pow hlt
        have h2 : (3:Nat) ^ (3 * (m + 1)) = 27 ^ (m + 1) := by
          rw [Nat.pow_mul, show (3:Nat) ^ 3 = 27 from rfl]
        have h3 : (3:Nat) ^ (5 * a + 1) = 3 ^ (5 * a) * 3 := by
          rw [Nat.pow_succ]
        rw [h3, h2] at h1
        exact h1
      have hgt : (27:Nat) ^ (m + 1) < 32 ^ (m + 1) :=
        Nat.pow_lt_pow_left (by omega) (by omega)
      have h3pos : 0 < (3:Nat) ^ (5 * a) := Arith.three_pow_pos _
      omega

/-- Every heavy residue carries weight at least `2 ^ ⌈3k/5⌉`. -/
theorem two_pow_le_weight_of_heavy {k r : Nat} (h : heavyB k r = true) :
    2 ^ ((3 * k + 4) / 5) ≤ 2 ^ oddCount r k := by
  have h1 : 2 ^ k ≤ 3 ^ oddCount r k := by simpa [heavyB] using h
  have h2 : 3 * k ≤ 5 * oddCount r k := three_mul_le_five_mul_of_heavy h1
  exact Arith.two_pow_le_two_pow (by omega)

/-! ## Light residues descend

The complement of the heavy set is where descent actually happens, and it
happens for every sufficiently large member of the class.  This is what makes
`heavyCount` the right object to bound: it is exactly the set of residues that
obstruct descent, with the finitely many small members of each class set
aside. -/

/-- **Light classes descend.**  If the multiplier of `r` at level `k` is smaller
than the modulus, then every member `2 ^ k · m + r` of its class with
`T^k(r) < m + r` drops strictly below itself in `k` accelerated steps. -/
theorem accOrbit_lt_of_light {k r m : Nat} (hlight : 3 ^ oddCount r k < 2 ^ k)
    (hm : acceleratedOrbit k r < m + r) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  rw [accOrbit_pow_two_mul_add]
  have hmul : 3 ^ oddCount r k * m + m ≤ 2 ^ k * m := by
    have h1 : 3 ^ oddCount r k + 1 ≤ 2 ^ k := by omega
    have h2 : (3 ^ oddCount r k + 1) * m ≤ 2 ^ k * m := Nat.mul_le_mul_right m h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    exact h2
  omega

/-- Every light residue therefore has a threshold past which its whole class
descends. -/
theorem exists_threshold_of_light {k r : Nat} (hlight : 3 ^ oddCount r k < 2 ^ k) :
    ∃ M : Nat, ∀ m : Nat, M ≤ m →
      acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  refine ⟨acceleratedOrbit k r + 1, fun m hm => ?_⟩
  exact accOrbit_lt_of_light hlight (by omega)

/-- Restated as a dichotomy: at every level each residue is either heavy, or its
class eventually descends. -/
theorem heavy_or_eventually_descends (k r : Nat) :
    heavyB k r = true ∨
      ∃ M : Nat, ∀ m : Nat, M ≤ m →
        acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  by_cases h : heavyB k r = true
  · exact Or.inl h
  · refine Or.inr (exists_threshold_of_light ?_)
    have : ¬ (2 ^ k ≤ 3 ^ oddCount r k) := by
      intro hc
      exact h (by simp [heavyB, hc])
    omega

/-! ## The density theorem -/

/-- The counted weight bound: `2 ^ ⌈3k/5⌉` times the number of heavy residues is
at most the total weight `3 ^ k`. -/
theorem mul_heavyCount_le (k : Nat) :
    2 ^ ((3 * k + 4) / 5) * heavyCount k ≤ 3 ^ k := by
  have h := mul_countRange_le (n := 2 ^ k) (w := 2 ^ ((3 * k + 4) / 5))
    (p := heavyB k) (f := fun r => 2 ^ oddCount r k)
    (fun i _ hi => two_pow_le_weight_of_heavy hi)
  have hw : sumRange (2 ^ k) (fun r => 2 ^ oddCount r k) = 3 ^ k := weightSum_eq k
  rw [heavyCount]
  omega

/-- **The density theorem.**  `heavyCount k ^ 5 * 8 ^ k ≤ 243 ^ k`.

Dividing by `(2 ^ k) ^ 5 * 8 ^ k = 256 ^ k` this says the heavy fraction `δ k`
satisfies `δ k ^ 5 ≤ (243/256) ^ k`, so the fraction of residue classes that
resist descent decays geometrically in `k`. -/
theorem heavyCount_pow_five (k : Nat) : heavyCount k ^ 5 * 8 ^ k ≤ 243 ^ k := by
  have hbase := mul_heavyCount_le k
  -- raise the counted weight bound to the fifth power
  have hpow : (2 ^ ((3 * k + 4) / 5) * heavyCount k) ^ 5 ≤ (3 ^ k) ^ 5 :=
    Nat.pow_le_pow_left hbase 5
  have hleft : (2 ^ ((3 * k + 4) / 5) * heavyCount k) ^ 5
      = 2 ^ (5 * ((3 * k + 4) / 5)) * heavyCount k ^ 5 := by
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm ((3 * k + 4) / 5) 5]
  have hright : ((3:Nat) ^ k) ^ 5 = 243 ^ k := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul, show (3:Nat) ^ 5 = 243 from rfl]
  rw [hleft, hright] at hpow
  -- and `2 ^ (5 ⌈3k/5⌉) ≥ 2 ^ (3k) = 8 ^ k`
  have h8 : (8:Nat) ^ k ≤ 2 ^ (5 * ((3 * k + 4) / 5)) := by
    have h1 : (8:Nat) ^ k = 2 ^ (3 * k) := by
      rw [Nat.pow_mul, show (2:Nat) ^ 3 = 8 from rfl]
    rw [h1]
    exact Arith.two_pow_le_two_pow (by omega)
  calc heavyCount k ^ 5 * 8 ^ k
      ≤ heavyCount k ^ 5 * 2 ^ (5 * ((3 * k + 4) / 5)) :=
        Nat.mul_le_mul_left _ h8
    _ = 2 ^ (5 * ((3 * k + 4) / 5)) * heavyCount k ^ 5 := Nat.mul_comm _ _
    _ ≤ 243 ^ k := hpow

/-- Restated against the total number of classes: the heavy fraction to the
fifth power is at most `(243/256) ^ k`. -/
theorem heavyCount_pow_five_ratio (k : Nat) :
    heavyCount k ^ 5 * 256 ^ k ≤ 243 ^ k * (2 ^ k) ^ 5 := by
  have hmain := heavyCount_pow_five k
  have h256 : (256:Nat) ^ k = 8 ^ k * (2 ^ k) ^ 5 := by
    rw [← Nat.pow_mul, Nat.mul_comm k 5, Nat.pow_mul, ← Nat.mul_pow,
      show (8:Nat) * 2 ^ 5 = 256 from rfl]
  rw [h256, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ hmain

/-- The heavy set never has full density: strictly fewer than all classes are
heavy once `k ≥ 1`. -/
theorem heavyCount_lt (k : Nat) (hk : 0 < k) : heavyCount k < 2 ^ k := by
  by_cases h : heavyCount k < 2 ^ k
  · exact h
  · exfalso
    have hge : 2 ^ k ≤ heavyCount k := by omega
    have hmain := heavyCount_pow_five k
    have hmono : (2 ^ k) ^ 5 ≤ heavyCount k ^ 5 := Nat.pow_le_pow_left hge 5
    have h256 : ((2:Nat) ^ k) ^ 5 * 8 ^ k = 256 ^ k := by
      rw [← Nat.pow_mul, Nat.mul_comm k 5, Nat.pow_mul, ← Nat.mul_pow,
        show (2:Nat) ^ 5 * 8 = 256 from rfl]
    have hlt : (243:Nat) ^ k < 256 ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
    have hchain : (256:Nat) ^ k ≤ heavyCount k ^ 5 * 8 ^ k := by
      rw [← h256]
      exact Nat.mul_le_mul_right _ hmono
    omega

/-! ## The exceptional set is never empty

The density theorem says the heavy classes thin out.  It does not say they
disappear, and they never do. -/

/-- The residue `2 ^ k − 1` is heavy at every level: its multiplier is `3 ^ k`. -/
theorem heavy_two_pow_sub_one {k : Nat} (_hk : 0 < k) : heavyB k (2 ^ k - 1) = true := by
  have hcount : oddCount (2 ^ k - 1) k = k := Obstruction.oddCount_two_pow_sub_one k
  have hle : (2:Nat) ^ k ≤ 3 ^ k := Arith.two_pow_le_three_pow k
  simp [heavyB, hcount, hle]

/-- Consequently the heavy count is positive at every level. -/
theorem heavyCount_pos {k : Nat} (hk : 0 < k) : 0 < heavyCount k := by
  have hmem : heavyB k (2 ^ k - 1) = true := heavy_two_pow_sub_one hk
  have hlt : 2 ^ k - 1 < 2 ^ k := by
    have := Arith.two_pow_pos k
    omega
  have hle : (if heavyB k (2 ^ k - 1) then 1 else 0) ≤ heavyCount k :=
    le_sumRange (n := 2 ^ k) (fun i => if heavyB k i then 1 else 0) hlt
  rw [hmem] at hle
  simp only [if_pos] at hle
  omega

/-! ## Concrete values

The bound is not vacuous: these are the actual heavy counts. -/

theorem heavyCount_one : heavyCount 1 = 1 := by decide
theorem heavyCount_two : heavyCount 2 = 1 := by decide
theorem heavyCount_three : heavyCount 3 = 4 := by decide
theorem heavyCount_four : heavyCount 4 = 5 := by decide
theorem heavyCount_five : heavyCount 5 = 6 := by decide

set_option maxRecDepth 4000 in
theorem heavyCount_six : heavyCount 6 = 22 := by decide

set_option maxRecDepth 8000 in
theorem heavyCount_seven : heavyCount 7 = 29 := by decide

set_option maxRecDepth 16000 in
/-- At modulus `256`, only `37` of `256` classes are heavy. -/
theorem heavyCount_eight : heavyCount 8 = 37 := by decide

/-- **The gap between density zero and emptiness.**  For every `k` the heavy set
is nonempty yet vanishingly sparse.  This is precisely why the density theorem,
though sharp, cannot settle the conjecture. -/
theorem heavy_nonempty_but_sparse {k : Nat} (hk : 0 < k) :
    0 < heavyCount k ∧ heavyCount k ^ 5 * 8 ^ k ≤ 243 ^ k :=
  ⟨heavyCount_pos hk, heavyCount_pow_five k⟩

end Density
end Collatz
