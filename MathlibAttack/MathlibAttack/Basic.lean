import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# The Mathlib attack branch — isolated from the no-Mathlib development

This directory is a **separate Lake project**.  The root `Collatz` library remains
Mathlib-free; nothing here is imported by it and nothing there is imported by this.

Everything below is proved from scratch against Mathlib, as an independent
cross-check of the hand-rolled development.  No `sorry`, no `axiom`,
no `native_decide`.
-/

namespace MathlibAttack

instance instNeZeroTwoPow (N : ℕ) : NeZero ((2 : ℕ) ^ N) := ⟨by positivity⟩

/-! ## The maps -/

/-- The Collatz step. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The accelerated (Terras) step `T(n) = n/2` for even `n`, `(3n+1)/2` for odd. -/
def Tacc (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The Syracuse (odd-to-odd) map: strip every factor of two from `3n+1`.

`Nat.divMaxPow` lives in `Mathlib/Data/Nat/MaxPowDiv.lean`, where `padicValNat` is
literally `(Nat.maxPowDvdDiv p n).fst`.  **It does not reduce in the kernel** —
see the note below `two_pow_dvd_iff`. -/
def S (n : ℕ) : ℕ := Nat.divMaxPow (3 * n + 1) 2

/-- The valuation-flavoured description of `S`, matching the usual definition
`S n = (3n+1) / 2 ^ v₂(3n+1)`. -/
theorem S_eq_div_pow_padicValNat (n : ℕ) :
    S n = (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1) := by
  have h := Nat.divMaxPow_mul_pow_padicValNat 2 (3 * n + 1)
  have hpos : 0 < (2 : ℕ) ^ padicValNat 2 (3 * n + 1) := by positivity
  exact (Nat.div_eq_of_eq_mul_left hpos h.symm).symm

/-- `S n` is odd for every `n`: the definition strips *all* factors of two. -/
theorem S_odd (n : ℕ) : S n % 2 = 1 := by
  have hne : (3 * n + 1) ≠ 0 := by omega
  have h := Nat.not_dvd_divMaxPow (p := 2) (n := 3 * n + 1) (by norm_num) hne
  simp only [S]
  omega


/-! ## What sees `v₂(3n+1)`?

This is the question the branch exists to answer.  Mathlib's valuation API *does*
give leverage the hand-rolled development lacks, and the leverage is concentrated
in exactly two lemmas:

* `Nat.pow_dvd_iff_le_padicValNat` turns the valuation into a **divisibility**,
  an `iff` in both directions, with no side condition beyond `n ≠ 0`;
* `ZMod.isUnit_iff_coprime` makes `3` a unit mod `2 ^ k`.

Composing them, `v₂(3n+1) ≥ k` is *exactly* membership in a single residue class
mod `2 ^ k`, and the class is named explicitly as `-(3 : ZMod (2^k))⁻¹`.  That is
the object which sees the exact contraction.

**Honest counterweight, recorded because it is load-bearing:** `padicValNat` is
*not* kernel-reducible.  `Nat.maxPowDvdDiv` is defined by well-founded recursion,
so `padicValNat 2 22 = 1` fails by `rfl`, by `decide` and by `norm_num` — there is
no `norm_num` extension for `padicValNat` anywhere in Mathlib.  Concrete values
must go through `Nat.maxPowDvdDiv_of_pow_mul_eq` with an explicit witness, as in
`valuation_of_witness` below.  So on the *computational* side the no-Mathlib
branch's hand-rolled, structurally recursive valuation is strictly better. -/

/-- Divisibility form of the valuation, specialised to `3n+1`. -/
theorem two_pow_dvd_iff (k n : ℕ) :
    2 ^ k ∣ (3 * n + 1) ↔ k ≤ padicValNat 2 (3 * n + 1) :=
  Nat.pow_dvd_iff_le_padicValNat (by norm_num) (by omega)

/-- `3` is a unit modulo `2 ^ k`, and its inverse satisfies `3 * 3⁻¹ = 1`. -/
theorem three_mul_inv_zmod (k : ℕ) :
    (3 : ZMod (2 ^ k)) * (3 : ZMod (2 ^ k))⁻¹ = 1 := by
  have hc : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by decide)
  have := ZMod.coe_mul_inv_eq_one (n := 2 ^ k) 3 hc
  simpa using this

/-- **The `v₂(3n+1) ≥ k` criterion is one residue class mod `2 ^ k`.**

`v₂(3n+1) ≥ k` holds exactly when `n ≡ −3⁻¹ (mod 2 ^ k)`.  So the deep-valuation
events are nested arithmetic progressions of ratio `2`, and the whole `2`-adic
structure of the Syracuse map is visible in `ZMod (2 ^ k)` alone. -/
theorem le_padicValNat_iff_residue (k n : ℕ) :
    k ≤ padicValNat 2 (3 * n + 1) ↔ (n : ZMod (2 ^ k)) = -(3 : ZMod (2 ^ k))⁻¹ := by
  rw [← two_pow_dvd_iff, ← ZMod.natCast_eq_zero_iff]
  push_cast
  have h3 := three_mul_inv_zmod k
  constructor
  · intro h
    linear_combination (3 : ZMod (2 ^ k))⁻¹ * h - (n : ZMod (2 ^ k)) * h3
  · intro h
    linear_combination (3 : ZMod (2 ^ k)) * h - h3

/-- The nesting is strict in the sense that the exact-valuation event
`v₂(3n+1) = k` is the set difference of the class mod `2^k` and the class mod
`2^(k+1)`. -/
theorem padicValNat_eq_iff (k n : ℕ) :
    padicValNat 2 (3 * n + 1) = k ↔
      ((n : ZMod (2 ^ k)) = -(3 : ZMod (2 ^ k))⁻¹ ∧
        (n : ZMod (2 ^ (k + 1))) ≠ -(3 : ZMod (2 ^ (k + 1)))⁻¹) := by
  simp only [ne_eq, ← le_padicValNat_iff_residue]
  omega

/-- Concrete values of `S` and of `v₂(3n+1)` need an explicit witness, because
`padicValNat` does not reduce.  This is the working substitute for `decide`. -/
theorem valuation_of_witness {n k m : ℕ} (h : 2 ^ k * m = 3 * n + 1) (hm : m % 2 = 1) :
    S n = m ∧ padicValNat 2 (3 * n + 1) = k := by
  have hn : (3 * n + 1) ≠ 0 := by omega
  have hl : ¬ (2 ∣ m) := by omega
  have hmax := Nat.maxPowDvdDiv_of_pow_mul_eq (p := 2) hn h hl
  refine ⟨?_, ?_⟩
  · simp [S, Nat.divMaxPow, hmax]
  · simp [padicValNat, hmax]

example : S 7 = 11 := (valuation_of_witness (k := 1) (m := 11) (by norm_num) (by norm_num)).1

example : padicValNat 2 (3 * 5 + 1) = 4 :=
  (valuation_of_witness (n := 5) (k := 4) (m := 1) (by norm_num) (by norm_num)).2


/-- Concrete form of the criterion at `k = 1`: the **exact contraction**
`S n = (3n+1)/2` — one halving and no more — happens precisely on `n ≡ 3 (mod 4)`.

This is the `omega`-friendly face of `le_padicValNat_iff_residue`: because
`two_pow_dvd_iff` is a divisibility, `omega` can finish from it directly, with no
`ZMod` reasoning at all. -/
theorem padicValNat_eq_one_iff (n : ℕ) :
    padicValNat 2 (3 * n + 1) = 1 ↔ n % 4 = 3 := by
  have h1 := two_pow_dvd_iff 1 n
  have h2 := two_pow_dvd_iff 2 n
  norm_num at h1 h2
  omega


/-- And `v₂(3n+1) ≥ 2` — at least two halvings — is `n ≡ 1 (mod 4)`. -/
theorem two_le_padicValNat_iff (n : ℕ) :
    2 ≤ padicValNat 2 (3 * n + 1) ↔ n % 4 = 1 := by
  have h2 := two_pow_dvd_iff 2 n
  norm_num at h2
  omega


/-! ### Lifting the exponent: the one thing the no-Mathlib branch cannot build

`Mathlib/NumberTheory/Multiplicity.lean` carries the full `p = 2` lifting-the-exponent
package.  It gives an *exact formula* for `v₂(3 ^ a − 1)` — a quantity the
hand-rolled development can only bound.  This is the sharpest concrete leverage
found in this round. -/

theorem padicValNat_three_pow_sub_one {a : ℕ} (ha : a ≠ 0) (heven : Even a) :
    padicValNat 2 (3 ^ a - 1) = padicValNat 2 a + 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := padicValNat.pow_two_sub_one (x := 3) (n := a) (by norm_num) (by decide) ha heven
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    have e : (3 + 1 : ℕ) = 2 ^ 2 := by norm_num
    rw [e, padicValNat.prime_pow]
  have h2 : padicValNat 2 (3 - 1) = 1 := by
    have e : (3 - 1 : ℕ) = 2 ^ 1 := by norm_num
    rw [e, padicValNat.prime_pow]
  omega


private theorem nine_pow_mod_four (m : ℕ) : 9 ^ m % 4 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ]; omega

/-! ## The affine law

`2 ^ j · Tacc^[j] x = 3 ^ a · x + C`, with `a` the number of odd steps and `C` an
explicit accumulator fed only by the odd steps.

Working in `ℤ` rather than `ℕ` is the first real difference from the no-Mathlib
development: there is no truncated subtraction, so the cycle equation below needs
**no** `3 ^ a < 2 ^ L` side hypothesis. -/

/-- Number of odd iterates among `x, Tacc x, …, Tacc^[j-1] x`. -/
def oddCount (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => oddCount x j + (if Tacc^[j] x % 2 = 1 then 1 else 0)

/-- The additive accumulator, fed only by odd steps: `C ↦ 3C + 2^j`. -/
def accC (x : ℕ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => if Tacc^[j] x % 2 = 1 then 3 * accC x j + 2 ^ j else accC x j

@[simp] theorem oddCount_zero (x : ℕ) : oddCount x 0 = 0 := rfl
@[simp] theorem accC_zero (x : ℕ) : accC x 0 = 0 := rfl

/-- **The affine law.**  `2 ^ j · Tacc^[j](x) = 3 ^ (oddCount x j) · x + accC x j`. -/
theorem affine (x : ℕ) : ∀ j : ℕ,
    (2 : ℤ) ^ j * (Tacc^[j] x : ℤ) = 3 ^ oddCount x j * (x : ℤ) + accC x j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    set y := Tacc^[j] x with hy
    have hstep : Tacc^[j + 1] x = Tacc y := by
      rw [hy, Function.iterate_succ_apply']
    by_cases h : y % 2 = 1
    · -- odd step
      have hval : Tacc y = (3 * y + 1) / 2 := by
        rw [Tacc, if_neg (by omega)]
      have hdouble : 2 * ((3 * y + 1) / 2) = 3 * y + 1 := by omega
      have hcount : oddCount x (j + 1) = oddCount x j + 1 := by
        simp [oddCount, ← hy, h]
      have hC : accC x (j + 1) = 3 * accC x j + 2 ^ j := by
        simp [accC, ← hy, h]
      have hZ : (2 : ℤ) * ((3 * y + 1) / 2 : ℕ) = 3 * (y : ℤ) + 1 := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdouble
      rw [hstep, hval, hcount, hC]
      have : (2 : ℤ) ^ (j + 1) * (((3 * y + 1) / 2 : ℕ) : ℤ)
           = 2 ^ j * (2 * (((3 * y + 1) / 2 : ℕ) : ℤ)) := by ring
      rw [this, hZ]
      have : (2 : ℤ) ^ j * (3 * (y : ℤ) + 1) = 3 * (2 ^ j * (y : ℤ)) + 2 ^ j := by ring
      rw [this, ih]
      ring
    · -- even step
      have h0 : y % 2 = 0 := by omega
      have hval : Tacc y = y / 2 := by rw [Tacc, if_pos h0]
      have hdouble : 2 * (y / 2) = y := by omega
      have hcount : oddCount x (j + 1) = oddCount x j := by
        simp [oddCount, ← hy, h]
      have hC : accC x (j + 1) = accC x j := by simp [accC, ← hy, h]
      have hZ : (2 : ℤ) * ((y / 2 : ℕ) : ℤ) = (y : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdouble
      rw [hstep, hval, hcount, hC]
      have : (2 : ℤ) ^ (j + 1) * (((y / 2 : ℕ)) : ℤ) = 2 ^ j * (2 * (((y / 2 : ℕ)) : ℤ)) := by
        ring
      rw [this, hZ, ih]

/-! ## The cycle equation

Over `ℤ` this is an unconditional `iff`. -/

/-- **The cycle equation.**  `x` is a point of an accelerated cycle of length `L`
exactly when `(2 ^ L − 3 ^ a) · x = accC x L`, where `a = oddCount x L`.

Unlike the `ℕ`-valued statement, this needs no hypothesis `3 ^ a < 2 ^ L`. -/
theorem cycle_iff (x L : ℕ) :
    Tacc^[L] x = x ↔ ((2 : ℤ) ^ L - 3 ^ oddCount x L) * (x : ℤ) = accC x L := by
  have h := affine x L
  constructor
  · intro hcyc
    rw [hcyc] at h
    linarith [h]
  · intro heq
    have : (2 : ℤ) ^ L * (Tacc^[L] x : ℤ) = 2 ^ L * (x : ℤ) := by
      rw [h]; linarith [heq]
    have h2 : (0 : ℤ) < 2 ^ L := by positivity
    have : ((Tacc^[L] x : ℕ) : ℤ) = ((x : ℕ) : ℤ) := by
      exact mul_left_cancel₀ (ne_of_gt h2) this
    exact_mod_cast this

/-! ## The Terras bijection

Parity words of length `N` correspond bijectively to residues mod `2 ^ N`.
The Mathlib proof is *conceptually different* from the hand-rolled one: we prove
injectivity from the affine law, then get surjectivity **for free** from
`Finite.injective_iff_bijective`, because `ZMod (2^N)` and `Fin N → Bool` have the
same cardinality.  The no-Mathlib branch has to construct the preimage explicitly. -/

/-- The parity word of `x` of length `N`. -/
def parity (x N : ℕ) : Fin N → Bool := fun i => decide (Tacc^[i.val] x % 2 = 1)

/-- The accumulator and the odd-step count are determined by the parity word.
(Both are defined by recursion reading only the parities.) -/
theorem oddCount_accC_congr {x y : ℕ} {N : ℕ} (h : parity x N = parity y N) :
    ∀ j ≤ N, oddCount x j = oddCount y j ∧ accC x j = accC y j := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j ≤ N := le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self j) hj)
    obtain ⟨hc, hC⟩ := ih hj'
    have hpar : (Tacc^[j] x % 2 = 1) ↔ (Tacc^[j] y % 2 = 1) := by
      have := congrFun h ⟨j, by omega⟩
      simpa [parity, decide_eq_decide] using this
    constructor
    · simp only [oddCount, hc]
      by_cases hx : Tacc^[j] x % 2 = 1
      · rw [if_pos hx, if_pos (hpar.mp hx)]
      · rw [if_neg hx, if_neg (fun hy => hx (hpar.mpr hy))]
    · simp only [accC, hC]
      by_cases hx : Tacc^[j] x % 2 = 1
      · rw [if_pos hx, if_pos (hpar.mp hx)]
      · rw [if_neg hx, if_neg (fun hy => hx (hpar.mpr hy))]

/-- **Terras, injectivity.**  Equal parity words of length `N` force congruence
mod `2 ^ N`.

The whole content is: the affine law makes `3 ^ a · (x − y)` divisible by `2 ^ N`,
and `3 ^ a` is a unit mod `2 ^ N`.  Mathlib supplies the cancellation as
`Nat.Coprime.dvd_of_dvd_mul_left`, so no hand-rolled `dvd_of_odd_mul` induction
is needed. -/
theorem parity_inj_mod {x y N : ℕ} (h : parity x N = parity y N) :
    (x : ZMod (2 ^ N)) = (y : ZMod (2 ^ N)) := by
  obtain ⟨hc, hC⟩ := oddCount_accC_congr h N le_rfl
  have hx := affine x N
  have hy := affine y N
  rw [hc, hC] at hx
  -- `2^N` divides `3^a * (x - y)` in `ℤ`
  have hdvd : ((2 : ℤ) ^ N) ∣ (3 : ℤ) ^ oddCount y N * ((x : ℤ) - (y : ℤ)) := by
    refine ⟨(Tacc^[N] x : ℤ) - (Tacc^[N] y : ℤ), ?_⟩
    have : (3 : ℤ) ^ oddCount y N * (x : ℤ) - 3 ^ oddCount y N * (y : ℤ)
         = 2 ^ N * (Tacc^[N] x : ℤ) - 2 ^ N * (Tacc^[N] y : ℤ) := by
      rw [hx, hy]; ring
    linarith [this]
  -- `3^a` is coprime to `2^N`
  have hcop : IsCoprime ((2 : ℤ) ^ N) ((3 : ℤ) ^ oddCount y N) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]
    decide
  have hdvd' : ((2 : ℤ) ^ N) ∣ ((x : ℤ) - (y : ℤ)) := hcop.dvd_of_dvd_mul_left hdvd
  have hcast : (((x : ℤ) - (y : ℤ) : ℤ) : ZMod (2 ^ N)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ N)).mpr (by exact_mod_cast hdvd')
  push_cast at hcast
  exact sub_eq_zero.mp (by simpa using hcast)

/-- The parity word as a function out of `ZMod (2 ^ N)`. -/
def parityOfResidue (N : ℕ) : ZMod (2 ^ N) → (Fin N → Bool) :=
  fun r => parity (r.val) N

/-- **The Terras bijection.** `r ↦ parity word of r` is a bijection from
`ZMod (2 ^ N)` onto all binary words of length `N`.

The Mathlib route is conceptually different from the hand-rolled one: prove
injectivity from the affine law, then read off surjectivity from
`Fintype.bijective_iff_injective_and_card`, since both sides have `2 ^ N` elements.
The no-Mathlib branch has to construct the preimage explicitly. -/
theorem terras_bijective (N : ℕ) : Function.Bijective (parityOfResidue N) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h : parity a.val N = parity b.val N := hab
    have h2 := parity_inj_mod h
    simpa [ZMod.natCast_val, ZMod.cast_id] using h2
  · simp [ZMod.card]

/-- Consequently every binary word of length `N` is realised by some residue —
Terras' surjectivity, obtained by counting rather than by construction. -/
theorem terras_surjective (N : ℕ) (w : Fin N → Bool) :
    ∃ r : ZMod (2 ^ N), parity (r.val) N = w :=
  (terras_bijective N).2 w

end MathlibAttack
