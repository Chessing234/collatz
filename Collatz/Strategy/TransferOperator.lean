import Collatz.Accelerated
import Collatz.Core.Sum

/-!
# The transfer operator of the accelerated map, and what it can never do

Every potential-function attempt in this development so far has been *forward*: a
rank `φ` compared at `x` and at `T x`.  This file introduces the adjoint object,
the **transfer operator** (Ruelle–Perron–Frobenius operator) of the accelerated
map `T`, which sums over *all inverse branches at once*:

`(L f)(x) = f (2 x) + [3 ∣ 2x − 1] · f ((2x − 1) / 3)`.

The two summands are exactly the two possible `T`-preimages of `x`: the even
preimage `2x`, always present, and the odd preimage `(2x−1)/3`, present iff
`x ≡ 2 (mod 3)`.  The generalisation to `3x + d` is `transferD` below; the branch
guard is `d ≤ 2x ∧ 3 ∣ 2x − d`, which for `d` coprime to `3` is the single
congruence `2x ≡ d (mod 3)` — so the *branching pattern* depends only on
`d mod 3`, while the *branch map* `x ↦ (2x − d)/3` depends on `d` itself.

The programme this object suggests is: find `f > 0` and `λ < 1` with `L f ≤ λ f`.
Such an `f` would be a Lyapunov certificate obtained without ever ranking a
forward step, so none of the forward no-go theorems
(`AnyModulusRanking.no_ranking_any_modulus`, `NoFiniteRanking.no_class_ranking`,
`JointRank.no_joint_class_ranking`) applies to it directly.

**This file proves the programme is empty.**  Two independent obstructions.

## 1.  Mass conservation

`T` is a *function*: every `y` has exactly one image, so the inverse branches
partition `ℕ`, and summing `L f` over a large enough window recovers the whole
sum of `f`:

`Σ_{y < 2N} f y ≤ Σ_{x < 3N} (L f) x`   (`sum_le_sum_transfer`).

Hence if `f` is supported in `[0, N)` and `q · (L f) x ≤ p · f x` pointwise with
`p < q` — that is, `L f ≤ (p/q) · f` with `p/q < 1` — then

`q · S ≤ Σ q · (L f) ≤ Σ p · f = p · S`,  so  `S = 0`  (`no_summable_subeigen`).

**No summable positive sub-eigenfunction with eigenvalue `< 1` exists**, and the
proof is one line of bookkeeping: the operator preserves total mass, so it cannot
contract it.  This kills the naive form of the programme outright.

## 2.  The inequality is a forward rank in disguise, and its only content is the
absence of cycles

The pointwise inequality `q · (L f) x ≤ p · f x` implies, dropping the branch not
taken, `q · f y ≤ p · f (T y)` for **every** `y` (`forward_step`) — the even
preimage gives it at even `y`, the odd preimage at odd `y`.  So `f` must grow by
the factor `q/p > 1` at every forward step: `f` is exactly the exponential of a
forward ranking function with a uniform geometric rate.  The transfer operator is
therefore *not* a new kind of certificate; it is a forward rank in adjoint
clothing, with one extra demand (the two branches must fit in the budget
*together*, not merely separately).

Iterating gives `q^k · f y ≤ p^k · f (T^k y)` (`forward_orbit`), so on a cycle
`T^k y = y` the two sides collide and `f y = 0` (`cycle_forces_zero`).  In
particular `f 1 = 0` from the trivial cycle `1 → 2 → 1` (`fixes_one`), so a
strictly positive `f` cannot exist on any set containing a cycle, and — this is
the point — a positive `f` on the complement of the trivial cycle exists **iff**
there is no other cycle: the witness in the positive direction is
`f y = (p/q)^{s y}` with `s y` the number of steps from `y` to `1`, available
exactly when that quantity is finite.  The operator restates the problem rather
than attacking it.

## 3.  `d`-sensitivity: real, and useless

`cycle_forces_zero_D` is stated for the general `3x + d` map, and
`no_positive_seven` instantiates it at `d = 7`, `y = 5`, `k = 4`: the genuine
cycle `5 → 11 → 20 → 10 → 5` forces `f 5 = 0`.  So `L_d` does distinguish `d = 1`
from `d = 7` — but through the cycle, which is the thing to be proved.  The
operator sees `d` only as much as the answer does.  Weights cannot repair this:
for a weighted operator the sub-eigen inequality along a cycle reads
`Π_{y ∈ C} w y ≤ (p/q)^{|C|}`, a condition on the cycle's weight product, so a
`d`-sensitive weight is a `d`-sensitive *cycle invariant* — and the soundness
filter (`C (w, d) = d · C (w, 1)`) refuses any weight built from the word.

## Truncations are vacuous, and not for the expected reason

Restricting to `{3, …, N}` (Dirichlet: `f = 0` outside) makes `L` a matrix each of
whose **columns** has at most one nonzero entry, because `T` is a function.  Such
a matrix is nilpotent as soon as its digraph is acyclic, which for `{3, …, N}` is
exactly the verified range.  Nilpotent means the optimal `λ` is `0`, approached by
`f y = c ^ (e y)` with `e` the exit time and `λ = 2c`: computationally the maximum
exit time is `21, 52, 110, 141` for `N = 10², 10³, 10⁴, 10⁵`.  So the truncated
linear programme does not degrade towards `1`; it collapses to `0`, and its
optimal value certifies *precisely* "no cycle inside the truncation" and nothing
more.
-/

namespace Collatz
namespace TransferOperator

open _root_.Collatz.Sum

/-! ## The maps and the operator -/

/-- The accelerated `3x + d` map: `n / 2` for even `n`, `(3n + d) / 2` for odd. -/
def stepD (d n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + d) / 2

/-- At `d = 1` this is the development's accelerated map. -/
theorem stepD_one (n : Nat) : stepD 1 n = acceleratedStep n := rfl

/-- Iterating `stepD`. -/
def orbitD (d : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => orbitD d k (stepD d n)

@[simp] theorem orbitD_zero (d n : Nat) : orbitD d 0 n = n := rfl

theorem orbitD_succ (d k n : Nat) : orbitD d (k + 1) n = orbitD d k (stepD d n) := rfl

/-- **The transfer operator of the `3x + d` map.**  `(L f)(x)` sums `f` over the
full `stepD d`-preimage of `x`: the even preimage `2x`, always there, and the odd
preimage `(2x − d) / 3`, there exactly when `d ≤ 2x` and `3 ∣ 2x − d`. -/
def transferD (d : Nat) (f : Nat → Nat) (x : Nat) : Nat :=
  f (2 * x) + (if d ≤ 2 * x ∧ (2 * x - d) % 3 = 0 then f ((2 * x - d) / 3) else 0)

/-- The transfer operator of the accelerated `3x + 1` map. -/
def transfer (f : Nat → Nat) (x : Nat) : Nat := transferD 1 f x

/-- The odd branch of `L` is present exactly on `x ≡ 2 (mod 3)`, `x ≥ 1`. -/
theorem transfer_eq (f : Nat → Nat) (x : Nat) (hx : 0 < x) :
    transfer f x = f (2 * x) + (if x % 3 = 2 then f ((2 * x - 1) / 3) else 0) := by
  unfold transfer transferD
  by_cases h : x % 3 = 2
  · have h1 : 1 ≤ 2 * x ∧ (2 * x - 1) % 3 = 0 := by omega
    simp [h1, h]
  · have h1 : ¬ (1 ≤ 2 * x ∧ (2 * x - 1) % 3 = 0) := by omega
    simp [h1, h]

/-! ## Part 1: mass conservation

`T` is a function, so the inverse branches partition `ℕ` and `L` cannot lose
mass.  The counting below is the finite form of `Σ (L f) = Σ f`. -/

/-- Strict monotonicity of multiplication by a positive factor (no Mathlib). -/
theorem mul_lt_mul_pos {a b c : Nat} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  have hle : c * (a + 1) ≤ c * b := Nat.mul_le_mul_left c h
  rw [Nat.mul_add, Nat.mul_one] at hle
  omega

/-- A sum over `[0, 2n)` regrouped into consecutive pairs. -/
theorem sumRange_pair (n : Nat) (f : Nat → Nat) :
    sumRange (2 * n) f = sumRange n (fun i => f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h, sumRange_succ, sumRange_succ, ih, sumRange_succ]
    omega

/-- A sum over `[0, 3n)` regrouped into consecutive triples. -/
theorem sumRange_triple (n : Nat) (f : Nat → Nat) :
    sumRange (3 * n) f = sumRange n (fun i => f (3 * i) + f (3 * i + 1) + f (3 * i + 2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : 3 * (n + 1) = ((3 * n + 1) + 1) + 1 := by omega
    rw [h, sumRange_succ, sumRange_succ, sumRange_succ, ih, sumRange_succ]
    omega

/-- A sum does not see the range beyond the support. -/
theorem sumRange_eq_of_vanish {N M : Nat} {f : Nat → Nat} (h : N ≤ M)
    (hsupp : ∀ x, N ≤ x → f x = 0) : sumRange M f = sumRange N f := by
  have hM : M = N + (M - N) := by omega
  rw [hM, sumRange_split]
  have hzero : sumRange (M - N) (fun i => f (N + i)) = sumRange (M - N) (fun _ => 0) :=
    sumRange_congr (fun i _ => hsupp (N + i) (by omega))
  rw [hzero, sumRange_const]
  omega

/-- **Mass conservation, finite form.**  Every `y < 2N` is the preimage of some
`x < 3N` under one of the two branches, and the branches are disjoint, so the
window `[0, 3N)` of `L f` already contains the whole mass of `f` on `[0, 2N)`. -/
theorem sum_le_sum_transfer (f : Nat → Nat) (N : Nat) :
    sumRange (2 * N) f ≤ sumRange (3 * N) (transfer f) := by
  have hsplit : sumRange (3 * N) (transfer f)
      = sumRange (3 * N) (fun x => f (2 * x))
        + sumRange (3 * N) (fun x =>
            if 1 ≤ 2 * x ∧ (2 * x - 1) % 3 = 0 then f ((2 * x - 1) / 3) else 0) := by
    rw [← sumRange_add]
    rfl
  -- the even branch already covers all even `y < 2N`
  have heven : sumRange N (fun i => f (2 * i)) ≤ sumRange (3 * N) (fun x => f (2 * x)) :=
    sumRange_mono_length _ (by omega)
  -- the odd branch, read at the indices `x = 3 i + 2`, covers all odd `y < 2N`
  have hodd : sumRange N (fun i => f (2 * i + 1))
      ≤ sumRange (3 * N) (fun x =>
          if 1 ≤ 2 * x ∧ (2 * x - 1) % 3 = 0 then f ((2 * x - 1) / 3) else 0) := by
    rw [sumRange_triple]
    refine sumRange_le (fun i _ => ?_)
    have hcond : 1 ≤ 2 * (3 * i + 2) ∧ (2 * (3 * i + 2) - 1) % 3 = 0 := by omega
    have hval : (2 * (3 * i + 2) - 1) / 3 = 2 * i + 1 := by omega
    have hif : (if 1 ≤ 2 * (3 * i + 2) ∧ (2 * (3 * i + 2) - 1) % 3 = 0
        then f ((2 * (3 * i + 2) - 1) / 3) else 0) = f (2 * i + 1) := by
      rw [if_pos hcond, hval]
    omega
  rw [hsplit, sumRange_pair, sumRange_add]
  omega

/-- **No summable positive sub-eigenfunction.**  If `f` is supported on `[0, N)`
and satisfies `q · (L f) ≤ p · f` pointwise with `p < q` — the integral form of
`L f ≤ λ f` with `λ = p / q < 1` — then `f` is identically zero.

The transfer operator preserves total mass because `T` is a function, so it
cannot multiply the mass by `λ < 1` unless the mass is `0`. -/
theorem no_summable_subeigen {p q N : Nat} (hpq : p < q) (f : Nat → Nat)
    (hsupp : ∀ x, N ≤ x → f x = 0)
    (hsub : ∀ x, q * transfer f x ≤ p * f x) : ∀ x, f x = 0 := by
  have h2 : sumRange (2 * N) f = sumRange N f := sumRange_eq_of_vanish (by omega) hsupp
  have h3 : sumRange (3 * N) f = sumRange N f := sumRange_eq_of_vanish (by omega) hsupp
  have hmass := sum_le_sum_transfer f N
  have hq : q * sumRange (3 * N) (transfer f) = sumRange (3 * N) (fun x => q * transfer f x) := by
    rw [sumRange_const_mul]
  have hp : p * sumRange (3 * N) f = sumRange (3 * N) (fun x => p * f x) := by
    rw [sumRange_const_mul]
  have hle : sumRange (3 * N) (fun x => q * transfer f x)
      ≤ sumRange (3 * N) (fun x => p * f x) := sumRange_le (fun i _ => hsub i)
  have hchain : q * sumRange N f ≤ p * sumRange N f := by
    calc q * sumRange N f
        = q * sumRange (2 * N) f := by rw [h2]
      _ ≤ q * sumRange (3 * N) (transfer f) := Nat.mul_le_mul_left _ hmass
      _ = sumRange (3 * N) (fun x => q * transfer f x) := hq
      _ ≤ sumRange (3 * N) (fun x => p * f x) := hle
      _ = p * sumRange (3 * N) f := hp.symm
      _ = p * sumRange N f := by rw [h3]
  have hS : sumRange N f = 0 := by
    rcases Nat.eq_zero_or_pos (sumRange N f) with h0 | h0
    · exact h0
    · have hlt : sumRange N f * p < sumRange N f * q := mul_lt_mul_pos hpq h0
      have e1 : sumRange N f * p = p * sumRange N f := Nat.mul_comm _ _
      have e2 : sumRange N f * q = q * sumRange N f := Nat.mul_comm _ _
      omega
  intro x
  by_cases hx : x < N
  · have := le_sumRange f hx
    omega
  · exact hsupp x (by omega)

/-! ## Part 2: the inequality is a forward rank, and only cycles obstruct it -/

/-- The even inverse branch is one of the summands. -/
theorem le_transferD_even (d : Nat) (f : Nat → Nat) (x : Nat) : f (2 * x) ≤ transferD d f x := by
  unfold transferD
  omega

/-- The odd inverse branch is the other summand: for odd `y` and odd `d`, `f y`
is one of the terms of `(L f) (stepD d y)`. -/
theorem le_transferD_odd {d y : Nat} (f : Nat → Nat) (hd : d % 2 = 1) (hy : y % 2 = 1) :
    f y ≤ transferD d f (stepD d y) := by
  have hstep : stepD d y = (3 * y + d) / 2 := by
    unfold stepD
    simp [hy]
  have h2 : 2 * ((3 * y + d) / 2) = 3 * y + d := by omega
  have hcond : d ≤ 2 * ((3 * y + d) / 2) ∧ (2 * ((3 * y + d) / 2) - d) % 3 = 0 := by omega
  have hval : (2 * ((3 * y + d) / 2) - d) / 3 = y := by omega
  have hif : (if d ≤ 2 * ((3 * y + d) / 2) ∧ (2 * ((3 * y + d) / 2) - d) % 3 = 0
      then f ((2 * ((3 * y + d) / 2) - d) / 3) else 0) = f y := by
    rw [if_pos hcond, hval]
  unfold transferD
  rw [hstep]
  omega

/-- **The forward reading.**  A sub-eigenfunction of the transfer operator grows
by the factor `q / p` at every forward step of the map: for odd `d`, the
inequality `q · (L f) ≤ p · f` is exactly a forward ranking condition. -/
theorem forward_stepD {p q d : Nat} (hd : d % 2 = 1) (f : Nat → Nat)
    (hsub : ∀ x, q * transferD d f x ≤ p * f x) (y : Nat) :
    q * f y ≤ p * f (stepD d y) := by
  by_cases hy : y % 2 = 0
  · have hstep : stepD d y = y / 2 := by unfold stepD; simp [hy]
    have hy2 : 2 * (y / 2) = y := by omega
    have h1 : f (2 * (y / 2)) ≤ transferD d f (y / 2) := le_transferD_even d f (y / 2)
    have h2 := hsub (y / 2)
    rw [hy2] at h1
    rw [hstep]
    calc q * f y ≤ q * transferD d f (y / 2) := Nat.mul_le_mul_left _ h1
      _ ≤ p * f (y / 2) := h2
  · have hy1 : y % 2 = 1 := by omega
    have h1 := le_transferD_odd f hd hy1
    have h2 := hsub (stepD d y)
    calc q * f y ≤ q * transferD d f (stepD d y) := Nat.mul_le_mul_left _ h1
      _ ≤ p * f (stepD d y) := h2

/-- The forward reading, iterated: `q ^ k · f y ≤ p ^ k · f (T^k y)`. -/
theorem forward_orbitD {p q d : Nat} (hd : d % 2 = 1) (f : Nat → Nat)
    (hsub : ∀ x, q * transferD d f x ≤ p * f x) (k : Nat) :
    ∀ y : Nat, q ^ k * f y ≤ p ^ k * f (orbitD d k y) := by
  induction k with
  | zero => intro y; simp
  | succ k ih =>
    intro y
    have h1 := forward_stepD hd f hsub y
    have h2 := ih (stepD d y)
    have hpow : q ^ (k + 1) * f y = q ^ k * (q * f y) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have hstep : q ^ k * (q * f y) ≤ q ^ k * (p * f (stepD d y)) := Nat.mul_le_mul_left _ h1
    have hcomm : q ^ k * (p * f (stepD d y)) = p * (q ^ k * f (stepD d y)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (q ^ k) p, Nat.mul_assoc]
    have hnext : p * (q ^ k * f (stepD d y)) ≤ p * (p ^ k * f (orbitD d k (stepD d y))) :=
      Nat.mul_le_mul_left _ h2
    have hfin : p * (p ^ k * f (orbitD d k (stepD d y))) = p ^ (k + 1) * f (orbitD d (k + 1) y) := by
      rw [orbitD_succ, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm p (p ^ k)]
    omega

/-- Positivity of powers, proved locally (no Mathlib). -/
theorem pow_pos_of_pos {q : Nat} (hq : 0 < q) : ∀ k : Nat, 0 < q ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih hq

/-- Strict monotonicity of `k`-th powers, proved locally (no Mathlib). -/
theorem pow_lt_pow_of_lt {p q : Nat} (h : p < q) : ∀ k : Nat, 0 < k → p ^ k < q ^ k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simpa using h
    · have hprev := ih hk
      have hq : 0 < q ^ k := pow_pos_of_pos (by omega) k
      have hstep : q ^ k * p < q ^ k * q := mul_lt_mul_pos h hq
      have hmono : p ^ k * p ≤ q ^ k * p := Nat.mul_le_mul_right _ (Nat.le_of_lt hprev)
      have e1 : p ^ (k + 1) = p ^ k * p := Nat.pow_succ p k
      have e2 : q ^ (k + 1) = q ^ k * q := Nat.pow_succ q k
      omega

/-- **A cycle kills the certificate.**  If `y` lies on a `stepD d`-cycle of
length `k > 0`, every sub-eigenfunction with ratio `p / q < 1` vanishes at `y`. -/
theorem cycle_forces_zero_D {p q d k y : Nat} (hd : d % 2 = 1) (hpq : p < q) (hk : 0 < k)
    (f : Nat → Nat) (hsub : ∀ x, q * transferD d f x ≤ p * f x)
    (hcyc : orbitD d k y = y) : f y = 0 := by
  have h := forward_orbitD hd f hsub k y
  rw [hcyc] at h
  have hlt := pow_lt_pow_of_lt hpq k hk
  rcases Nat.eq_zero_or_pos (f y) with h0 | h0
  · exact h0
  · have hstrict : f y * p ^ k < f y * q ^ k := mul_lt_mul_pos hlt h0
    have e1 : f y * p ^ k = p ^ k * f y := Nat.mul_comm _ _
    have e2 : f y * q ^ k = q ^ k * f y := Nat.mul_comm _ _
    omega

/-- The same statement for the development's accelerated map. -/
theorem cycle_forces_zero {p q k y : Nat} (hpq : p < q) (hk : 0 < k)
    (f : Nat → Nat) (hsub : ∀ x, q * transfer f x ≤ p * f x)
    (hcyc : orbitD 1 k y = y) : f y = 0 :=
  cycle_forces_zero_D (by decide) hpq hk f hsub hcyc

/-- **The trivial cycle already bites.**  Any sub-eigenfunction of the `3x + 1`
transfer operator vanishes at `1`, because `1 → 2 → 1`. -/
theorem fixes_one {p q : Nat} (hpq : p < q) (f : Nat → Nat)
    (hsub : ∀ x, q * transfer f x ≤ p * f x) : f 1 = 0 :=
  cycle_forces_zero (k := 2) hpq (by decide) f hsub (by rfl)

/-- … and at `2`. -/
theorem fixes_two {p q : Nat} (hpq : p < q) (f : Nat → Nat)
    (hsub : ∀ x, q * transfer f x ≤ p * f x) : f 2 = 0 :=
  cycle_forces_zero (k := 2) hpq (by decide) f hsub (by rfl)

/-- **The `d`-sensitivity, and its uselessness.**  For `d = 7` the genuine cycle
`5 → 11 → 20 → 10 → 5` forces every sub-eigenfunction to vanish at `5`.  So the
transfer operator does separate `d = 1` from `d = 7` — but only through the
cycle, which is exactly what one wanted to prove. -/
theorem no_positive_seven {p q : Nat} (hpq : p < q) (f : Nat → Nat)
    (hsub : ∀ x, q * transferD 7 f x ≤ p * f x) : f 5 = 0 :=
  cycle_forces_zero_D (d := 7) (k := 4) (by decide) hpq (by decide) f hsub (by rfl)

end TransferOperator
end Collatz
