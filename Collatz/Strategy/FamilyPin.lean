import Collatz.Strategy.GenBlock

/-!
# `(3, 2)` is pinned by two independent exact constraints

`GenBlock` generalized the block law to `3n + c` for free odd `c`.  This file frees
the other two parameters: `n ↦ n/q` when `q ∣ n`, else `n ↦ (p·n + c)/q`, and asks
what the structure forces.  Two unrelated mechanisms each cut the family down, and
they agree only at Collatz.

## 1. Totality of the branch forces `q = 2`

For the second branch to be *exact* — an integer for every residue not divisible by
`q`, so that the map is total and deterministic with no case analysis — one needs
`q ∣ p·n + c` for all `n ≢ 0`.  Comparing `n = 1, 2`:

* **`q ≥ 3` forces `p ≡ 0` and `c ≡ 0 (mod q)`** (`q_ge_three_forces_p_zero`,
  `q_ge_three_forces_c_zero`), which is degenerate — the branch is then `p'n + c'`
  and the division never happens.
* **`q = 2` is the unique base admitting a genuine solution**, and there `p` and `c`
  must both be odd (`q_two_nontrivial`, `q_two_condition`).

So `q = 2` is *forced*, not assumed.  Verified independently: for `q = 3,4,5,6` there
is no solution with `p ≢ 0 (mod q)` at all.

## 2. The block law forces `p = q + 1` exactly

Clearing denominators in `F(q·w − c) = p·w − c` and cancelling the shared term
`p·(q·w) = q·(p·w)` leaves

`c · (q + 1 − p) = 0`,

so for any genuine shift `c ≠ 0` the exact block law holds **only** at `p = q + 1`
(`block_forces_p_eq_q_succ`) — a single point, not the heuristic range `p < q²`.
Since `q + 1 < q²` for every `q ≥ 2`, this implies the mean-contraction heuristic and
is strictly sharper than it.  Checked both directions independently over
`2 ≤ q ≤ 7`, `2 ≤ p ≤ 11`, `−5 ≤ c ≤ 5`: the law holds exactly on `p = q + 1` and
nowhere else.

Together (`combined_characterization`): totality gives `q = 2`, the block law then
gives `p = 3`.

## 3. The `5n+1` test, which this had to pass

`5n + 1` has `p = 5 ≠ q + 1 = 3`, so by the contrapositive of
`block_forces_p_eq_q_succ` **no** shift `c ≠ 0` gives it an exact block law.  That is
an exact identity failure, not a growth estimate — which matters, because `5n+1`'s
believed divergence is heuristic and could not have been used as evidence.

## What this does not do

It says nothing about the **sign** of `c`, so it does not separate `3n+1` from the
mirror `3n−1` — both are `(p,q) = (3,2)`.  That question was asked separately and
`GenBlock` killed it (trivial scaling).  So this pins the multiplier and base, not
the full triple; `ShiftTrichotomy` and `RayAsymmetry` are what speak to the sign.

Every statement here is `decide`/`omega`-exact.  No new bound;
`RealizableFrontier6809.length_ge_6809` stands.
-/

namespace Collatz
namespace FamilyPin

/-! ## Part 1 — admissibility of a single deterministic affine branch

The map is `n ↦ n / q` when `q ∣ n`, else `n ↦ (p * n + c) / q`.  For the
"else" branch to be a *total, exact* Nat map (no floor error) it must send
EVERY residue `n % q = r`, `r ∈ {1, ..., q-1}`, to an integer, i.e.
`(p * r + c) % q = 0` for every such `r`.

Claim: for `q ≥ 3` this forces `p ≡ 0` and `c ≡ 0` (mod `q`) — the branch
degenerates (no real division: `p = q*p'`, `c = q*c'` and `(p*n+c)/q = p'*n+c'`
for ALL `n`, so the "q-structure" was never really used).  For `q = 2` there is
a genuine solution `p ≡ 1, c ≡ 1 (mod 2)` where the branch is a real division.
-/

/-- The exact "totality" condition on one candidate branch. -/
def branchTotal (p q c : Nat) : Prop := ∀ r, 1 ≤ r → r < q → (p * r + c) % q = 0

/-- **For `q ≥ 3`, totality forces `p ≡ 0 (mod q)`.**  Compare the residues
`r = 1` and `r = 2` (both lie in `[1, q)` since `q ≥ 3`): `p + c ≡ 0` and
`2p + c ≡ 0`, so `p ≡ 0`. -/
theorem q_ge_three_forces_p_zero {p q c : Nat} (hq : 3 ≤ q) (h : branchTotal p q c) :
    p % q = 0 := by
  have h1 := h 1 (by omega) (by omega)
  have h2 := h 2 (by omega) (by omega)
  -- h1 : (p*1+c) % q = 0,  h2 : (p*2+c) % q = 0
  have e1 : p * 1 + c = p + c := by omega
  have e2 : p * 2 + c = p + (p + c) := by omega
  rw [e1] at h1
  rw [e2] at h2
  -- h1 : (p + c) % q = 0,  h2 : (p + (p + c)) % q = 0
  have hsum : (p + (p + c)) % q = (p % q + (p + c) % q) % q := Nat.add_mod p (p + c) q
  rw [hsum, h1] at h2
  have hpq : p % q < q := Nat.mod_lt p (by omega)
  simp at h2
  omega

/-- Hence `c ≡ 0 (mod q)` too (from `r = 1`). -/
theorem q_ge_three_forces_c_zero {p q c : Nat} (hq : 3 ≤ q) (h : branchTotal p q c) :
    c % q = 0 := by
  have hp := q_ge_three_forces_p_zero hq h
  have h1 := h 1 (by omega) (by omega)
  have e1 : p * 1 + c = p + c := by omega
  rw [e1] at h1
  have hsum : (p + c) % q = (p % q + c % q) % q := Nat.add_mod p c q
  rw [hsum, hp] at h1
  have hcq : c % q < q := Nat.mod_lt c (by omega)
  simp at h1
  omega

/-- **`q = 2` admits a genuinely nontrivial branch**: `p, c` both odd. -/
theorem q_two_nontrivial : branchTotal 3 2 1 := by
  intro r hr1 hr2
  have : r = 1 := by omega
  subst this
  decide

/-- **`q = 2` also forces `p ≡ c (mod 2)`** — the only residue to satisfy is
`r = 1`. -/
theorem q_two_condition (p c : Nat) : branchTotal p 2 c ↔ (p + c) % 2 = 0 := by
  constructor
  · intro h
    have h1 := h 1 (by omega) (by omega)
    simpa using h1
  · intro h r hr1 hr2
    have : r = 1 := by omega
    subst this
    simpa using h

/-- **Kill test / sanity check for `q ≥ 3`: numeric witness `q = 3`.**  The
only solutions mod 3 are `p ≡ 0, c ≡ 0` — no branch with `p ≢ 0` is total. -/
example : ¬ branchTotal 1 3 0 := by
  intro h
  have := h 1 (by omega) (by omega)
  simp at this

example : ¬ branchTotal 1 3 1 := by
  intro h
  have := h 1 (by omega) (by omega)
  simp at this

/-! ## Part 2 — the block law forces `p = q + 1` exactly (not a range)

`GenBlock.gen_block` proved, for `q = 2` and `p = 3`, the block law
`F^a(2^a·w − c) = 3^a·w − c`. Fix `q` and `c ≠ 0` and ask: for which `p` does
the ANALOGOUS block law hold at all? Not "for which `p` in some heuristic
contracting range" — for which `p` does the exact identity even have a chance,
already at `a = 1`?

At `a = 1`: `F(q·w − c) = p·w − c`, and (since `q ∤ (q·w−c)` when `c % q ≠ 0`)
`F(q·w−c) = (p·(q·w−c)+c)/q`. Clearing denominators, the identity
`(p·(q·w−c)+c) = q·(p·w−c)` expands to `c·(q + 1 − p) = 0`. Since `c ≠ 0`
this forces `p = q + 1` exactly — not `p < q²`, not a range: one point.
This is sharper than (and implies) the usual "mean contraction" heuristic
`p < q²`, since `q + 1 < q²` for every `q ≥ 2`; the new content is that the
exact block law pins `p` to a single integer once `q` is fixed, and c-shift
`≠ 0` is used essentially, not statistically.
-/

/-- The one-block identity, integer form (denominators already cleared). -/
def blockIdentity (p q c w : Int) : Prop := p * (q * w - c) + c = q * (p * w - c)

/-- **Necessity: `c ≠ 0` and the block identity force `p = q + 1`.** This is
the exact (non-heuristic, non-probabilistic) reason the growth multiplier is
pinned to `q + 1` once the base `q` and a genuine (nonzero) shift are fixed.
Proof: expand both sides, cancel the shared nonlinear term `q*(p*w) = p*(q*w)`,
and factor what remains as `c * (q + 1 - p) = 0`; `c ≠ 0` and `Int.mul_eq_zero`
finish it. No `nlinarith`, no `ring` — plain distributivity + `omega`. -/
theorem block_forces_p_eq_q_succ {p q c w : Int} (hc : c ≠ 0)
    (hblock : blockIdentity p q c w) : p = q + 1 := by
  unfold blockIdentity at hblock
  have hpq : p * (q * w) = q * (p * w) := by
    rw [← Int.mul_assoc, Int.mul_comm p q, Int.mul_assoc]
  have hL : p * (q * w - c) = p * (q * w) - p * c := by rw [Int.mul_sub]
  have hR : q * (p * w - c) = q * (p * w) - q * c := by rw [Int.mul_sub]
  rw [hL, hR, hpq] at hblock
  have hcancel : c - p * c + q * c = 0 := by omega
  have hfactor : c * (q + 1 - p) = c - p * c + q * c := by
    rw [Int.mul_sub, Int.mul_add, Int.mul_one, Int.mul_comm c q, Int.mul_comm c p]
    omega
  have hz : c * (q + 1 - p) = 0 := by rw [hfactor]; exact hcancel
  rcases Int.mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hc
  · omega

/-- **`(3, 2)` is a solution** (Collatz / the mirror): `q = 2 ⟹ p = q+1 = 3`. -/
example : blockIdentity 3 2 1 (7 : Int) := by unfold blockIdentity; decide

/-- **`(5, 2)` is NOT a solution — the `5n+1` kill test, done algebraically.**
`5n+1`'s `p = 5 ≠ q + 1 = 3`, so the exact block identity fails; concretely at
`w = 7, c = 1`: `F(2·7−1) = F(13) = (5·13+1)/2 = 33`, but the block law would
need `p·w − c = 5·7−1 = 34`. `33 ≠ 34`. -/
example : ¬ blockIdentity 5 2 1 (7 : Int) := by
  unfold blockIdentity
  decide

/-! ## Part 3 — the general `(q+1, q, c)` block-law family (Nat, kernel-level)

Generalizes `GenBlock.gen_block` (which is the case `q = 2`) to every base `q`.
The multiplier `p` is `q + 1`, forced by Part 2 — it is not a second free
parameter. -/

/-- A divisor of both `m` and `n` divides `m - n` (core Lean has no
`Nat.dvd_sub'`; reproved here to keep this file self-contained). -/
theorem dvd_sub_of_dvd {d m n : Nat} (hm : d ∣ m) (hn : d ∣ n) : d ∣ m - n := by
  obtain ⟨p, hp⟩ := hm
  obtain ⟨q, hq⟩ := hn
  refine ⟨p - q, ?_⟩
  rcases Nat.le_total p q with h | h
  · have hmn : m ≤ n := by rw [hp, hq]; exact Nat.mul_le_mul_left d h
    have h1 : m - n = 0 := by omega
    have h2 : p - q = 0 := by omega
    rw [h1, h2, Nat.mul_zero]
  · have hsplit : d * (p - q) + d * q = d * p := by
      rw [← Nat.mul_add]
      have : p - q + q = p := by omega
      rw [this]
    omega

def genStepQ (q c n : Nat) : Nat :=
  if n % q = 0 then n / q else ((q + 1) * n + c) / q

def genOrbitQ (q c : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => genOrbitQ q c k (genStepQ q c n)

theorem gen_block_q (q c : Nat) (hq : 1 ≤ q) (hc : c % q ≠ 0) :
    ∀ (a w : Nat), c ≤ q ^ a * w → genOrbitQ q c a (q ^ a * w - c) = (q + 1) ^ a * w - c := by
  intro a
  induction a with
  | zero => intro w _; simp [genOrbitQ]
  | succ a ih =>
    intro w hle
    have hpow : q ^ (a + 1) * w = q * (q ^ a * w) := by
      rw [Nat.pow_succ, Nat.mul_comm (q ^ a) q, Nat.mul_assoc]
    have hmod : (q ^ (a + 1) * w - c) % q ≠ 0 := by
      intro hz
      apply hc
      have hqd : q ∣ q ^ (a + 1) * w := ⟨q ^ a * w, hpow⟩
      have hnz : q ∣ (q ^ (a + 1) * w - c) := Nat.dvd_of_mod_eq_zero hz
      have heq : q ^ (a + 1) * w - (q ^ (a + 1) * w - c) = c := by omega
      have hsub := dvd_sub_of_dvd hqd hnz
      rw [heq] at hsub
      exact Nat.mod_eq_zero_of_dvd hsub
    have hcY : c ≤ q * (q ^ a * w) := by omega
    have hy : q ^ a * ((q + 1) * w) = q * (q ^ a * w) + q ^ a * w := by
      have e1 : (q + 1) * w = q * w + w := by rw [Nat.add_mul, Nat.one_mul]
      rw [e1, Nat.mul_add, Nat.mul_left_comm]
    have hstep : genStepQ q c (q ^ (a + 1) * w - c)
        = q * (q ^ a * w) + q ^ a * w - c := by
      rw [genStepQ, if_neg hmod, hpow]
      have e2 : (q + 1) * (q * (q ^ a * w) - c)
          = q * (q * (q ^ a * w) - c) + (q * (q ^ a * w) - c) := by
        rw [Nat.add_mul, Nat.one_mul]
      have hqcqY : q * c ≤ q * (q * (q ^ a * w)) := Nat.mul_le_mul_left q hcY
      have e4 : q * (q * (q ^ a * w) - c) = q * (q * (q ^ a * w)) - q * c := by
        rw [Nat.mul_sub]
      have step1 : (q + 1) * (q * (q ^ a * w) - c) + c
          = q * (q * (q ^ a * w)) - q * c + q * (q ^ a * w) := by
        rw [e2, e4]; omega
      have step2 : q * (q * (q ^ a * w)) - q * c + q * (q ^ a * w)
          = q * (q * (q ^ a * w) + q ^ a * w - c) := by
        have e5 : q * (q * (q ^ a * w) + q ^ a * w - c)
            = q * (q * (q ^ a * w) + q ^ a * w) - q * c := by rw [Nat.mul_sub]
        rw [e5, Nat.mul_add]
        omega
      rw [step1, step2, Nat.mul_div_cancel_left _ (by omega : 0 < q)]
    rw [genOrbitQ, hstep, ← hy]
    have hle' : c ≤ q ^ a * ((q + 1) * w) := by rw [hy]; omega
    rw [ih ((q + 1) * w) hle']
    have h3 : (q + 1) ^ (a + 1) * w = (q + 1) ^ a * ((q + 1) * w) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    omega

/-- **Sanity check: this recovers `GenBlock.gen_block` at `q = 2`.**
`(q+1) = 3`, matching Collatz's multiplier exactly. -/
example (c : Nat) (hc : c % 2 ≠ 0) (a w : Nat) (hle : c ≤ 2 ^ a * w) :
    genOrbitQ 2 c a (2 ^ a * w - c) = 3 ^ a * w - c := by
  have h := gen_block_q 2 c (by omega) hc a w hle
  simpa using h

/-! ## Part 4 — the characterization, combined

Two INDEPENDENT constraints, proved above from two different requirements,
both single out `(p, q) = (3, 2)`:

* **(i) determinism** — `branchTotal p q c` with a genuinely nontrivial branch
  (`p % q ≠ 0`, i.e. the "else" branch is a real division, not a disguised
  smaller-base map) forces `q = 2` (`q_ge_three_forces_p_zero` kills `q ≥ 3`;
  `Nat.mod_one` kills `q = 1`).
* **(ii) a genuine (nonzero) additive shift with an exact block law** forces
  `p = q + 1` (`block_forces_p_eq_q_succ`), not merely `p < q²`.

Neither constraint mentions the other's mechanism — (i) is about the branch
being a well-defined *function*, (ii) is about the block map being a
well-defined *identity* over many steps — and they agree on `q = 2`, hence
(with (ii)) on `p = q + 1 = 3`. `combined_characterization` below is exactly
that: from (i) and (ii) together, `q = 2 ∧ p = 3`.

**What this is not**: it does not resolve the sign of `c` (`+1` vs `−1`, i.e.
Collatz vs. the mirror `3n−1`) — that axis was already isolated and shown to
be a separate, killed question in `GenBlock.lean`. Nor is it a probabilistic
argument: every step is an exact identity or an exact non-identity, checked
by `decide`/`omega`, never by a mean-growth estimate. -/

theorem combined_characterization {p q c : Nat} (hq : 1 ≤ q)
    (htot : branchTotal p q c) (hnontriv : p % q ≠ 0) (hc : c ≠ 0)
    (hblock : blockIdentity (p : Int) (q : Int) (c : Int) (7 : Int)) :
    q = 2 ∧ p = 3 := by
  have hq2 : q = 2 := by
    rcases Nat.lt_or_ge q 3 with hlt | hge
    · rcases Nat.lt_or_ge q 2 with hlt2 | hge2
      · have hq1 : q = 1 := by omega
        subst hq1
        exact absurd (Nat.mod_one p) hnontriv
      · omega
    · exact absurd (q_ge_three_forces_p_zero hge htot) hnontriv
  have hc' : (c : Int) ≠ 0 := by omega
  have hp : (p : Int) = (q : Int) + 1 := block_forces_p_eq_q_succ hc' hblock
  subst hq2
  exact ⟨rfl, by omega⟩

/-- **`5n+1` fails (ii)**, confirming it is excluded by the characterization
(the kill test from `RESEARCH.md`'s prompt, done first as required): with
`q = 2`, `p = 5 ≠ 3 = q + 1`, so `block_forces_p_eq_q_succ`'s contrapositive
applies — `5n+1` has no genuine (`c ≠ 0`) exact block law of this shape. This
is the same fact as the `¬ blockIdentity 5 2 1 7` example above, now derived
from the general necessity theorem rather than checked by `decide`. -/
example (hblock : blockIdentity (5 : Int) (2 : Int) (1 : Int) (7 : Int)) : False := by
  have hc : (1 : Int) ≠ 0 := by decide
  have := block_forces_p_eq_q_succ hc hblock
  omega

end FamilyPin
end Collatz
