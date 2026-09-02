import Collatz.Strategy.StairGap

/-!
# The certificate in closed form

Every rung of the frontier ladder rests on a `cert` computation —
`PreCertified.cert_8951` is an `8951`-step kernel evaluation over `14 000`-bit
numbers, and each rung's is larger than the last.  Those computations are the
only opaque step in the whole ladder: what they establish is
`Bcap i + 3 ^ i · c < 2 · 2 ^ (fexp i) · c` for every `i < A`, but *why* it holds
at a given `(A, c)` is visible only by running them.

This file bounds the certificate condition from both sides in closed form.

## The sandwich

`RouteCap.reach_sharp` already gave the **necessary** direction: if the
certificate holds at `a`, then

    a · 3 ^ a  <  6c · gapAt a.

`cert_of_gap_bound` here gives the **sufficient** direction: if

    i · 3 ^ i  <  3c · gapAt i    for every `i < A`,

then the certificate holds to `A`.  The two differ by a factor of two, and the
gap is exactly the slack between `Bcap a ≤ a · 3 ^ (a−1)` (`three_Bcap_le`, this
file) and `a · 3 ^ a ≤ 6 · Bcap a` (`RouteCap.six_Bcap_ge`).

Checked against every threshold the ladder actually uses:

| `c` | sufficient reach | actual `A` | necessary bound |
|---|---|---|---|
| `1 086 055` | `≥ 2965` | `4296` | `≤ 4960` |
| `2 010 160` | `≥ 4960` | `6291` | `≤ 7620` |
| `3 380 808` | `≥ 6955` | `8286` | `≤ 9615` |
| `3 997 765` | `≥ 7620` | `8951` | `≤ 10280` |

The bounds bracket the truth in all four, landing a rung or two either side.

## What this buys

The `cert` computations were never logically necessary — they buy a factor of
two in the reach, nothing more.  A frontier theorem can now be stated at any `c`
with no kernel evaluation at all, given control of `gapAt`, which
`Strategy.StairGeneric` and `Strategy.StairLower` supply exactly.

It does not move any frontier: the banked certificates are sharper than the
closed form, so `Frontier14187` stays the record.  What changes is that the
ladder is no longer opaque anywhere.
-/

namespace Collatz
namespace CertClosedForm

open RealizableBound StairGap

/-! ## The upper bound on `Bcap`

Dual to `RouteCap.six_Bcap_ge`.  Each summand of
`Bcap a = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (fexp i)` is at most `3 ^ (a−1)`, because
`2 ^ fexp i ≤ 3 ^ i`, and there are `a` of them. -/

theorem three_Bcap_le : ∀ a : Nat, 3 * Bcap a ≤ a * 3 ^ a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hstep : Bcap (a + 1) = 3 * Bcap a + 2 ^ fexp a := Bcap_succ a
    have hfe : (2:Nat) ^ fexp a ≤ 3 ^ a := fexp_le a
    have hpow : (3:Nat) ^ (a + 1) = 3 ^ a * 3 := Nat.pow_succ 3 a
    have h1 : 3 * (3 * Bcap a) ≤ 3 * (a * 3 ^ a) := Nat.mul_le_mul (Nat.le_refl 3) ih
    have h2 : 3 * (a * 3 ^ a) = a * 3 ^ (a + 1) := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm 3 a, Nat.mul_assoc,
        Nat.mul_comm (3:Nat) (3 ^ a)]
    have h3 : (a + 1) * 3 ^ (a + 1) = a * 3 ^ (a + 1) + 3 ^ (a + 1) :=
      Nat.succ_mul a (3 ^ (a + 1))
    rw [hstep]
    omega

/-! ## The sufficient condition -/

/-- **The certificate, in closed form.**  If `i · 3 ^ i < 3c · gapAt i` for every
`i < A`, the certificate holds to `A` — no kernel evaluation needed. -/
theorem cert_of_gap_bound {c A : Nat}
    (h : ∀ i : Nat, i < A → i * 3 ^ i < 3 * c * gapAt i) :
    ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c := by
  intro i hi
  have hB := three_Bcap_le i
  have hg := h i hi
  have hr : 3 * c * gapAt i = 3 * (c * gapAt i) := Nat.mul_assoc 3 c (gapAt i)
  have hBc : Bcap i < c * gapAt i := by omega
  have hgap : gapAt i = 2 * 2 ^ fexp i - 3 ^ i := rfl
  have hle : (3:Nat) ^ i ≤ 2 * 2 ^ fexp i := three_pow_le i
  have hmul : c * (2 * 2 ^ fexp i - 3 ^ i) = c * (2 * 2 ^ fexp i) - c * 3 ^ i :=
    Nat.mul_sub _ _ _
  have hc1 : c * (2 * 2 ^ fexp i) = 2 * 2 ^ fexp i * c := Nat.mul_comm _ _
  have hc2 : c * 3 ^ i = 3 ^ i * c := Nat.mul_comm _ _
  have hle2 : c * 3 ^ i ≤ c * (2 * 2 ^ fexp i) := Nat.mul_le_mul (Nat.le_refl c) hle
  rw [hgap] at hBc
  omega

/-- The two directions together.  `RouteCap.reach_sharp` supplies the converse;
stated here so the sandwich is one citation. -/
theorem cert_necessary {a c : Nat}
    (h : Bcap a + 3 ^ a * c < 2 * 2 ^ fexp a * c) :
    a * 3 ^ a < 6 * c * (2 * 2 ^ fexp a - 3 ^ a) :=
  RouteCap.reach_sharp h

/-! ## Correction: this is a structural sandwich, not a computational shortcut

The section above says a frontier theorem "can now be stated at any `c` with no
kernel evaluation, given control of `gapAt`".  The statement is true; the
implicature is not, and it is worth correcting explicitly.

`cert_of_gap_bound`'s hypothesis is `∀ i < A, i · 3 ^ i < 3c · gapAt i` — a
condition at **every** `i` below the reach, not at the staircase rungs.
`StairGeneric` and `StairLower` determine `gapAt` everywhere in principle, by
exact recurrences, but *evaluating* it at every `i < A` is a computation of the
same order as `cert` itself.  So the closed form does not save the computation.
What it does is explain it: the certificate is pinned between two explicit
inequalities, and the pinning is what was previously invisible.

## What the sandwich costs, measured

The closed form and the certificate need different ranges for the same reach.
The ratio is `a · 3 ^ a / (3 · Bcap a)`, which `Bcap_sandwich` confines to
`[1, 2]`, and which comes out the same at every rung tried:

| reach `A` | closed form needs `c >` | `cert` needs `c ≥` | ratio |
|---|---|---|---|
| `8286` | `4 685 313` | `3 380 808` | `1.386` |
| `8951` | `5 540 467` | `3 997 765` | `1.386` |
| `9616` | `6 559 829` | `4 733 176` | `1.386` |

`1.386` is `2 · ln 2`, and the reason is visible: `Bcap a` averages
`2 ^ (fexp i) / 3 ^ i = 2 ^ (−θ_i)` over the fractional parts `θ_i`, and
`∫₀¹ 2 ^ (−θ) dθ = 1 / (2 ln 2) = 0.7213`, so `a · 3 ^ a / (3 · Bcap a) → 2 ln 2`.
That is a heuristic — it assumes the `θ_i` equidistribute — and is recorded as
one, not proved.

So the price of the closed form is a `39 %` larger verified range, not a factor
of two.  Also recorded: the threshold for the next rung, `A = 9616`, is
`4 733 176`, computed by the routine that reproduces all eight known thresholds
exactly.  It is not banked as a `cert` here; the computation is available when
the cores are. -/

/-- The two directions of the `Bcap` estimate, together.  The certificate and its
closed form differ by exactly this ratio. -/
theorem Bcap_sandwich (a : Nat) : 3 * Bcap a ≤ a * 3 ^ a ∧ a * 3 ^ a ≤ 6 * Bcap a :=
  ⟨three_Bcap_le a, RouteCap.six_Bcap_ge a⟩

end CertClosedForm
end Collatz
