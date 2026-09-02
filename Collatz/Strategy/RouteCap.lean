import Collatz.Strategy.FrontierParametric

/-!
# The certificate route is capped by the verified range

`Strategy.Frontier9971` is the fourth instantiation of the same machine:
a verified range `c` feeds `RealizableBound.cert`, the certificate reaches some
odd-step budget `A`, and `FrontierParametric.length_ge_of_cert` converts `A` into
a cycle-length frontier `F` with `2 ^ (F−1) < 3 ^ A`.

Round XLIV recorded, as prose, that this route cannot reach every cycle length —
the range needed to kill the `k`-th rung was measured to grow like
`a_k · a_{k+1} / (6 ln 2)`, which diverges.  A measured growth rate is not a
theorem.  This file proves the finiteness outright, and elementarily.

## The bound

The certificate condition at index `i` is

  `Bcap i + 3 ^ i · c < 2 · 2 ^ (fexp i) · c`.

Two facts about `Bcap` and `fexp` collide:

* `2 ^ fexp a ≤ 3 ^ a` (`fexp_le`), so the right-hand side is at most `2 · 3 ^ a · c`,
  and the condition forces `Bcap a < 3 ^ a · c`;
* `3 ^ i < 2 · 2 ^ fexp i` (`lt_fexp`), so every one of the `a` summands of
  `Bcap a = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (fexp i)` exceeds `3 ^ a / 6`, giving
  `a · 3 ^ a ≤ 6 · Bcap a` (`six_Bcap_ge`).

Together: `a · 3 ^ a ≤ 6 · Bcap a < 6 · 3 ^ a · c`, hence **`a < 6c`**.

So a verified range `c` buys a certificate reach of at most `6c` odd steps, and
therefore a frontier of at most `fexp (6c) + 1 ≈ 9.5 c` accelerated steps.  Every
finite range gives a finite frontier.  **No verified computation, however large,
excludes all cycle lengths by this route.**

## Honesty about the constant

`a < 6c` is true and far from tight.  At the range this repository actually has,
`c = 2 010 160`, it permits `a < 12 060 960`; the certificate in fact stops at
`a = 6291`.  The gap is the whole content of the measured `a_k · a_{k+1}` law:
the binding constraint is not the crude `2 ^ fexp a ≤ 3 ^ a` used here but how
closely `3 ^ a` approaches `2 ^ (fexp a + 1)` from below, which is a Diophantine
approximation question about `log₂ 3` and is not settled here.  What *is* settled
is the qualitative statement the route's finiteness rests on, which was the part
being asserted without proof.

No positivity hypothesis on `c` is needed: at `c = 0` the certificate condition
`Bcap i + 0 < 0` is unsatisfiable, so the reach is `0` and the cap holds
vacuously.
-/

namespace Collatz
namespace RouteCap

open RealizableBound

/-! ## The lower bound on `Bcap` -/

/-- **Every summand of `Bcap` exceeds `3 ^ a / 6`.**  Stated without division:
`a * 3 ^ a ≤ 6 * Bcap a`.  Each term `3 ^ (a−1−i) * 2 ^ (fexp i)` is at least
`3 ^ a / 6` because `3 ^ i < 2 * 2 ^ fexp i`, and there are `a` of them. -/
theorem six_Bcap_ge : ∀ a : Nat, a * 3 ^ a ≤ 6 * Bcap a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hstep : Bcap (a + 1) = 3 * Bcap a + 2 ^ fexp a := Bcap_succ a
    have hpow : (3:Nat) ^ (a + 1) = 3 ^ a * 3 := Nat.pow_succ 3 a
    -- the new term alone covers `3 ^ (a+1)`, because `3 ^ a < 2 * 2 ^ fexp a`
    have hnew : (3:Nat) ^ (a + 1) ≤ 6 * 2 ^ fexp a := by
      have hlt := lt_fexp a
      have hp2 : (2:Nat) ^ (fexp a + 1) = 2 ^ fexp a * 2 := Nat.pow_succ 2 (fexp a)
      omega
    -- the carried part reuses the induction hypothesis
    have hcarry : a * 3 ^ (a + 1) ≤ 18 * Bcap a := by
      have h1 : a * 3 ^ (a + 1) = 3 * (a * 3 ^ a) := by
        rw [hpow]; simp [Nat.mul_comm, Nat.mul_left_comm]
      have h2 : 3 * (a * 3 ^ a) ≤ 3 * (6 * Bcap a) := Nat.mul_le_mul (Nat.le_refl 3) ih
      omega
    have hsplit : (a + 1) * 3 ^ (a + 1) = a * 3 ^ (a + 1) + 3 ^ (a + 1) :=
      Nat.succ_mul a (3 ^ (a + 1))
    rw [hstep]
    omega

/-! ## The cap -/

/-- **The exact form of the collision.**  A certificate step at index `a` bounds
`a · 3 ^ a` by six times the range times the *gap* `2 · 2 ^ fexp a − 3 ^ a`, not
by six times the range times `3 ^ a`.  Everything else in this file is this
inequality with the gap estimated one way or another. -/
theorem reach_sharp {a c : Nat}
    (h : Bcap a + 3 ^ a * c < 2 * 2 ^ fexp a * c) :
    a * 3 ^ a < 6 * c * (2 * 2 ^ fexp a - 3 ^ a) := by
  have hlt := lt_fexp a
  have hp2 : (2:Nat) ^ (fexp a + 1) = 2 ^ fexp a * 2 := Nat.pow_succ 2 (fexp a)
  have hYX : (3:Nat) ^ a ≤ 2 * 2 ^ fexp a := by omega
  have hsub : (2 * 2 ^ fexp a - 3 ^ a) * c = 2 * 2 ^ fexp a * c - 3 ^ a * c :=
    Nat.sub_mul _ _ _
  have hmul : 3 ^ a * c ≤ 2 * 2 ^ fexp a * c := Nat.mul_le_mul hYX (Nat.le_refl c)
  have hB : Bcap a < (2 * 2 ^ fexp a - 3 ^ a) * c := by omega
  have hlow := six_Bcap_ge a
  have hcomm : 6 * c * (2 * 2 ^ fexp a - 3 ^ a) = 6 * ((2 * 2 ^ fexp a - 3 ^ a) * c) := by
    rw [Nat.mul_assoc, Nat.mul_comm c]
  omega

/-- **A certificate step at index `a` forces `a < 6c`.**  The verified range caps
the certificate's reach linearly, so no finite range reaches every odd-step
budget.  This is `reach_sharp` with the gap estimated crudely, by
`2 ^ fexp a ≤ 3 ^ a`. -/
theorem reach_lt_six_mul {a c : Nat}
    (h : Bcap a + 3 ^ a * c < 2 * 2 ^ fexp a * c) : a < 6 * c := by
  have hsharp := reach_sharp h
  have hfe : (2:Nat) ^ fexp a ≤ 3 ^ a := fexp_le a
  have hgap : 2 * 2 ^ fexp a - 3 ^ a ≤ 3 ^ a := by omega
  have hmono : 6 * c * (2 * 2 ^ fexp a - 3 ^ a) ≤ 6 * c * 3 ^ a :=
    Nat.mul_le_mul (Nat.le_refl (6 * c)) hgap
  have hcomm : 6 * c * 3 ^ a = 3 ^ a * (6 * c) := Nat.mul_comm _ _
  have hL : a * 3 ^ a = 3 ^ a * a := Nat.mul_comm a (3 ^ a)
  have hchain : 3 ^ a * a < 3 ^ a * (6 * c) := by omega
  exact Nat.lt_of_mul_lt_mul_left hchain

/-- The certificate hypothesis in the form `FrontierParametric` consumes it: a
certificate reaching `A` forces `A ≤ 6c`. -/
theorem cert_reach_le {c A : Nat}
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) :
    A ≤ 6 * c := by
  cases A with
  | zero => omega
  | succ A =>
    have := reach_lt_six_mul (a := A) (hcert A (by omega))
    omega

/-! ## The obstruction

Every frontier this route can produce is bounded by a function of the verified
range alone.  This is the statement Round XLIV asserted and did not prove. -/

/-- **The route's frontier is capped by the verified range.**  Whatever
certificate reach `A` and gap `2 ^ (F−1) < 3 ^ A` are supplied,
`F ≤ fexp (6c) + 1`. -/
theorem frontier_le_of_route {c A F : Nat}
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c)
    (hgap : (2:Nat) ^ (F - 1) < 3 ^ A) : F ≤ fexp (6 * c) + 1 := by
  have hA : A ≤ 6 * c := cert_reach_le hcert
  have hmono : (3:Nat) ^ A ≤ 3 ^ (6 * c) := Nat.pow_le_pow_right (by omega) hA
  have hceil : (3:Nat) ^ (6 * c) < 2 ^ (fexp (6 * c) + 1) := lt_fexp (6 * c)
  have hlt : (2:Nat) ^ (F - 1) < 2 ^ (fexp (6 * c) + 1) := by omega
  rcases Nat.lt_or_ge (F - 1) (fexp (6 * c) + 1) with hok | hcon
  · omega
  · exfalso
    have := Arith.two_pow_le_two_pow hcon
    omega

/-- **No finite verified range excludes all cycle lengths by this route.**  For
every range `c` there is a length — namely `fexp (6c) + 2` — that the route
cannot reach, no matter which certificate and gap are supplied. -/
theorem route_misses_a_length (c : Nat) :
    ∃ F₀ : Nat, ∀ A F : Nat,
      (∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) →
      (2:Nat) ^ (F - 1) < 3 ^ A → F < F₀ := by
  refine ⟨fexp (6 * c) + 2, ?_⟩
  intro A F hcert hgap
  have := frontier_le_of_route hcert hgap
  omega

/-! ## Proved lower bounds on the range each future rung needs

`reach_lt_six_mul` throws the gap away; keeping it turns the ladder's measured
cost into proved arithmetic.  The gap `2 · 2 ^ fexp a − 3 ^ a` measures how far
`3 ^ a` sits below `2 ^ (fexp a + 1)`, and on the `306 + 665k` staircase it
shrinks: `≈ 5.0 · 10⁻⁴ · 3 ^ a` at `a = 8286`, `≈ 1.1 · 10⁻⁴ · 3 ^ a` at
`a = 14271`.  Since `reach_sharp` reads `a · 3 ^ a < 6c · gap`, a shrinking gap
is a growing range requirement, and the requirement can be *proved* rung by rung
without any statement about how the gap behaves in general.

Pinning `fexp a` needs no evaluation of the `fexp` recursion — two big-number
comparisons suffice. -/

/-- `fexp a = F` from the two comparisons that characterise it. -/
theorem fexp_eq_of {a F : Nat} (h1 : (2:Nat) ^ F ≤ 3 ^ a) (h2 : (3:Nat) ^ a < 2 ^ (F + 1)) :
    fexp a = F := by
  have hge : F ≤ fexp a := le_fexp_of_pow_le h1
  have hle : fexp a ≤ F := by
    rcases Nat.lt_or_ge (fexp a) (F + 1) with hok | hcon
    · omega
    · exfalso
      have hmono := Arith.two_pow_le_two_pow hcon
      have := fexp_le a
      omega
  omega

/-- **The range a rung costs, from below.**  If a certificate at range `c`
reaches past the index `a`, and `N` satisfies `6N · gap ≤ a · 3 ^ a` at `a`, then
`N < c`.  Both `F` and `N` are supplied as literals and checked by the kernel;
nothing about the growth of the gap is assumed. -/
theorem range_gt_of_reach {c A a F N : Nat} (ha : a < A)
    (hF1 : (2:Nat) ^ F ≤ 3 ^ a) (hF2 : (3:Nat) ^ a < 2 ^ (F + 1))
    (hN : 6 * N * (2 * 2 ^ F - 3 ^ a) ≤ a * 3 ^ a)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) : N < c := by
  have hfe : fexp a = F := fexp_eq_of hF1 hF2
  have hsharp := reach_sharp (hcert a ha)
  rw [hfe] at hsharp
  -- the gap is positive, so `6N · gap < 6c · gap` cancels
  have hpos : 0 < 2 * 2 ^ F - 3 ^ a := by
    have hlt := lt_fexp a
    have hp2 : (2:Nat) ^ (fexp a + 1) = 2 ^ fexp a * 2 := Nat.pow_succ 2 (fexp a)
    rw [hfe] at hlt hp2
    omega
  have hchain : 6 * N * (2 * 2 ^ F - 3 ^ a) < 6 * c * (2 * 2 ^ F - 3 ^ a) := by omega
  have hcancel : 6 * N < 6 * c :=
    Nat.lt_of_mul_lt_mul_right hchain
  omega


/-! ### The rungs, checked

Five rungs of the `306 + 665k` staircase, spanning the last banked certificate
(`a = 8286`) and four beyond it.  Each needs three kernel comparisons: the two
that pin `fexp a`, and the one that certifies `N`.  Each `N` is the largest
integer the inequality admits, so these are the sharpest bounds `reach_sharp`
gives at those indices.

| `a` | frontier it would reach | range provably required |
|---|---|---|
| `8286` | `13133` | `> 2 770 233` |
| `9616` | `15241` | `> 3 897 857` |
| `10946` | `17349` | `> 5 633 687` |
| `12276` | `19457` | `> 8 651 415` |
| `14271` | `22619` | `> 22 543 234` |

The last row is the point.  `PreCertified` records that frontier `13133` costs a
range of `3 380 808` — a measurement.  Frontier `22619` provably costs more than
`22 543 234`, six and a half times as much for less than twice the frontier, and
the gap `2 · 2 ^ fexp a − 3 ^ a` is still shrinking. -/

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem lo_8286 : (2:Nat) ^ 13132 ≤ 3 ^ 8286 := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem hi_8286 : (3:Nat) ^ 8286 < 2 ^ (13132 + 1) := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem wit_8286 : 6 * 2770233 * (2 * 2 ^ 13132 - 3 ^ 8286) ≤ 8286 * 3 ^ 8286 := by decide

/-- A certificate reaching past index `8286` needs a verified range above
`2770233`. -/
theorem range_gt_2770233 {c A : Nat} (hA : 8286 < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) : 2770233 < c :=
  range_gt_of_reach hA lo_8286 hi_8286 wit_8286 hcert

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem lo_9616 : (2:Nat) ^ 15240 ≤ 3 ^ 9616 := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem hi_9616 : (3:Nat) ^ 9616 < 2 ^ (15240 + 1) := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem wit_9616 : 6 * 3897857 * (2 * 2 ^ 15240 - 3 ^ 9616) ≤ 9616 * 3 ^ 9616 := by decide

/-- A certificate reaching past index `9616` needs a verified range above
`3897857`. -/
theorem range_gt_3897857 {c A : Nat} (hA : 9616 < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) : 3897857 < c :=
  range_gt_of_reach hA lo_9616 hi_9616 wit_9616 hcert

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem lo_10946 : (2:Nat) ^ 17348 ≤ 3 ^ 10946 := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem hi_10946 : (3:Nat) ^ 10946 < 2 ^ (17348 + 1) := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem wit_10946 : 6 * 5633687 * (2 * 2 ^ 17348 - 3 ^ 10946) ≤ 10946 * 3 ^ 10946 := by decide

/-- A certificate reaching past index `10946` needs a verified range above
`5633687`. -/
theorem range_gt_5633687 {c A : Nat} (hA : 10946 < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) : 5633687 < c :=
  range_gt_of_reach hA lo_10946 hi_10946 wit_10946 hcert

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem lo_12276 : (2:Nat) ^ 19456 ≤ 3 ^ 12276 := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem hi_12276 : (3:Nat) ^ 12276 < 2 ^ (19456 + 1) := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem wit_12276 : 6 * 8651415 * (2 * 2 ^ 19456 - 3 ^ 12276) ≤ 12276 * 3 ^ 12276 := by decide

/-- A certificate reaching past index `12276` needs a verified range above
`8651415`. -/
theorem range_gt_8651415 {c A : Nat} (hA : 12276 < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) : 8651415 < c :=
  range_gt_of_reach hA lo_12276 hi_12276 wit_12276 hcert

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem lo_14271 : (2:Nat) ^ 22618 ≤ 3 ^ 14271 := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem hi_14271 : (3:Nat) ^ 14271 < 2 ^ (22618 + 1) := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 30000 in
theorem wit_14271 : 6 * 22543234 * (2 * 2 ^ 22618 - 3 ^ 14271) ≤ 14271 * 3 ^ 14271 := by decide

/-- A certificate reaching past index `14271` needs a verified range above
`22543234`. -/
theorem range_gt_22543234 {c A : Nat} (hA : 14271 < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) : 22543234 < c :=
  range_gt_of_reach hA lo_14271 hi_14271 wit_14271 hcert

end RouteCap
end Collatz
