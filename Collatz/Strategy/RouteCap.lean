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

/-- **A certificate step at index `a` forces `a < 6c`.**  The verified range caps
the certificate's reach linearly, so no finite range reaches every odd-step
budget. -/
theorem reach_lt_six_mul {a c : Nat}
    (h : Bcap a + 3 ^ a * c < 2 * 2 ^ fexp a * c) : a < 6 * c := by
  -- weaken the certificate condition by `2 ^ fexp a ≤ 3 ^ a`
  have hfe : (2:Nat) ^ fexp a ≤ 3 ^ a := fexp_le a
  have hup : 2 * 2 ^ fexp a * c ≤ 2 * 3 ^ a * c :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 2) hfe) (Nat.le_refl c)
  have hdist : 2 * 3 ^ a * c = 2 * (3 ^ a * c) := Nat.mul_assoc 2 (3 ^ a) c
  have hBlt : Bcap a < 3 ^ a * c := by omega
  -- and combine with the lower bound
  have hlow := six_Bcap_ge a
  have hL : a * 3 ^ a = 3 ^ a * a := Nat.mul_comm a (3 ^ a)
  have hR : 6 * (3 ^ a * c) = 3 ^ a * (6 * c) := by
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
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

end RouteCap
end Collatz
