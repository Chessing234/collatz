import Collatz.Strategy.Pillars
import Collatz.Strategy.ScaleRecord

/-!
# Uniform covering by certified descent blocks

Round XV, sections 11 and 16.  The brief's headline form
`∀ n > 1, ∃ k, T^k(n) < n` is the conjecture verbatim
(`NeverDrops.collatz_iff_neverDrops`), so it is off limits.  The live,
non-circular version is the **finite-modulus covering**:

> fix `M = 2^K`; for each residue `r < M`, produce an explicit `k` and an
> explicit threshold `N(r)` such that **every** `n ≡ r (mod M)` with `n ≥ N(r)`
> satisfies `T^k(n) < n`.

That is a real theorem for each `K` — Terras' "sufficient sets" — and it is not
the conjecture, because the conjecture is the statement that *some* `K` covers
*all* classes.  This file supplies:

1. **The certificate.**  `accOrbit_lt_of_gap` and
   `accOrbit_lt_of_descendsLarge_of_mod`: the descent time `k` and the threshold
   are functions of the residue alone, so a single certificate covers the whole
   class, not a sample of it.
2. **The criterion is the pure multiplier test** `3 ^ a(r,k) < 2 ^ k`
   (`DescendsLarge`), with **no** auxiliary `T^k(r) ≤ r` conjunct.  Dropping the
   conjunct is a strict gain per level — `DescendsLarge 8 7` holds while
   `Descends 8 7` fails — and `survivesLarge_eq_survives_1024` records the
   kernel fact that at `K = 10` the two sieves nevertheless have the *same*
   survivor set.
3. **The failing set, exactly.**  `r` fails iff every prefix odd-count obeys
   `2 ^ i ≤ 3 ^ a(r,i)` for `1 ≤ i ≤ K` (`survivesLarge_iff`).  Under Terras'
   parity bijection `r ↦ (parity of T^0 r, …, T^{K-1} r)` this is a ballot
   condition: the counting path must stay weakly above the line of slope
   `log 2 / log 3`.  `covering_never_complete` records that the set is never
   empty.
4. **The even branch is consumed.**  `oddCount_lt_of_descendsLarge`: a
   certificate forces `a(r,k) < k`, i.e. at least one even step
   (`even_steps_pos`).  For `expStep` the `k`-step multiplier is `3 ^ k` on
   *every* class, the test becomes `3 ^ k < 2 ^ k`, which is false for every `k`
   (`expStep_never_descends`), and indeed `expOrbit` never drops
   (`expOrbit_no_drop`).  **The certificate distinguishes Collatz from
   `expStep`.**
-/

namespace Collatz
namespace Strategy
namespace UniformCovering

open Reach Congruence Minimal

/-! ## The odd-count is bounded by the step count -/

/-- At most one odd step per step: `a(n,k) ≤ k`. -/
theorem oddCount_le : ∀ (k n : Nat), oddCount n k ≤ k := by
  intro k
  induction k with
  | zero => intro n; rw [oddCount_zero]; omega
  | succ k ih =>
    intro n
    rcases Arith.mod_two_eq_zero_or_one n with he | ho
    · rw [oddCount_succ_of_even he]
      have := ih (acceleratedStep n); omega
    · rw [oddCount_succ_of_odd ho]
      have := ih (acceleratedStep n); omega

/-! ## The criterion

`Congruence.Descends` carries a second conjunct `T^k(r) ≤ r`, needed because it
asserts descent for *every* member of the class with `m > 0`.  The covering
formulation only asks for *sufficiently large* members, so the conjunct can go:
what is left is the pure multiplier test. -/

/-- **The descent criterion for large members of a class**: the `k`-step
multiplier of the class of `r` beats `2 ^ k`. -/
def DescendsLarge (k r : Nat) : Prop := 3 ^ oddCount r k < 2 ^ k

instance (k r : Nat) : Decidable (DescendsLarge k r) := by
  unfold DescendsLarge; infer_instance

/-- The gap `2 ^ k − 3 ^ a` is positive exactly when the criterion holds. -/
theorem gap_pos {k r : Nat} (h : DescendsLarge k r) :
    0 < 2 ^ k - 3 ^ oddCount r k := by
  unfold DescendsLarge at h; omega

/-- Splitting `2 ^ k · m` along the gap. -/
theorem gap_mul (k r m : Nat) (h : DescendsLarge k r) :
    3 ^ oddCount r k * m + (2 ^ k - 3 ^ oddCount r k) * m = 2 ^ k * m := by
  unfold DescendsLarge at h
  have hsum : 3 ^ oddCount r k + (2 ^ k - 3 ^ oddCount r k) = 2 ^ k := by omega
  rw [← Nat.add_mul, hsum]

/-! ## The certificate, uniform in the class -/

/-- **The certified descent block, sharp form.**  If the residue `r` passes the
multiplier test, then every member `2 ^ k · m + r` of its class whose index `m`
clears the gap threshold drops strictly below itself in `k` steps.  The step
count `k` and the threshold depend on `r` alone — this is what makes the
certificate uniform in the class rather than a per-element check. -/
theorem accOrbit_lt_of_gap {k r m : Nat} (h : DescendsLarge k r)
    (hm : acceleratedOrbit k r < (2 ^ k - 3 ^ oddCount r k) * m + r) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  rw [accOrbit_pow_two_mul_add]
  have hg := gap_mul k r m h
  omega

/-- **Crude but universal threshold**: `m > T^k(r)` always suffices, because the
gap is at least `1`. -/
theorem accOrbit_lt_of_descendsLarge {k r m : Nat} (h : DescendsLarge k r)
    (hm : acceleratedOrbit k r < m) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  refine accOrbit_lt_of_gap h ?_
  have h1 : 1 * m ≤ (2 ^ k - 3 ^ oddCount r k) * m :=
    Nat.mul_le_mul (gap_pos h) (Nat.le_refl m)
  have h2 : 1 * m = m := Nat.one_mul m
  omega

/-- The certificate stated on `n` itself, through its residue.  Note the shape:
`k` is fixed by the class, and the hypothesis is a *threshold* on `n`, so the
conclusion covers every sufficiently large member of the class at once. -/
theorem accOrbit_lt_of_descendsLarge_of_mod {k n : Nat}
    (h : DescendsLarge k (n % 2 ^ k))
    (hbig : 2 ^ k * (acceleratedOrbit k (n % 2 ^ k) + 1) ≤ n) :
    acceleratedOrbit k n < n := by
  have hpow : 0 < 2 ^ k := Arith.two_pow_pos k
  have hmod : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpow
  have hdecomp : 2 ^ k * (n / 2 ^ k) + n % 2 ^ k = n := by
    have := Nat.div_add_mod n (2 ^ k); omega
  -- the threshold forces the index past `T^k(r)`
  have hidx : acceleratedOrbit k (n % 2 ^ k) < n / 2 ^ k := by
    rcases Nat.lt_or_ge (acceleratedOrbit k (n % 2 ^ k)) (n / 2 ^ k) with hlt | hge
    · exact hlt
    · have hstep : n / 2 ^ k + 1 ≤ acceleratedOrbit k (n % 2 ^ k) + 1 := by omega
      have : 2 ^ k * (n / 2 ^ k + 1) ≤ 2 ^ k * (acceleratedOrbit k (n % 2 ^ k) + 1) :=
        Nat.mul_le_mul (Nat.le_refl (2 ^ k)) hstep
      have hexp : 2 ^ k * (n / 2 ^ k + 1) = 2 ^ k * (n / 2 ^ k) + 2 ^ k := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
  have := accOrbit_lt_of_descendsLarge (k := k) (r := n % 2 ^ k) h hidx
  rw [hdecomp] at this
  exact this

/-! ## The failing set, exactly

A residue *fails* (survives the sieve) at level `K` when no prefix length
`i ≤ K` passes the multiplier test. -/

/-- Boolean multiplier test. -/
def descendsLargeB (k r : Nat) : Bool := decide (3 ^ oddCount r k < 2 ^ k)

/-- The failing (surviving) predicate for the multiplier sieve. -/
def survivesLarge (j r : Nat) : Bool :=
  (List.range (j + 1)).all (fun i => !descendsLargeB i (r % 2 ^ i))

/-- **The failing set, characterised exactly.**  `r` fails at level `K` iff every
prefix odd-count stays on or above the critical line: `2 ^ i ≤ 3 ^ a(r mod 2^i, i)`
for all `i ≤ K`.  Under Terras' parity bijection this is precisely a ballot
condition on the parity word of `r`. -/
theorem survivesLarge_iff (K r : Nat) :
    survivesLarge K r = true ↔ ∀ i : Nat, i ≤ K → 2 ^ i ≤ 3 ^ oddCount (r % 2 ^ i) i := by
  constructor
  · intro h i hi
    rw [survivesLarge, List.all_eq_true] at h
    have hmem : i ∈ List.range (K + 1) := List.mem_range.mpr (by omega)
    have := h i hmem
    rw [descendsLargeB] at this
    simp at this
    omega
  · intro h
    rw [survivesLarge, List.all_eq_true]
    intro i hi
    have hiK : i ≤ K := by have := List.mem_range.mp hi; omega
    have := h i hiK
    rw [descendsLargeB]
    simp
    omega

/-- Failing to fail: some prefix length passes the test. -/
theorem exists_descendsLarge_of_not_survivesLarge {K r : Nat}
    (h : ¬ survivesLarge K r = true) :
    ∃ i : Nat, i ≤ K ∧ DescendsLarge i (r % 2 ^ i) := by
  rcases Nat.lt_or_ge 0 1 with _ | _
  · by_cases hc : ∃ i : Nat, i ≤ K ∧ DescendsLarge i (r % 2 ^ i)
    · exact hc
    · exfalso
      refine h ((survivesLarge_iff K r).mpr (fun i hi => ?_))
      have : ¬ DescendsLarge i (r % 2 ^ i) := fun hd => hc ⟨i, hi, hd⟩
      unfold DescendsLarge at this
      omega
  · omega

/-! ## The covering theorem for a fixed modulus

For each `K` this is a genuine, finite, non-circular theorem: every class that
fails the sieve is covered by one certificate valid for the whole class. -/

/-- **Finite-modulus covering, positive half.**  Every residue class modulo
`2 ^ K` outside the failing set carries a certified uniform descent block: a
single `i ≤ K` and a single threshold that work for the entire class. -/
theorem covering_of_not_survivesLarge {K r : Nat}
    (h : ¬ survivesLarge K r = true) :
    ∃ i : Nat, i ≤ K ∧ ∀ n : Nat, n % 2 ^ K = r →
      2 ^ i * (acceleratedOrbit i (n % 2 ^ i) + 1) ≤ n → acceleratedOrbit i n < n := by
  obtain ⟨i, hiK, hd⟩ := exists_descendsLarge_of_not_survivesLarge h
  refine ⟨i, hiK, ?_⟩
  intro n hn hbig
  have hmod : n % 2 ^ K % 2 ^ i = n % 2 ^ i := mod_pow_two_mod hiK
  rw [hn] at hmod
  refine accOrbit_lt_of_descendsLarge_of_mod ?_ hbig
  rw [← hmod]
  exact hd

/-- **Finite-modulus covering, negative half.**  No `K` covers every class: the
class of `−1` modulo `2 ^ K` fails the sieve for every `K`
(`Obstruction.sieve_never_clears`), so the covering is never complete and the
step from "each `K` is a theorem" to "some `K` proves Collatz" is exactly the
gap this method cannot close. -/
theorem covering_never_complete (K : Nat) :
    ∃ r : Nat, r < 2 ^ K ∧ survives K r = true :=
  Obstruction.sieve_never_clears K

/-! ## The two sieves agree at `K = 10`

`Descends` adds `T^k(r) ≤ r` to the multiplier test, so `survivesLarge` is
pointwise at most `survives`.  Per level the containment is strict — see
`descendsLarge_eight_seven` below.  Globally at `K = 10` it is not: the two
sieves have the *same* `64` survivors, verified by kernel computation. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem survivesLarge_eq_survives_1024 :
    (List.range 1024).all (fun r => survivesLarge 10 r == survives 10 r) = true := by
  decide

/-! ## The certificate reads the even branch

This is the round's test.  A descent certificate is available only when the
multiplier `3 ^ a` is beaten by `2 ^ k`, and since `2 ^ k ≤ 3 ^ k` that forces
`a < k`: the class must spend at least one step on the even branch.  So the
certificate is not a consequence of the affine law, the parity word, heaviness
or positivity alone — it consumes the even branch's exact contraction. -/

/-- **A certificate forces `a(r,k) < k`.** -/
theorem oddCount_lt_of_descendsLarge {k r : Nat} (h : DescendsLarge k r) :
    oddCount r k < k := by
  unfold DescendsLarge at h
  have hle := oddCount_le k r
  rcases Nat.lt_or_ge (oddCount r k) k with hlt | hge
  · exact hlt
  · exfalso
    have heq : oddCount r k = k := by omega
    rw [heq] at h
    have := Arith.two_pow_le_three_pow k
    omega

/-- Equivalently: a certified class takes at least one even step. -/
theorem even_steps_pos {k r : Nat} (h : DescendsLarge k r) :
    0 < k - oddCount r k :=
  Nat.sub_pos_of_lt (oddCount_lt_of_descendsLarge h)

/-- **`expStep` fails the criterion at every modulus and every length.**  Its
`k`-step multiplier is `3 ^ k` on every class — the even branch multiplies by
`3` too — so the test reads `3 ^ k < 2 ^ k`, which is false for every `k`. -/
theorem expStep_never_descends (k : Nat) : ¬ (3 ^ k < 2 ^ k) := by
  have := Arith.two_pow_le_three_pow k
  omega

/-- And in fact `expOrbit` never drops below its start, from any positive `x`
and after any number of steps: there is no descent block to certify. -/
theorem expOrbit_no_drop {x : Nat} (hx : 0 < x) (k : Nat) :
    ¬ (ScaleRecord.expOrbit k x < x) := by
  have := ScaleRecord.expOrbit_ge k x hx
  omega

/-- **The separation, in one statement.**  (i) the certificate consumes the even
branch; (ii) `expStep`'s multiplier test is unsatisfiable at every length; (iii)
`expStep` has no descending iterate at all.  A certificate that held for
`expStep` would be the wrong object; these do not. -/
theorem certificate_separates :
    (∀ k r : Nat, DescendsLarge k r → oddCount r k < k)
    ∧ (∀ k : Nat, ¬ (3 ^ k < 2 ^ k))
    ∧ (∀ x : Nat, 0 < x → ∀ k : Nat, x ≤ ScaleRecord.expOrbit k x) :=
  ⟨fun _ _ h => oddCount_lt_of_descendsLarge h,
   expStep_never_descends,
   fun x hx k => by have := ScaleRecord.expOrbit_ge k x hx; omega⟩

/-! ## One certificate, end to end

The class `7 mod 256`.  Its parity word over `8` steps has `a = 5` odd letters,
so the multiplier is `3 ^ 5 = 243`, the gap is `2 ^ 8 − 243 = 13`, and
`T^8(7) = 8`.  Note that `Descends 8 7` is **false** — `T^8(7) = 8 > 7` — so the
repository's sieve cannot use this level at all, while the covering criterion
can.  The three even steps are exactly what makes `243 < 256`; with `a = 8` the
multiplier would be `6561`. -/

theorem oddCount_eight_seven : oddCount 7 8 = 5 := by decide

theorem accOrbit_eight_seven : acceleratedOrbit 8 7 = 8 := by decide

/-- The multiplier test passes at `(k, r) = (8, 7)`. -/
theorem descendsLarge_eight_seven : DescendsLarge 8 7 := by decide

/-- …while the repository's stricter criterion fails there. -/
theorem not_descends_eight_seven : ¬ Descends 8 7 := by decide

/-- **The certified block.**  Every `n ≡ 7 (mod 256)` with `n ≥ 263` satisfies
`T^8(n) < n`.  Uniform in the class: one `k = 8`, one threshold, no sampling. -/
theorem drop_seven_mod_256 {n : Nat} (hmod : n % 256 = 7) (hn : 263 ≤ n) :
    acceleratedOrbit 8 n < n := by
  have h256 : (2 : Nat) ^ 8 = 256 := by decide
  have hdecomp : 256 * (n / 256) + n % 256 = n := by
    have := Nat.div_add_mod n 256; omega
  have hm : 1 ≤ n / 256 := by omega
  have hkey : acceleratedOrbit 8 (2 ^ 8 * (n / 256) + 7) < 2 ^ 8 * (n / 256) + 7 := by
    refine accOrbit_lt_of_gap descendsLarge_eight_seven ?_
    rw [accOrbit_eight_seven, oddCount_eight_seven]
    have hgap : (2 : Nat) ^ 8 - 3 ^ 5 = 13 := by decide
    rw [hgap]
    have h13 : 13 * 1 ≤ 13 * (n / 256) := Nat.mul_le_mul (Nat.le_refl 13) hm
    omega
  rw [h256] at hkey
  rw [hmod] at hdecomp
  rw [hdecomp] at hkey
  exact hkey

/-- The same block seen as a chunk of the `7 mod 16` pillar of Route C: one
sixteenth of that class is now unconditional. -/
theorem pillar_seven_mod_sixteen_partial {n : Nat} (hmod : n % 256 = 7) (hn : 263 ≤ n) :
    n % 16 = 7 ∧ ∃ k : Nat, acceleratedOrbit k n < n := by
  refine ⟨by omega, ⟨8, drop_seven_mod_256 hmod hn⟩⟩


/-! ## The exact obstruction to a finite covering

`covering_never_complete` says the failing *residue set* is never empty.  The
following is sharper and is the real obstruction: **descent times are
unbounded**, so no single block length `K` — hence no single modulus `2 ^ K`,
since a level-`K` certificate uses at most `K` steps — can cover every integer.
This is unconditional: it does not depend on the conjecture, and it holds for
the same reason `expStep` diverges, namely that a maximally odd parity word has
multiplier `3 ^ K`. -/

/-- **Descent times are unbounded.**  For every `K` the integer `2 ^ (K+2) − 1`
has no accelerated iterate below itself within `K` steps. -/
theorem no_bounded_descent_time (K : Nat) :
    ∃ n : Nat, 1 < n ∧ ∀ i : Nat, i ≤ K → ¬ acceleratedOrbit i n < n := by
  refine ⟨2 ^ (K + 2) - 1, ?_, ?_⟩
  · have h4 : (2:Nat) ^ 2 ≤ 2 ^ (K + 2) := Arith.two_pow_le_two_pow (by omega)
    have : (2:Nat) ^ 2 = 4 := by decide
    omega
  · intro i hi
    have hiK : i ≤ K + 2 := by omega
    have hval := Obstruction.accOrbit_two_pow_sub_one (K := K + 2) i hiK
    have hsplit : 2 ^ i * 2 ^ (K + 2 - i) = 2 ^ (K + 2) := by
      rw [← Arith.two_pow_add]
      congr 1
      omega
    have hdom : 2 ^ i * 2 ^ (K + 2 - i) ≤ 3 ^ i * 2 ^ (K + 2 - i) :=
      Nat.mul_le_mul (Arith.two_pow_le_three_pow i) (Nat.le_refl _)
    have hpos : 0 < 2 ^ (K + 2) := Arith.two_pow_pos (K + 2)
    omega

/-- **No finite covering.**  A complete finite-modulus covering would supply one
`K` with every `n > 1` dropping within `K` steps; `no_bounded_descent_time`
refutes that outright.  So each modulus `2 ^ K` yields a genuine theorem, the
uncovered set shrinks, but it is never empty — and the shrinkage is not a route
to the conjecture, because the obstruction is a *uniformity* failure, not a
density one. -/
theorem covering_needs_unbounded_blocks :
    ¬ ∃ K : Nat, ∀ n : Nat, 1 < n → ∃ i : Nat, i ≤ K ∧ acceleratedOrbit i n < n := by
  intro h
  obtain ⟨K, hK⟩ := h
  obtain ⟨n, hn, hno⟩ := no_bounded_descent_time K
  obtain ⟨i, hi, hlt⟩ := hK n hn
  exact hno i hi hlt

/-- The same obstruction seen through the criterion: the failing residue
`2 ^ K − 1` is maximally expanding, `a = K`, so its multiplier is `3 ^ K` — the
`expStep` multiplier.  **The residue classes the covering cannot reach are
exactly the classes that look like `expStep` for as long as one is willing to
look.** -/
theorem failing_class_is_expStep_like (K : Nat) :
    oddCount (2 ^ K - 1) K = K ∧ ¬ DescendsLarge K (2 ^ K - 1) := by
  refine ⟨Obstruction.oddCount_two_pow_sub_one K, ?_⟩
  intro hd
  have := oddCount_lt_of_descendsLarge hd
  rw [Obstruction.oddCount_two_pow_sub_one K] at this
  omega

end UniformCovering
end Strategy
end Collatz
