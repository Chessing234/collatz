import Collatz.Strategy.BcapSharp
import Collatz.Strategy.LatticeGeometry

/-!
# Round XIV: the extremal family is affine, and one integer kills all `2^m` of it

Round XIII produced an exponentially large family of heavy words hugging the
ceiling `Bcap`: the Beatty corner `t i = fexp i` with any admissible subset of its
*two-jump* coordinates lowered by one (`BcapSharp.tSub`, `Adm`).  The brief for
this round asked whether that family can be killed arithmetically — whether some
prime `p ∣ G` has `C(ε) ≢ 0 (mod p)` for every one of the `2 ^ m` selectors.

## 1.  `C(ε)` is affine in `ε`, not merely multilinear

Because `ε i ∈ {0,1}`, `2 ^ (fexp i − ε i) = 2 ^ fexp i · (1 − ε i / 2)`, and each
`ε i` occurs in exactly one summand of the positional expansion.  Hence

`C(ε) = Bcap a − Σ_{i ∈ J} ε i · λ i`,  `λ i = 3 ^ (a−1−i) · 2 ^ (fexp i − 1)`,

with `J` the set of two-jump indices.  This is already a theorem of the
repository: `BcapSharp.Cw_tSub_add_loss` says `Cw (tSub S) a + lossW S a = Bcap a`
and `lossW` is exactly the Horner form of `Σ ε i λ i`.  `lossW_fire_step` below
records the one-coordinate difference, which is the affineness statement proper:
switching a single coordinate on changes `C` by exactly `λ i`, independent of the
other coordinates.

So `G ∣ C(ε)` is a **subset-sum problem mod `G`**: is `Bcap a` in the `{0,1}`-span
of `{λ i}_{i ∈ J}` modulo `G`?  It is not a polynomial-vanishing problem.

## 2.  The masked flatness certificate

`LatticeGeometry.not_dvd_of_small` already had the right shape but the wrong
support: its dual `ℓ¹`-norm `msum` runs over **all** `a` coordinates, i.e. it
certifies flatness against every one of the `2 ^ a` perturbations of the reference
word, and that hypothesis is never satisfiable (that file measured
`msum / G ≥ 0.66` over every `k < G` at every ledge pair with `a ≤ 20`).

The family of this round moves only the `m ≈ 0.585 a` two-jump coordinates.
`msumM` below is `msum` restricted to a mask, `not_dvd_of_certificateM` is the
certificate against exactly the masked cube, and — this is the round's finding —
**the masked hypothesis is satisfiable where the unmasked one is not**.
`family_not_dvd` turns any such `k` into the statement that no member of the
`2 ^ m`-element family is a cycle word.

## 3.  What is verified, and where it stops

* `cert_17` / `family_17`: at the ledge pair `(L,a) = (27,17)`, where
  `G = 2 ^ 27 − 3 ^ 17 = 5077565` and `m = 9`, the single integer `k = 969166`
  gives `q = 333742`, `msumM = 4020244`, `q + msumM = 4353986 < G`.  Therefore
  **none of the `512` words of the family satisfies `G ∣ C`** — one witness, no
  enumeration.

* COMPUTATIONAL (exact integers, exhaustive over `k < G`): a masked witness `k`
  exists at every `a` with `5 ≤ a ≤ 23`, and the first `k` that works appears at
  a density matching `G / (m+1)!` — the probability that `m + 1` independent
  uniform residues sum to less than `G`.  Measured `G/(m+1)!` at the last success
  `a = 23` is `6.95`; it drops below `1` at `a = 25` and is `6.8·10⁻⁷` at
  `a = 41`, `2.4·10⁻⁹` at `a = 53`.  A bounded scan of the first `4·10⁸` values of
  `k` finds nothing at any `24 ≤ a ≤ 41`.  **The certificate dies by counting at
  `a ≈ 24`, and it dies because ledge survivors have anomalously small `G`.**

* Independently, and reaching further: MITM enumeration of all `2 ^ m` selectors
  shows `G ∤ C(ε)` for every `ε` at **every** `a` with `2 ≤ a ≤ 77`
  (COMPUTATIONAL).  A *prime* `p ∣ G` avoiding all `ε` exists at `66` of those
  `76` values; at `a ∈ {25,34,50,57,58,60,66,68,70,74}` **no prime factor of `G`
  avoids the family** — every prime is hit — yet `G` itself still is not.  So the
  brief's prime formulation is strictly weaker than the divisor formulation, and
  is false as a universal statement about ledge pairs.

## 4.  Honest accounting

Exact integer measurements at the surviving ledge `(L,a) = (6809, 4296)`:
`m = 2512` (`m/a = 0.5847`), `⌊log₂ G⌋ = 6798`, `⌊log₂ binom(L,a)⌋ = 6461`,
`⌊Bcap a / G⌋ = 1358717`.  So the heuristic count of cycle words *in the family*
is `2 ^ m / G = 2 ^ (−4286)`, while in the whole heavy-word space it is
`binom(L,a) / G = 2 ^ (−337)`.  Killing the family removes a `2 ^ (−3949)`
fraction of the expected obstruction.

**This closes brief sections 23–26 and 41 negatively.**  The family is cycle-free,
but for a reason that does not generalise: the certificate exists only where `G` is
large relative to `(m+1)!`, and ledge survivors are exactly the pairs where `G` is
anomalously *small*.  The family is not empty — `BcapSharp.tSub_strictInc` and
`tSub_heavy` prove every one of its `2 ^ m` members is a legal heavy word — so this
is a real exclusion, merely a negligible one.
-/

namespace Collatz
namespace FamilyFlatness

open RealizableBound ExtremalWord BcapSharp LatticeGeometry

/-! ## Part 1.  Affineness of `C` in the selector -/

/-- Two selectors that agree below `a` give the same accumulator. -/
theorem Cw_congr {t u : Nat → Nat} :
    ∀ a : Nat, (∀ i : Nat, i < a → t i = u i) → Cw t a = Cw u a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    rw [Cw_succ, Cw_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h a (Nat.lt_succ_self a)]

/-- `lossW` depends only on the selector below `a`. -/
theorem lossW_congr {S T : Nat → Bool} :
    ∀ a : Nat, (∀ j : Nat, j < a → S j = T j) → lossW S a = lossW T a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ p ihp =>
    intro h
    rw [lossW, lossW, ihp (fun j hj => h j (Nat.lt_succ_of_lt hj)),
      h p (Nat.lt_succ_self p)]

/-- **Affineness, one coordinate at a time.**  If `S` and `T` agree below `a`
except that `T` also fires at `i`, then `lossW` differs by exactly
`λ i = 3 ^ (a−1−i) · 2 ^ (fexp i − 1)`, independently of every other coordinate. -/
theorem lossW_fire_step {S T : Nat → Bool} {i : Nat} :
    ∀ a : Nat, i < a → S i = false → T i = true →
      (∀ j : Nat, j < a → j ≠ i → S j = T j) →
      lossW S a + 3 ^ (a - 1 - i) * 2 ^ (fexp i - 1) = lossW T a := by
  intro a
  induction a with
  | zero => intro h; exact absurd h (Nat.not_lt_zero i)
  | succ a ih =>
    intro hi hS hT hagree
    rcases Nat.lt_or_ge i a with hlt | hge
    · have ih' := ih hlt hS hT (fun j hj hne => hagree j (Nat.lt_succ_of_lt hj) hne)
      have hlast : S a = T a := hagree a (Nat.lt_succ_self a) (by omega)
      have hexp : a + 1 - 1 - i = (a - 1 - i) + 1 := by omega
      rw [lossW, lossW, hlast, hexp, Nat.pow_succ,
        Nat.mul_comm (3 ^ (a - 1 - i)) 3, Nat.mul_assoc]
      omega
    · have hia : i = a := by omega
      subst hia
      have hbelow : ∀ j : Nat, j < i → S j = T j :=
        fun j hj => hagree j (Nat.lt_succ_of_lt hj) (by omega)
      have hloss : lossW S i = lossW T i := lossW_congr i hbelow
      have h0 : i + 1 - 1 - i = 0 := by omega
      rw [lossW, lossW, hS, hT, hloss, h0, Nat.pow_zero, Nat.one_mul]
      simp

/-! ## Part 2.  The masked flatness certificate -/

/-- `Σ_{i<a, M i} (k · w i) % G`: the dual `ℓ¹`-norm restricted to the moving
coordinates.  Where `LatticeGeometry.msum` charges every coordinate, this charges
only the ones the family actually moves. -/
def msumM (M : Nat → Bool) (w : Nat → Nat) (k G : Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => msumM M w k G a + (if M a = true then (k * w a) % G else 0)

@[simp] theorem msumM_zero (M : Nat → Bool) (w : Nat → Nat) (k G : Nat) :
    msumM M w k G 0 = 0 := rfl

theorem msumM_succ (M : Nat → Bool) (w : Nat → Nat) (k G a : Nat) :
    msumM M w k G (a + 1) = msumM M w k G a + (if M a = true then (k * w a) % G else 0) := rfl

/-- A masked selection is bounded by the masked dual norm. -/
theorem ssum_le_msumM (M : Nat → Bool) (w e : Nat → Nat) (k G : Nat) :
    ∀ a : Nat, (∀ i : Nat, i < a → e i ≤ 1) →
      (∀ i : Nat, i < a → M i = false → e i = 0) →
      ssum (fun i => (k * w i) % G) e a ≤ msumM M w k G a := by
  intro a
  induction a with
  | zero => intro _ _; exact Nat.le_refl _
  | succ a ih =>
    intro he hm
    have ih' := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
      (fun i hi => hm i (Nat.lt_succ_of_lt hi))
    rw [ssum_succ, msumM_succ]
    by_cases hMa : M a = true
    · have h1 : e a * ((k * w a) % G) ≤ (k * w a) % G := by
        have := he a (Nat.lt_succ_self a)
        calc e a * ((k * w a) % G) ≤ 1 * ((k * w a) % G) := Nat.mul_le_mul_right _ this
          _ = (k * w a) % G := by omega
      rw [if_pos hMa]
      omega
    · have hMf : M a = false := by
        cases hh : M a with
        | false => rfl
        | true => rw [hh] at hMa; exact absurd rfl hMa
      have hea : e a = 0 := hm a (Nat.lt_succ_self a) hMf
      rw [if_neg hMa, hea]
      omega

/-- **The masked certificate.**  A single `k` whose dual vector is short *on the
mask* forbids every masked `{0,1}` perturbation from reaching a multiple of `G`. -/
theorem not_dvd_of_certificateM {M : Nat → Bool} {w e : Nat → Nat} {k G C0 a : Nat}
    (he : ∀ i : Nat, i < a → e i ≤ 1)
    (hm : ∀ i : Nat, i < a → M i = false → e i = 0)
    (hq : 0 < (k * C0) % G)
    (hsmall : (k * C0) % G + msumM M w k G a < G) :
    ¬ (G ∣ (C0 + ssum w e a)) := by
  intro hdvd
  have hT : ssum (fun i => (k * w i) % G) e a ≤ msumM M w k G a :=
    ssum_le_msumM M w e k G a he hm
  obtain ⟨c, hc⟩ := hdvd
  have hzero : (k * (C0 + ssum w e a)) % G = 0 := by
    rw [hc, ← Nat.mul_assoc, Nat.mul_comm k G, Nat.mul_assoc]
    exact Nat.mul_mod_right G (k * c)
  have h1 : (k * (C0 + ssum w e a)) % G
      = ((k * C0) % G + ssum (fun i => (k * w i) % G) e a) % G := by
    rw [Nat.mul_add, Nat.add_mod (k * C0), ssum_mul_mod w e k G a he, add_mod_right']
  have hlt : (k * C0) % G + ssum (fun i => (k * w i) % G) e a < G := by omega
  rw [Nat.mod_eq_of_lt hlt] at h1
  omega

/-! ## Part 3.  The mask of the extremal family -/

/-- The mask: the two-jump indices, i.e. exactly the coordinates an admissible
selector is allowed to fire at. -/
def canFire : Nat → Bool
  | 0 => false
  | i + 1 => decide (fexp i + 2 ≤ fexp (i + 1))

theorem canFire_zero : canFire 0 = false := rfl

theorem fexp_jump_of_canFire {i : Nat} (h : canFire (i + 1) = true) :
    fexp i + 2 ≤ fexp (i + 1) := of_decide_eq_true h

/-- The mask is itself an admissible selector: it fires everywhere it may. -/
theorem adm_canFire : Adm canFire := by
  refine ⟨rfl, ?_⟩
  intro i h
  exact fexp_jump_of_canFire h

/-- Every admissible selector is dominated by the mask. -/
theorem canFire_of_adm {S : Nat → Bool} (hS : Adm S) :
    ∀ i : Nat, S i = true → canFire i = true := by
  intro i h
  match i with
  | 0 => rw [hS.1] at h; exact absurd h (by simp)
  | (p + 1) => exact decide_eq_true (hS.2 p h)

/-- At a mask index the exponent is at least two. -/
theorem fexp_ge_two_of_canFire {i : Nat} (h : canFire i = true) : 2 ≤ fexp i :=
  fexp_ge_two_of_fire adm_canFire h

/-- The **base word** of the family: every two-jump coordinate lowered. -/
def tAll : Nat → Nat := tSub canFire

/-- The perturbation that recovers `tSub S` from the base word. -/
def epsOf (S : Nat → Bool) (i : Nat) : Nat :=
  if S i = true then 0 else (if canFire i = true then 1 else 0)

theorem epsOf_le_one (S : Nat → Bool) (i : Nat) : epsOf S i ≤ 1 := by
  rw [epsOf]
  by_cases h : S i = true
  · rw [if_pos h]; omega
  · rw [if_neg h]; by_cases h2 : canFire i = true
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

theorem epsOf_off_mask {S : Nat → Bool} {i : Nat} (h : canFire i = false) : epsOf S i = 0 := by
  have h' : ¬ (canFire i = true) := by rw [h]; simp
  rw [epsOf]
  by_cases hs : S i = true
  · rw [if_pos hs]
  · rw [if_neg hs, if_neg h']

/-- **The family is a masked `{0,1}` perturbation of one base word.** -/
theorem tSub_eq_base_add {S : Nat → Bool} (hS : Adm S) (i : Nat) :
    tSub S i = tAll i + epsOf S i := by
  by_cases hs : S i = true
  · have hc : canFire i = true := canFire_of_adm hS i hs
    have h1 : tSub S i + 1 = fexp i := tSub_fire hS hs
    have h2 : tAll i + 1 = fexp i := tSub_fire adm_canFire hc
    rw [epsOf, if_pos hs]
    omega
  · have hsf : S i = false := by
      cases hh : S i with
      | false => rfl
      | true => rw [hh] at hs; exact absurd rfl hs
    have h1 : tSub S i = fexp i := tSub_quiet hsf
    by_cases hc : canFire i = true
    · have h2 : tAll i + 1 = fexp i := tSub_fire adm_canFire hc
      rw [epsOf, if_neg hs, if_pos hc]
      omega
    · have hcf : canFire i = false := by
        cases hh : canFire i with
        | false => rfl
        | true => rw [hh] at hc; exact absurd rfl hc
      have h2 : tAll i = fexp i := tSub_quiet hcf
      rw [epsOf, if_neg hs, if_neg hc]
      omega

/-! ## Part 4.  The certificate, on the family -/

/-- **The round's theorem.**  One integer `k` whose masked dual vector is shorter
than a period rules out `G ∣ C` for *every* admissible selector at once — all
`2 ^ m` of them, with no enumeration. -/
theorem family_not_dvd {G k a : Nat}
    (hq : 0 < (k * Cw tAll a) % G)
    (hsmall : (k * Cw tAll a) % G + msumM canFire (wgt tAll a) k G a < G)
    {S : Nat → Bool} (hS : Adm S) : ¬ (G ∣ Cw (tSub S) a) := by
  have he : ∀ i : Nat, i < a → epsOf S i ≤ 1 := fun i _ => epsOf_le_one S i
  have hm : ∀ i : Nat, i < a → canFire i = false → epsOf S i = 0 :=
    fun i _ h => epsOf_off_mask h
  have hrw : Cw (tSub S) a = Cw tAll a + ssum (wgt tAll a) (epsOf S) a := by
    rw [Cw_congr a (fun i _ => tSub_eq_base_add hS i), Cw_shift tAll (epsOf S) a he,
      Csel_eq_ssum]
  rw [hrw]
  exact not_dvd_of_certificateM he hm hq hsmall

/-! ## Part 5.  The ledge pair `(27, 17)`, certified by one integer -/

theorem G_17 : 2 ^ 27 - 3 ^ 17 = 5077565 := by decide

theorem Cw_tAll_17 : Cw tAll 17 = 386303947 := by decide

theorem cert_17 :
    0 < (969166 * Cw tAll 17) % 5077565 ∧
      (969166 * Cw tAll 17) % 5077565
        + msumM canFire (wgt tAll 17) 969166 5077565 17 < 5077565 := by
  rw [Cw_tAll_17]
  decide

/-- **At the ledge pair `(27, 17)` the entire `2 ^ 9`-element extremal family is
cycle-free**, certified by the single integer `k = 969166`. -/
theorem family_17 {S : Nat → Bool} (hS : Adm S) :
    ¬ ((2 ^ 27 - 3 ^ 17) ∣ Cw (tSub S) 17) := by
  rw [G_17]
  exact family_not_dvd cert_17.1 cert_17.2 hS

end FamilyFlatness
end Collatz
