import Collatz.Strategy.PreCertified

/-!
# The frontier theorem, parametric in the verified range

`RealizableBound.length_ge_4701` and `RealizableFrontier6809.length_ge_6809` are
the same proof written twice, once at `(c, A, F) = (768000, 2966, 4701)` and once
at `(1086464, 4296, 6809)`.  Each re-proves its own `no_light_window` too.  The
underlying lemmas `affineC_le_Bcap` and `le_fexp_of_affineC_le` were already
parametric in `c` and the reach `A`; only the wrappers were not.

This file states the theorem once, over `(c, A, F)`, taking the verified range as
a hypothesis.  With `Strategy.PreCertified` supplying the certificates and gaps,
a future range extension becomes a single instantiation rather than a new proof.

The three inputs are exactly:

* `hcert` — the certificate to reach `A`, i.e. `G(i) < c` for every `i < A`;
* `hgap` — `2 ^ (F − 1) < 3 ^ A`, so a cycle shorter than `F` stays inside the
  certificate's reach;
* `hver` — every orbit point of a counterexample is at least `c`.

Only `hver` depends on verified computation; the other two are banked.
-/

namespace Collatz
namespace FrontierParametric

open Reach Congruence AffineExact AccumulatorArith RealizableBound

/-- `no_light_window`, over an arbitrary range and reach. -/
theorem no_light_window_of_cert {c A m j : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlt : 3 ^ oddCount m j < 2 ^ j) (hA : oddCount m j < A) : False := by
  have hB : affineC j m ≤ Bcap (oddCount m j) :=
    affineC_le_Bcap hcpos hc hnd hcert j (by omega)
  have htime : j ≤ fexp (oddCount m j) :=
    le_fexp_of_affineC_le hcpos hc hnd (hcert _ hA) rfl hB
  have hpow : (2:Nat) ^ j ≤ 2 ^ fexp (oddCount m j) := Arith.two_pow_le_two_pow htime
  have hceil := fexp_le (oddCount m j)
  omega

open AccCycle in
/-- **The frontier theorem, once.**  Given a certificate reaching `A`, the gap
`2 ^ (F−1) < 3 ^ A`, and a verified range `c`, every nontrivial accelerated cycle
has length at least `F`. -/
theorem length_ge_of_cert {c A F : Nat} (hcpos : 0 < c)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c)
    (hgap : (2:Nat) ^ (F - 1) < 3 ^ A)
    (hver : ∀ {n m : Nat}, 0 < n → ¬ ReachesOne n →
      (∃ i : Nat, acceleratedOrbit i n = m) → c ≤ m)
    {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : F ≤ L := by
  rcases Nat.lt_or_ge L F with hL | hL
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    obtain ⟨i, hi⟩ := hm
    have hmpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
    have htrans : ∀ k : Nat, acceleratedOrbit k m = acceleratedOrbit (k + i) n := by
      intro k; rw [← hi, acceleratedOrbit_add k i n]
    have hnd : ∀ k : Nat, m ≤ acceleratedOrbit k m := by
      intro k; rw [htrans k]; exact hmin _
    have hc : c ≤ m := hver hn hnr ⟨i, hi⟩
    have hcyc : acceleratedOrbit L m = m := by
      rw [htrans L, Nat.add_comm L i, ← acceleratedOrbit_add i L n, h.2, hi]
    have hlt : 3 ^ oddCount m L < 2 ^ L :=
      Cycle.two_pow_gt_three_pow_of_accCycle hmpos h.1 hcyc
    have hA : oddCount m L < A := by
      rcases Nat.lt_or_ge (oddCount m L) A with hok | hcon
      · exact hok
      · exfalso
        have h1 : (3:Nat) ^ A ≤ 3 ^ oddCount m L := Nat.pow_le_pow_right (by omega) hcon
        have h2 : (2:Nat) ^ L ≤ 2 ^ (F - 1) := Arith.two_pow_le_two_pow (by omega)
        omega
    exact no_light_window_of_cert hcpos hc hcert hnd hlt hA
  · exact hL

/-! ## The existing frontier, recovered

A sanity check that the parametric form really does subsume the hand-written
one: `length_ge_6809` follows from it by instantiation. -/

open AccCycle in
theorem length_ge_6809_again {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 6809 ≤ L :=
  length_ge_of_cert (c := 1086464) (A := 4296) (F := 6809) (by omega)
    RealizableFrontier6809.cert_1086464 RealizableFrontier6809.pow_gap_4296
    (fun hn' hnr' hreach => RealizableFrontier6809.ge_verified_1086464 hn' hnr' hreach)
    hn h hnr

/-! ## The banked rungs, as conditional frontiers

Each is the honest statement: *if* the verified range reaches the threshold,
the frontier follows.  The certificate and the gap are already proved; only the
range hypothesis is outstanding. -/

open AccCycle in
theorem length_ge_7863_of_verified
    (hver : ∀ {n m : Nat}, 0 < n → ¬ ReachesOne n →
      (∃ i : Nat, acceleratedOrbit i n = m) → 1358718 ≤ m)
    {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 7863 ≤ L :=
  length_ge_of_cert (c := 1358718) (A := 4961) (F := 7863) (by omega)
    PreCertified.bank_4961 PreCertified.pow_gap_4961 hver hn h hnr

open AccCycle in
theorem length_ge_8917_of_verified
    (hver : ∀ {n m : Nat}, 0 < n → ¬ ReachesOne n →
      (∃ i : Nat, acceleratedOrbit i n = m) → 1664599 ≤ m)
    {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 8917 ≤ L :=
  length_ge_of_cert (c := 1664599) (A := 5626) (F := 8917) (by omega)
    PreCertified.bank_5626 PreCertified.pow_gap_5626 hver hn h hnr

open AccCycle in
theorem length_ge_9971_of_verified
    (hver : ∀ {n m : Nat}, 0 < n → ¬ ReachesOne n →
      (∃ i : Nat, acceleratedOrbit i n = m) → 2010160 ≤ m)
    {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 9971 ≤ L :=
  length_ge_of_cert (c := 2010160) (A := 6291) (F := 9971) (by omega)
    PreCertified.bank_6291 PreCertified.pow_gap_6291 hver hn h hnr

open AccCycle in
theorem length_ge_11025_of_verified
    (hver : ∀ {n m : Nat}, 0 < n → ¬ ReachesOne n →
      (∃ i : Nat, acceleratedOrbit i n = m) → 2403661 ≤ m)
    {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 11025 ≤ L :=
  length_ge_of_cert (c := 2403661) (A := 6956) (F := 11025) (by omega)
    PreCertified.bank_6956 PreCertified.pow_gap_6956 hver hn h hnr

open AccCycle in
theorem length_ge_12079_of_verified
    (hver : ∀ {n m : Nat}, 0 < n → ¬ ReachesOne n →
      (∃ i : Nat, acceleratedOrbit i n = m) → 2855820 ≤ m)
    {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 12079 ≤ L :=
  length_ge_of_cert (c := 2855820) (A := 7621) (F := 12079) (by omega)
    PreCertified.bank_7621 PreCertified.pow_gap_7621 hver hn h hnr

open AccCycle in
theorem length_ge_13133_of_verified
    (hver : ∀ {n m : Nat}, 0 < n → ¬ ReachesOne n →
      (∃ i : Nat, acceleratedOrbit i n = m) → 3380808 ≤ m)
    {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 13133 ≤ L :=
  length_ge_of_cert (c := 3380808) (A := 8286) (F := 13133) (by omega)
    PreCertified.bank_8286 PreCertified.pow_gap_8286 hver hn h hnr

open AccCycle in
/-- The first rung past the range this development has verified.  `cert_8951` and
`pow_gap_8951` are proved; only `hver` is outstanding, and by
`RouteCap.reach_sharp` the range it needs is at least `3 997 765`. -/
theorem length_ge_14187_of_verified
    (hver : ∀ {n m : Nat}, 0 < n → ¬ ReachesOne n →
      (∃ i : Nat, acceleratedOrbit i n = m) → 3997765 ≤ m)
    {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 14187 ≤ L :=
  length_ge_of_cert (c := 3997765) (A := 8951) (F := 14187) (by omega)
    PreCertified.bank_8951 PreCertified.pow_gap_8951 hver hn h hnr

end FrontierParametric
end Collatz
