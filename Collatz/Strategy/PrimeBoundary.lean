import Collatz.Strategy.BoundaryCuts

namespace Collatz.PrimeBoundary
open BoundaryCuts BoundaryMoments
open Lean.Grind
attribute [local instance] Semiring.natCast

/-- The usual positive-divisor definition of a prime, without Mathlib. -/
def PrimeModulus (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d=1 ∨ d=p

theorem coprime_small {p a : Nat} (hp : PrimeModulus p) (ha : 0<a) (hap : a<p) :
    Nat.Coprime a p := by
  change Nat.gcd a p=1
  rcases hp.2 _ (Nat.gcd_dvd_right a p) with h|h
  · exact h
  · have := Nat.gcd_le_left p ha
    omega

theorem fin_no_zero_divisors {p : Nat} [NeZero p] (hp : PrimeModulus p)
    (a b : Fin p) (h : a*b=0) : a=0 ∨ b=0 := by
  by_cases ha : a=0
  · exact Or.inl ha
  · right
    have hva : 0<a.val := by
      have hz := (Fin.ext_iff (a := a) (b := 0))
      simp only [Fin.val_zero] at hz
      omega
    have hc := (coprime_small hp hva a.isLt).symm
    have hv := congrArg Fin.val h
    simp only [Fin.val_mul, Fin.val_zero] at hv
    have hb := hc.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hv)
    apply Fin.ext
    simpa [Nat.mod_eq_of_lt b.isLt] using Nat.mod_eq_zero_of_dvd hb

theorem annihilator_roots {p : Nat} [NeZero p] (hp : PrimeModulus p) (hn : 7<p) (a : Fin p)
    (h : 105*a*(a^2-1)=0) : a=0 ∨ a=1 ∨ a = -1 := by
  have h3 : (3 : Fin p) ≠ 0 := by
    intro h
    have hh := (IsCharP.ofNat_eq_zero_iff (α := Fin p) p 3).mp h
    rw [Nat.mod_eq_of_lt (by omega : 3<p)] at hh
    contradiction
  have h5 : (5 : Fin p) ≠ 0 := by
    intro h
    have hh := (IsCharP.ofNat_eq_zero_iff (α := Fin p) p 5).mp h
    rw [Nat.mod_eq_of_lt (by omega : 5<p)] at hh
    contradiction
  have h7 : (7 : Fin p) ≠ 0 := by
    intro h
    have hh := (IsCharP.ofNat_eq_zero_iff (α := Fin p) p 7).mp h
    rw [Nat.mod_eq_of_lt (by omega : 7<p)] at hh
    contradiction
  have he : (3 : Fin p)*5*7*a*(a-1)*(a+1)=0 := by grind
  rcases fin_no_zero_divisors hp _ _ he with h|h
  · rcases fin_no_zero_divisors hp _ _ h with h|h
    · rcases fin_no_zero_divisors hp _ _ h with h|h
      · rcases fin_no_zero_divisors hp _ _ h with h|h
        · rcases fin_no_zero_divisors hp _ _ h with h|h
          · exact False.elim (h3 h)
          · exact False.elim (h5 h)
        · exact False.elim (h7 h)
      · exact Or.inl h
    · exact Or.inr (Or.inl (by grind))
  · exact Or.inr (Or.inr (by grind))

theorem prime_half {p : Nat} [NeZero p] (hp : PrimeModulus p) (hn : 7<p) :
    2*(Nat.cast ((p+1)/2) : Fin p)=1 := by
  have hodd : p%2=1 := by
    by_cases he : p%2=0
    · have hd := hp.2 2 (Nat.dvd_of_mod_eq_zero he)
      omega
    · omega
  have heq : 2*((p+1)/2)=p+1 := by omega
  calc
    2*(Nat.cast ((p+1)/2) : Fin p) = Nat.cast (2*((p+1)/2)) := by
      rw [Semiring.natCast_mul]; grind
    _ = Nat.cast (p+1) := congrArg Nat.cast heq
    _ = 1 := by
      have h := IsCharP.natCast_ext (α := Fin p) p (x := p+1) (y := 1) (by simp)
      simpa only [Semiring.natCast_one] using h

theorem card_values {p q : Nat} [NeZero p] (hn : 7<p) (hq : 0<q) (hqp : q<p)
    (h : (Nat.cast q : Fin p)=0 ∨ (Nat.cast q : Fin p)=1 ∨ (Nat.cast q : Fin p) = -1) :
    q=1 ∨ q+1=p := by
  rcases h with h|h|h
  · have hh := (IsCharP.natCast_eq_zero_iff (α := Fin p) p q).mp h
    rw [Nat.mod_eq_of_lt hqp] at hh
    omega
  · left
    have hh : (Nat.cast q : Fin p)=Nat.cast 1 := by simpa only [Semiring.natCast_one] using h
    exact (IsCharP.natCast_eq_iff_of_lt (α := Fin p) p hqp (by omega)).mp hh
  · right
    have hz : (Nat.cast (q+1) : Fin p)=0 := by rw [Semiring.natCast_add, Semiring.natCast_one, h]; grind
    have hmod := (IsCharP.natCast_eq_zero_iff (α := Fin p) p (q+1)).mp hz
    have hd := Nat.le_of_dvd (by omega : 0<q+1) (Nat.dvd_of_mod_eq_zero hmod)
    omega

theorem prime_mul_injective {p : Nat} [NeZero p] (hp : PrimeModulus p)
    (c : Fin p) (hc : c ≠ 0) (a b : Fin p) (h : c*a=c*b) : a=b := by
  have hz : c*(a-b)=0 := by grind
  rcases fin_no_zero_divisors hp c (a-b) hz with hh|hh
  · exact False.elim (hc hh)
  · grind

theorem three_ne_zero {p : Nat} [NeZero p] (hn : 7<p) : (3 : Fin p) ≠ 0 := by
  intro h
  have hh := (IsCharP.ofNat_eq_zero_iff (α := Fin p) p 3).mp h
  rw [Nat.mod_eq_of_lt (by omega : 3<p)] at hh
  contradiction

/-- For every prime above 7, any nonempty proper two-edge cut has a singleton side. -/
theorem two_boundary_cardinality {p : Nat} [NeZero p] (hp : PrimeModulus p) (hn : 7<p)
    (L : List (Fin p)) (hL : L.Nodup) (hpos : 0<L.length) (hlt : L.length<p)
    (hb : boundary L (fun z => 2*z) +
      boundary L (oddBranch (Nat.cast ((p+1)/2)))=2) :
    L.length=1 ∨ L.length+1=p := by
  have h := two_boundary_annihilator L hL (Nat.cast ((p+1)/2)) (prime_half hp hn)
    (prime_mul_injective hp 3 (three_ne_zero hn)) hb
  exact card_values hn hpos hlt (annihilator_roots hp hn _ h)

/-- Boundary zero would force the cardinality to vanish modulo p. -/
theorem zero_boundary_impossible {p : Nat} [NeZero p] (hp : PrimeModulus p) (hn : 7<p)
    (L : List (Fin p)) (hL : L.Nodup) (hpos : 0<L.length) (hlt : L.length<p) :
    boundary L (fun z => 2*z) +
      boundary L (oddBranch (Nat.cast ((p+1)/2))) ≠ 0 := by
  intro hb
  let u : Fin p := Nat.cast ((p+1)/2)
  have hu : 2*u=1 := prime_half hp hn
  have hi2 : ∀ a b : Fin p, 2*a=2*b → a=b := by
    intro a b h
    have hh := congrArg (fun z => u*z) h
    grind
  have hiA : ∀ a b : Fin p, oddBranch u a=oddBranch u b → a=b := by
    intro a b h
    apply prime_mul_injective hp 3 (three_ne_zero hn) a b
    have hh := congrArg (fun z => 2*z) h
    simp only [oddBranch] at hh
    grind
  change boundary L (fun z => 2*z) + boundary L (oddBranch u)=0 at hb
  rw [boundary_twice hL _ hi2, boundary_twice hL _ hiA] at hb
  have hzeros : (outside L (L.map (fun z => 2*z))).length=0 ∧
      (outside L (L.map (oddBranch u))).length=0 := by
    have hh : ∀ a b : Nat, 2*a+2*b=0 → a=0 ∧ b=0 := by intros; omega
    exact hh _ _ hb
  have hd := (zero_perm hL (nodup_map hL _ hi2) (by simp) hzeros.1).symm
  have ha := (zero_perm hL (nodup_map hL _ hiA) (by simp) hzeros.2).symm
  have hmap : (fun z : Fin p => 2*oddBranch u z) = (fun z => 3*z+1) := by
    funext z; simp only [oddBranch]; grind
  have ha' := ha.map (fun z => 2*z)
  simp only [List.map_map, Function.comp_def, hmap] at ha'
  have hz := invariant_card_zero L ha' hd
  rw [moment_zero] at hz
  have hz' := (IsCharP.natCast_eq_zero_iff (α := Fin p) p L.length).mp hz
  rw [Nat.mod_eq_of_lt hlt] at hz'
  omega

/-- Every cut with at least two vertices on each side has at least four edges. -/
theorem four_le_boundary {p : Nat} [NeZero p] (hp : PrimeModulus p) (hn : 7<p)
    (L : List (Fin p)) (hL : L.Nodup) (hpos : 2≤L.length) (hlt : L.length+2≤p) :
    4 ≤ boundary L (fun z => 2*z) +
      boundary L (oddBranch (Nat.cast ((p+1)/2))) := by
  let u : Fin p := Nat.cast ((p+1)/2)
  have hu : 2*u=1 := prime_half hp hn
  have hi2 : ∀ a b : Fin p, 2*a=2*b → a=b := by
    intro a b h
    have hh := congrArg (fun z => u*z) h
    grind
  have hiA : ∀ a b : Fin p, oddBranch u a=oddBranch u b → a=b := by
    intro a b h
    apply prime_mul_injective hp 3 (three_ne_zero hn) a b
    have hh := congrArg (fun z => 2*z) h
    simp only [oddBranch] at hh
    grind
  have hne0 := zero_boundary_impossible hp hn L hL (by omega) (by omega)
  have hne2 : boundary L (fun z => 2*z) + boundary L (oddBranch u) ≠ 2 := by
    intro hh
    have hc := two_boundary_cardinality hp hn L hL (by omega) (by omega) hh
    omega
  change boundary L (fun z => 2*z) + boundary L (oddBranch u) ≠ 0 at hne0
  change 4 ≤ boundary L (fun z => 2*z) + boundary L (oddBranch u)
  rw [boundary_twice hL _ hi2, boundary_twice hL _ hiA] at hne0 hne2 ⊢
  have hh : ∀ a b : Nat, 2*a+2*b ≠ 0 → 2*a+2*b ≠ 2 → 4≤2*a+2*b := by intros; omega
  exact hh _ _ hne0 hne2

end Collatz.PrimeBoundary
