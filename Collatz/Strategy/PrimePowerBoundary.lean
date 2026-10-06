import Collatz.Strategy.PrimeBoundary

/-!
Lift the existing four-moment boundary obstruction from primes to prime powers.
The prime-power ring has zero divisors: cancellation below uses explicit
coprimality, not field cancellation. This is a modular cut theorem only.
-/
namespace Collatz.PrimePowerBoundary
open PrimeBoundary BoundaryCuts BoundaryMoments Lean.Grind
attribute [local instance] Semiring.natCast

theorem coprime_of_not_dvd {p a : Nat} (hp : PrimeModulus p) (ha : ¬p ∣ a) :
    Nat.Coprime p a := by
  rcases hp.2 _ (Nat.gcd_dvd_left p a) with h | h
  · exact h
  · have hd := Nat.gcd_dvd_right p a
    rw [h] at hd
    exact False.elim (ha hd)

theorem not_dvd_near {p a : Nat} (_hp : 2 < p) (ha : p ∣ a)
    {d : Nat} (hd : 0 < d) (hdp : d < p) : ¬p ∣ a+d := by
  intro h
  have h1 := Nat.mod_eq_zero_of_dvd ha
  have h2 := Nat.mod_eq_zero_of_dvd h
  simp only [Nat.add_mod, h1, Nat.zero_add, Nat.mod_eq_of_lt hdp] at h2
  omega

/-- A prime power dividing three consecutive integers divides one whole factor.
This is the local-ring step; multiplying prime-level conclusions is insufficient. -/
theorem power_divides_one_of_three {p k a : Nat} (hp : PrimeModulus p)
    (hp3 : 2 < p) (h : p^k ∣ a*(a+1)*(a+2)) :
    p^k ∣ a ∨ p^k ∣ a+1 ∨ p^k ∣ a+2 := by
  by_cases ha : p ∣ a
  · have h1 := (coprime_of_not_dvd hp (not_dvd_near hp3 ha (by omega) (by omega : 1<p))).pow_left k
    have h2 := (coprime_of_not_dvd hp (not_dvd_near hp3 ha (by omega) (by omega : 2<p))).pow_left k
    exact Or.inl (h1.dvd_of_dvd_mul_right (h2.dvd_of_dvd_mul_right h))
  · have ha' := (coprime_of_not_dvd hp ha).pow_left k
    have h' : p^k ∣ (a+1)*(a+2) := by
      apply ha'.dvd_of_dvd_mul_left
      simpa [Nat.mul_assoc] using h
    by_cases hb : p ∣ a+1
    · have h2 := (coprime_of_not_dvd hp
        (not_dvd_near hp3 hb (by omega) (by omega : 1<p))).pow_left k
      exact Or.inr (Or.inl (h2.dvd_of_dvd_mul_right h'))
    · exact Or.inr (Or.inr (((coprime_of_not_dvd hp hb).pow_left k).dvd_of_dvd_mul_left h'))

theorem cancel_cast_mul {m c : Nat} [NeZero m] (hc : Nat.Coprime m c)
    (z : Fin m) (h : (Nat.cast c : Fin m)*z=0) : z=0 := by
  have hv : (Nat.cast z.val : Fin m)=z := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt z.isLt
  have he : (Nat.cast (c*z.val) : Fin m)=0 := by
    rw [Semiring.natCast_mul, hv]
    exact h
  have hd := Nat.dvd_of_mod_eq_zero ((IsCharP.natCast_eq_zero_iff (α := Fin m) m _).mp he)
  have hz := hc.dvd_of_dvd_mul_left hd
  apply Fin.ext
  have hval := Nat.mod_eq_zero_of_dvd hz
  simpa [Nat.mod_eq_of_lt z.isLt] using hval

theorem small_coprime_power {p k c : Nat} (hp : PrimeModulus p)
    (hc : 0<c) (hcp : c<p) : Nat.Coprime (p^k) c :=
  ((coprime_small hp hc hcp).symm).pow_left k

theorem coefficient_coprime {p k : Nat} (hp : PrimeModulus p) (hn : 7<p) :
    Nat.Coprime (p^k) 105 := by
  have h3 : Nat.Coprime (p^k) 3 := small_coprime_power hp (by omega) (by omega)
  have h5 : Nat.Coprime (p^k) 5 := small_coprime_power hp (by omega) (by omega)
  have h7 : Nat.Coprime (p^k) 7 := small_coprime_power hp (by omega) (by omega)
  exact (h3.mul_right h5).mul_right h7

theorem obstruction_cardinality {p k q : Nat} [NeZero (p^k)]
    (hp : PrimeModulus p) (hn : 7<p) (hq : 0<q) (hlt : q<p^k)
    (h : (105 : Fin (p^k))*Nat.cast q*((Nat.cast q)^2-1)=0) :
    q=1 ∨ q+1=p^k := by
  have he : (Nat.cast (105*q*(q-1)*(q+1)) : Fin (p^k))=0 := by
    have hq' : (Nat.cast (q-1) : Fin (p^k)) + 1 = Nat.cast q := by
      have hnq : q-1+1=q := by omega
      have hh := congrArg (fun n : Nat => (Nat.cast n : Fin (p^k))) hnq
      simpa only [Semiring.natCast_add, Semiring.natCast_one] using hh
    simp only [Semiring.natCast_mul, Semiring.natCast_add, Semiring.natCast_one]
    grind
  have hd := Nat.dvd_of_mod_eq_zero
    ((IsCharP.natCast_eq_zero_iff (α := Fin (p^k)) (p^k) _).mp he)
  have hd' : p^k ∣ (q-1)*q*(q+1) := by
    apply (coefficient_coprime hp hn).dvd_of_dvd_mul_left
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd
  have hh : p^k ∣ (q-1)*((q-1)+1)*((q-1)+2) := by
    have h1 : q-1+1=q := by omega
    have h2 : q-1+2=q+1 := by omega
    simpa only [h1,h2] using hd'
  rcases power_divides_one_of_three hp (by omega) hh with h0 | h1 | h2
  · have hz : q-1=0 := Nat.eq_zero_of_dvd_of_lt h0 (by omega)
    omega
  · have hz : q-1+1=0 := Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    omega
  · have he : q-1+2=q+1 := by omega
    rw [he] at h2
    have hh := Nat.le_of_dvd (by omega : 0<q+1) h2
    omega

theorem power_half {p k : Nat} [NeZero (p^k)] (hp : PrimeModulus p) (hn : 7<p) :
    2*(Nat.cast ((p^k+1)/2) : Fin (p^k))=1 := by
  have hodd : p%2=1 := by
    by_cases he : p%2=0
    · have hh := hp.2 2 (Nat.dvd_of_mod_eq_zero he)
      omega
    · omega
  have hm : (p^k)%2=1 := by rw [Nat.pow_mod,hodd]; simp
  have heq : 2*((p^k+1)/2)=p^k+1 := by omega
  calc
    2*(Nat.cast ((p^k+1)/2) : Fin (p^k)) = Nat.cast (2*((p^k+1)/2)) := by
      rw [Semiring.natCast_mul]; grind
    _ = Nat.cast (p^k+1) := congrArg Nat.cast heq
    _ = 1 := by
      have h := IsCharP.natCast_ext (α := Fin (p^k)) (p^k)
        (x := p^k+1) (y := 1) (by simp)
      simpa only [Semiring.natCast_one] using h

theorem three_injective {p k : Nat} [NeZero (p^k)] (hp : PrimeModulus p) (hn : 7<p)
    (a b : Fin (p^k)) (h : 3*a=3*b) : a=b := by
  have hz : (Nat.cast 3 : Fin (p^k))*(a-b)=0 := by grind
  have hzero := cancel_cast_mul (small_coprime_power hp (by omega) (by omega : 3<p)) (a-b) hz
  grind

/-- Two crossing edges force a singleton side, at every prime-power exponent. -/
theorem two_boundary_cardinality {p k : Nat} [NeZero (p^k)]
    (hp : PrimeModulus p) (hn : 7<p)
    (L : List (Fin (p^k))) (hL : L.Nodup) (hpos : 0<L.length) (hlt : L.length<p^k)
    (hb : boundary L (fun z => 2*z) +
      boundary L (oddBranch (Nat.cast ((p^k+1)/2)))=2) :
    L.length=1 ∨ L.length+1=p^k := by
  exact obstruction_cardinality hp hn hpos hlt
    (two_boundary_annihilator L hL _ (power_half hp hn) (three_injective hp hn) hb)

/-- Zero boundary is impossible for a nonempty proper set. -/
theorem zero_boundary_impossible {p k : Nat} [NeZero (p^k)]
    (hp : PrimeModulus p) (hn : 7<p)
    (L : List (Fin (p^k))) (hL : L.Nodup) (hpos : 0<L.length) (hlt : L.length<p^k) :
    boundary L (fun z => 2*z) +
      boundary L (oddBranch (Nat.cast ((p^k+1)/2))) ≠ 0 := by
  intro hb
  let u : Fin (p^k) := Nat.cast ((p^k+1)/2)
  have hu : 2*u=1 := power_half hp hn
  have hi2 : ∀ a b : Fin (p^k), 2*a=2*b → a=b := by
    intro a b h
    have hh := congrArg (fun z => u*z) h
    grind
  have hiA : ∀ a b : Fin (p^k), oddBranch u a=oddBranch u b → a=b := by
    intro a b h
    apply three_injective hp hn
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
  have hmap : (fun z : Fin (p^k) => 2*oddBranch u z) = (fun z => 3*z+1) := by
    funext z; simp only [oddBranch]; grind
  have ha' := ha.map (fun z => 2*z)
  simp only [List.map_map, Function.comp_def, hmap] at ha'
  have hz := invariant_card_zero L ha' hd
  rw [moment_zero] at hz
  have hz' := (IsCharP.natCast_eq_zero_iff (α := Fin (p^k)) (p^k) L.length).mp hz
  rw [Nat.mod_eq_of_lt hlt] at hz'
  omega

/-- The sharp nontrivial-cut bound survives all prime-power thickenings. -/
theorem four_le_boundary {p k : Nat} [NeZero (p^k)]
    (hp : PrimeModulus p) (hn : 7<p)
    (L : List (Fin (p^k))) (hL : L.Nodup) (hpos : 2≤L.length) (hlt : L.length+2≤p^k) :
    4 ≤ boundary L (fun z => 2*z) +
      boundary L (oddBranch (Nat.cast ((p^k+1)/2))) := by
  let u : Fin (p^k) := Nat.cast ((p^k+1)/2)
  have hu : 2*u=1 := power_half hp hn
  have hi2 : ∀ a b : Fin (p^k), 2*a=2*b → a=b := by
    intro a b h
    have hh := congrArg (fun z => u*z) h
    grind
  have hiA : ∀ a b : Fin (p^k), oddBranch u a=oddBranch u b → a=b := by
    intro a b h
    apply three_injective hp hn
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

/-- The lower bound four is attained by {1,2}, uniformly in the modulus. -/
theorem pair_boundary_sharp {m : Nat} [NeZero m] (hm : 7<m)
    (u : Fin m) (hu : 2*u=1) :
    boundary ([1,2] : List (Fin m)) (fun z => 2*z) +
      boundary ([1,2] : List (Fin m)) (oddBranch u)=4 := by
  have small_ne {a b : Nat} (ha : a<m) (hb : b<m) (hne : a≠b) :
      (Nat.cast a : Fin m) ≠ Nat.cast b := by
    intro h
    exact hne ((IsCharP.natCast_eq_iff_of_lt (α := Fin m) m ha hb).mp h)
  have h12 : (1 : Fin m) ≠ 2 := small_ne (a := 1) (b := 2) (by omega) (by omega) (by decide)
  have h14 : (1 : Fin m) ≠ 4 := small_ne (a := 1) (b := 4) (by omega) (by omega) (by decide)
  have h24 : (2 : Fin m) ≠ 4 := small_ne (a := 2) (b := 4) (by omega) (by omega) (by decide)
  have h72 : (7 : Fin m) ≠ 2 := small_ne (a := 7) (b := 2) (by omega) (by omega) (by decide)
  have h74 : (7 : Fin m) ≠ 4 := small_ne (a := 7) (b := 4) (by omega) (by omega) (by decide)
  have ha1 : oddBranch u 1=2 := by unfold oddBranch; grind
  have ha2 : 2*oddBranch u 2=7 := by unfold oddBranch; grind
  have hA1 : oddBranch u 2 ≠ 1 := by
    intro h
    rw [h] at ha2
    grind
  have hA2 : oddBranch u 2 ≠ 2 := by
    intro h
    rw [h] at ha2
    grind
  have hd1 : (2 : Fin m)*1=2 := by grind
  have hd2 : (2 : Fin m)*2=4 := by grind
  simp [boundary,outside,ha1,hd1,hd2,h12,h14,h24,hA1,hA2,
    Ne.symm h12,Ne.symm h14,Ne.symm h24,Ne.symm hA1,Ne.symm hA2]

/-- Sharpness at every positive power of every prime greater than seven. -/
theorem prime_power_sharp {p k : Nat} [NeZero (p^k)]
    (hp : PrimeModulus p) (hn : 7<p) (hk : 0<k) :
    boundary ([1,2] : List (Fin (p^k))) (fun z => 2*z) +
      boundary ([1,2] : List (Fin (p^k)))
        (oddBranch (Nat.cast ((p^k+1)/2)))=4 := by
  have hle : p≤p^k := Nat.le_pow hk
  exact pair_boundary_sharp (by omega) _ (power_half hp hn)

end Collatz.PrimePowerBoundary
