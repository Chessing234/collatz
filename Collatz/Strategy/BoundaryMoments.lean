import Collatz.Basic

/-!
Power-sum obstructions to a single exchange under a modular Collatz branch.
The statements hold in every commutative ring, including `Fin m` for `m > 0`.
List permutation records exact multisets; no probabilistic premise is used.
These results concern modular boundaries, not convergence of integer orbits.
-/
namespace Collatz.BoundaryMoments
open Lean.Grind
attribute [local instance] Semiring.natCast

variable {R : Type} [CommRing R]

/-- The j-th power sum, with multiplicity. -/
def moment (L : List R) (j : Nat) : R :=
  match L with
  | [] => 0
  | z :: zs => z^j + moment zs j

@[simp] theorem moment_nil (j : Nat) : moment ([] : List R) j = 0 := rfl
@[simp] theorem moment_cons (z : R) (L : List R) (j : Nat) :
    moment (z :: L) j = z^j + moment L j := rfl

theorem moment_perm {L K : List R} (h : L.Perm K) (j : Nat) :
    moment L j = moment K j := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [moment_cons, ih]
  | swap a b l => simp only [moment_cons]; grind
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem moment_zero (L : List R) : moment L 0 = (Nat.cast L.length : R) := by
  induction L with
  | nil => simp [moment]; grind
  | cons z zs ih => simp only [moment_cons, List.length_cons]; grind

theorem moment_map_mul (L : List R) (a : R) (j : Nat) :
    moment (L.map (fun z => a*z)) j = a^j*moment L j := by
  induction L with
  | nil => simp only [List.map_nil, moment_nil]; grind
  | cons z zs ih =>
    simp only [List.map_cons, moment_cons, ih, CommSemiring.mul_pow]
    grind

theorem moment_affine_one (L : List R) (a b : R) :
    moment (L.map (fun z => a*z+b)) 1 = a*moment L 1+b*moment L 0 := by
  induction L with
  | nil => simp only [List.map_nil, moment_nil]; grind
  | cons z zs ih => simp only [List.map_cons, moment_cons, ih]; grind

theorem moment_affine_two (L : List R) (a b : R) :
    moment (L.map (fun z => a*z+b)) 2 =
      a^2*moment L 2+2*a*b*moment L 1+b^2*moment L 0 := by
  induction L with
  | nil => simp only [List.map_nil, moment_nil]; grind
  | cons z zs ih => simp only [List.map_cons, moment_cons, ih]; grind

theorem moment_affine_three (L : List R) (a b : R) :
    moment (L.map (fun z => a*z+b)) 3 =
      a^3*moment L 3+3*a^2*b*moment L 2+3*a*b^2*moment L 1+b^3*moment L 0 := by
  induction L with
  | nil => simp only [List.map_nil, moment_nil]; grind
  | cons z zs ih => simp only [List.map_cons, moment_cons, ih]; grind

theorem moment_affine_four (L : List R) (a b : R) :
    moment (L.map (fun z => a*z+b)) 4 =
      a^4*moment L 4+4*a^3*b*moment L 3+6*a^2*b^2*moment L 2+
        4*a*b^3*moment L 1+b^4*moment L 0 := by
  induction L with
  | nil => simp only [List.map_nil, moment_nil]; grind
  | cons z zs ih => simp only [List.map_cons, moment_cons, ih]; grind

/-- Four centered moments remove the spurious cubic exceptional prime 19. -/
theorem centered_moment_obstruction (q x y p1 p2 p3 p4 : R)
 (h1 : p1=0) (h2 : 5*p2=0) (h3 : 19*p3=0) (h4 : 65*p4=0)
 (b1 : y-x=p1-q)
 (b2 : y^2-x^2=3*p2-4*p1+q)
 (b3 : y^3-x^3=7*p3-12*p2+6*p1-q)
 (b4 : y^4-x^4=15*p4-32*p3+24*p2-8*p1+q) :
 5*q*(q^2-1)=0 := by
 have hd : y-x = -q := by clear h2 h3 h4 b2 b3 b4; grind
 have hs : 5*q*(x+y+1)=0 := by
  clear h3 h4 b3 b4
  have hb : 5*(y^2-x^2)=5*q := by grind
  clear b1 b2 h1 h2
  grind
 have h95 : 95*q*(q^2-1)=0 := by
  clear h4 b4
  have hb : 95*(y^3-x^3) = -95*q := by grind
  clear h1 h2 h3 b1 b2 b3
  have ht : 95*q*(3*(x+y)^2+q^2-4)=0 := by clear hs; grind
  have hh : 95*q*(3*(x+y)^2-3)=0 := by
   clear ht hb hd
   have h := congrArg (fun z : R => 57*(x+y-1)*z) hs
   grind
  clear hs hb hd
  grind
 have h1170 : 1170*q*(q^2-1)=0 := by
  clear h3 h95
  have hb : 65*(7*(y^4-x^4)+32*(y^3-x^3)+25*q)=0 := by
   rw [b4, b3, h1]
   clear hd hs b1 b2 b3 b4 h1
   have h2a := congrArg (fun z : R => 2808*z) h2
   have h4a := congrArg (fun z : R => 105*z) h4
   grind
  clear h1 h2 h4 b1 b2 b3 b4
  have ht : 65*q*(14*(x+y)*((x+y)^2+q^2)+32*(3*(x+y)^2+q^2)-100)=0 := by
   clear hs
   grind
  clear hb hd
  have hh : 65*q*(14*(x+y)*((x+y)^2+q^2)+32*(3*(x+y)^2+q^2)-100) =
      1170*q*(q^2-1) := by
   clear ht
   have h := congrArg (fun z : R => 13*(14*(x+y)^2+82*(x+y)+14*q^2-82)*z) hs
   grind
  grind
 clear h1 h2 h3 h4 b1 b2 b3 b4 hd hs
 calc
  5*q*(q^2-1) = 37*(95*q*(q^2-1))-3*(1170*q*(q^2-1)) := by
   clear h95 h1170
   grind
  _ = 0 := by rw [h95, h1170]; grind

/-- The complementary branch configuration has a cubic obstruction. -/
theorem doubling_moment_obstruction (q x y m1 m2 m3 : R)
 (h1 : m1=0) (h2 : 3*m2=0) (h3 : 7*m3=0)
 (b1 : 2*(y-x)=m1+q)
 (b2 : 4*(y^2-x^2)=5*m2+6*m1+q)
 (b3 : 8*(y^3-x^3)=19*m3+27*m2+9*m1+q) :
 21*q*(q^2-1)=0 := by
 have hd : 2*(y-x)=q := by clear h2 h3 b2 b3; grind
 have hs : 3*q*(2*(x+y)-1)=0 := by
  clear b3 h3
  have hb : 12*(y^2-x^2)=3*q := by grind
  clear b2 b1 h1 h2
  grind
 have ht : 21*q*(12*(x+y)^2+q^2-4)=0 := by
  clear b1 b2 hs
  have hb : 168*(y^3-x^3)=21*q := by grind
  clear b3 h1 h2 h3
  grind
 clear b1 b2 b3 h1 h2 h3 hd
 have hh : 21*q*(12*(x+y)^2-3)=0 := by
  clear ht
  have h := congrArg (fun z : R => 21*(2*(x+y)+1)*z) hs
  grind
 clear hs
 grind

/-- First moments already exclude a proper common invariant set over a prime field. -/
theorem invariant_card_zero (L : List R)
    (ha : (L.map (fun z => 3*z+1)).Perm (L.map (fun z => 2*z)))
    (hd : (L.map (fun z => 2*z)).Perm L) : moment L 0=0 := by
  have h1 := moment_perm ha 1
  have h2 := moment_perm hd 1
  simp only [moment_affine_one, moment_map_mul] at h1 h2
  grind

/-- Center at the odd branch fixed point -1. An invariant odd branch and
one doubling exchange force the cardinality obstruction with coefficient 5. -/
theorem centered_exchange_obstruction (L : List R) (x y : R)
    (ha : (L.map (fun z => 3*z)).Perm (L.map (fun z => 2*z)))
    (hd : (x :: L.map (fun z => 2*z-1)).Perm (y :: L)) :
    5*moment L 0*((moment L 0)^2-1)=0 := by
  have h1 := moment_perm ha 1
  have h2 := moment_perm ha 2
  have h3 := moment_perm ha 3
  have h4 := moment_perm ha 4
  simp only [moment_map_mul] at h1 h2 h3 h4
  have b1 := moment_perm hd 1
  have b2 := moment_perm hd 2
  have b3 := moment_perm hd 3
  have b4 := moment_perm hd 4
  have he : (fun z : R => 2*z-1) = (fun z => 2*z+(-1)) := by funext z; grind
  rw [he] at b1 b2 b3 b4
  simp only [moment_cons, moment_affine_one, moment_affine_two,
    moment_affine_three, moment_affine_four] at b1 b2 b3 b4
  apply centered_moment_obstruction (moment L 0) x y
    (moment L 1) (moment L 2) (moment L 3) (moment L 4)
  · clear h2 h3 h4 b1 b2 b3 b4; grind
  · clear h1 h3 h4 b1 b2 b3 b4; grind
  · clear h1 h2 h4 b1 b2 b3 b4; grind
  · clear h1 h2 h3 b1 b2 b3 b4; grind
  · clear h1 h2 h3 h4 b2 b3 b4; grind
  · clear h1 h2 h3 h4 b1 b3 b4; grind
  · clear h1 h2 h3 h4 b1 b2 b4; grind
  · clear h1 h2 h3 h4 b1 b2 b3; grind

/-- An invariant doubling branch and one odd-branch exchange. No division
by 2 is needed: the image identity is multiplied through by 2. -/
theorem doubling_exchange_obstruction (L : List R) (x y : R)
    (hd : (L.map (fun z => 2*z)).Perm L)
    (ha : (2*x :: L.map (fun z => 3*z+1)).Perm
      (2*y :: L.map (fun z => 2*z))) :
    21*moment L 0*((moment L 0)^2-1)=0 := by
  have h1 := moment_perm hd 1
  have h2 := moment_perm hd 2
  have h3 := moment_perm hd 3
  simp only [moment_map_mul] at h1 h2 h3
  have b1 := moment_perm ha 1
  have b2 := moment_perm ha 2
  have b3 := moment_perm ha 3
  simp only [moment_cons, moment_affine_one, moment_affine_two,
    moment_affine_three, moment_map_mul] at b1 b2 b3
  apply doubling_moment_obstruction (moment L 0) x y
    (moment L 1) (moment L 2) (moment L 3)
  · clear h2 h3 b1 b2 b3; grind
  · clear h1 h3 b1 b2 b3; grind
  · clear h1 h2 b1 b2 b3; grind
  · clear h1 h2 h3 b2 b3; grind
  · clear h1 h2 h3 b1 b3; grind
  · clear h1 h2 h3 b1 b2; grind

/-- The original, unshifted Collatz branch equations imply the centered
conditions above, hence the coefficient-5 obstruction. -/
theorem affine_exchange_obstruction (L : List R) (x y : R)
    (ha : (L.map (fun z => 3*z+1)).Perm (L.map (fun z => 2*z)))
    (hd : (x :: L.map (fun z => 2*z)).Perm (y :: L)) :
    5*moment L 0*((moment L 0)^2-1)=0 := by
  have ha' := ha.map (fun z => z+2)
  have hd' := hd.map (fun z => z+1)
  have hmap1 : (fun z : R => 3*z+1+2) = (fun z => 3*(z+1)) := by
    funext z; grind
  have hmap2 : (fun z : R => 2*z+2) = (fun z => 2*(z+1)) := by
    funext z; grind
  have hmap3 : (fun z : R => 2*z+1) = (fun z => 2*(z+1)-1) := by
    funext z; grind
  have hac : ((L.map (fun z => z+1)).map (fun z => 3*z)).Perm
      ((L.map (fun z => z+1)).map (fun z => 2*z)) := by
    simpa only [List.map_map, Function.comp_def, hmap1, hmap2] using ha'
  have hdc : ((x+1) :: (L.map (fun z => z+1)).map (fun z => 2*z-1)).Perm
      ((y+1) :: L.map (fun z => z+1)) := by
    simpa only [List.map_cons, List.map_map, Function.comp_def, hmap3] using hd'
  have h := centered_exchange_obstruction (L.map (fun z => z+1)) (x+1) (y+1) hac hdc
  simpa only [moment_zero, List.length_map] using h

end Collatz.BoundaryMoments
