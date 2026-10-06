import Collatz.Strategy.PrimeBoundary

open Collatz BoundaryMoments BoundaryCuts PrimeBoundary

#print axioms Collatz.BoundaryMoments.centered_moment_obstruction
#print axioms Collatz.BoundaryMoments.doubling_moment_obstruction
#print axioms Collatz.BoundaryMoments.invariant_card_zero
#print axioms Collatz.BoundaryMoments.centered_exchange_obstruction
#print axioms Collatz.BoundaryMoments.doubling_exchange_obstruction
#print axioms Collatz.BoundaryMoments.affine_exchange_obstruction
#print axioms Collatz.BoundaryCuts.one_exchange
#print axioms Collatz.BoundaryCuts.two_boundary_obstruction
#print axioms Collatz.BoundaryCuts.two_boundary_annihilator
#print axioms Collatz.PrimeBoundary.fin_no_zero_divisors
#print axioms Collatz.PrimeBoundary.annihilator_roots
#print axioms Collatz.PrimeBoundary.prime_half
#print axioms Collatz.PrimeBoundary.two_boundary_cardinality
#print axioms Collatz.PrimeBoundary.zero_boundary_impossible
#print axioms Collatz.PrimeBoundary.four_le_boundary

-- Sharp exceptional primes, evaluated through the actual branch maps.
example : boundary ([1,2] : List (Fin 5)) (fun z => 2*z) +
    boundary ([1,2] : List (Fin 5)) (oddBranch 3)=2 := by decide
example : boundary ([3,5,6] : List (Fin 7)) (fun z => 2*z) +
    boundary ([3,5,6] : List (Fin 7)) (oddBranch 4)=2 := by decide

-- Their sizes do not satisfy the cubic without the exceptional factor.
example : (2 : Fin 5)*((2 : Fin 5)^2-1) ≠ 0 := by decide
example : (3 : Fin 7)*((3 : Fin 7)^2-1) ≠ 0 := by decide

-- The first three centered moment equations alone cannot remove prime 19.
-- This is algebraic data, not a claim that a vertex set realizes these moments.
example :
    let q : Fin 19 := 2
    let x : Fin 19 := 10
    let y : Fin 19 := 8
    let p1 : Fin 19 := 0
    let p2 : Fin 19 := 0
    let p3 : Fin 19 := 12
    p1=0 ∧ 5*p2=0 ∧ 19*p3=0 ∧
    y-x=p1-q ∧ y^2-x^2=3*p2-4*p1+q ∧
    y^3-x^3=7*p3-12*p2+6*p1-q ∧ 5*q*(q^2-1) ≠ 0 := by decide

-- The lower bound four is attained by a nonsingleton cut at p=11.
example : boundary ([1,2] : List (Fin 11)) (fun z => 2*z) +
    boundary ([1,2] : List (Fin 11)) (oddBranch 6)=4 := by decide

-- The four-moment coefficient 5 applies even in characteristic 19.
example (L : List (Fin 19)) (x y : Fin 19)
    (ha : (L.map (fun z => 3*z+1)).Perm (L.map (fun z => 2*z)))
    (hd : (x :: L.map (fun z => 2*z)).Perm (y :: L)) :
    5*moment L 0*((moment L 0)^2-1)=0 := affine_exchange_obstruction L x y ha hd

-- No upper bound on the prime is present in the final statement.
example (p : Nat) [NeZero p] (hp : PrimeModulus p) (hn : 7<p)
    (L : List (Fin p)) (hL : L.Nodup) (hpos : 2≤L.length) (hlt : L.length+2≤p) :
    4 ≤ boundary L (fun z => 2*z) +
      boundary L (oddBranch (Fin.ofNat p ((p+1)/2))) := by
  exact four_le_boundary hp hn L hL hpos hlt
