import Collatz.Exploration.ComputedClassWitness
import Collatz.Exploration.HalvingBlocks

/-!
# Quantitative successful times for constructed class witnesses

The finite modular search constructs a special convergent member of each dyadic
class. Its proof can supply a successful standard time, rather than just a
convergence proposition. The prefix has at most twice its accelerated length;
the tail costs exactly the raised exponent many halvings.

For a fixed class the resulting bound grows with the binary length of the
requested lower bound. The constant contains two ternary exponent periods and
can be very large. This is a bound for the chosen member only, and does not
bound the stopping time of an arbitrary input in the same class.
-/
namespace Collatz.Exploration.ClassWitnessCost

open ComputedClassWitness ExponentRaise ExponentSearch HalvingBlocks
open TimeChange Congruence

/-- Explicit standard time attached to a successful modular search result. -/
def witnessTime (k r N e : Nat) : Nat :=
  raiseExponent (oddCount r k) e (3^(oddCount r k)*N+acceleratedOrbit k r) +
    clock (2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r) k

/-- The time function is a real successful standard time, with no replay search. -/
theorem witnessTime_hits {k r N e : Nat}
    (he : findUnitExponent (oddCount r k) (acceleratedOrbit k r) = some e) :
    orbit (witnessTime k r N e)
      (2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r) = 1 := by
  have hm := (matchingIndex_spec (N := N) (findUnitExponent_sound he).2).2
  have hend : acceleratedOrbit k
      (2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r) =
      2^(raiseExponent (oddCount r k) e
        (3^(oddCount r k)*N+acceleratedOrbit k r)) := by
    rw [accOrbit_pow_two_mul_add, hm]
  exact endpoint_hits hend

/-- The successful time is logarithmic in the affine lower bound, with an
explicit class-dependent overhead. -/
theorem witnessTime_bound {k r N e : Nat}
    (he : findUnitExponent (oddCount r k) (acceleratedOrbit k r) = some e) :
    witnessTime k r N e < 2*k+
      bitLength (3^(oddCount r k)*N+acceleratedOrbit k r)+
      2*periodLength (oddCount r k) := by
  have hx := chosen_exponent_bound (N := N) he
  have hc := (clock_bounds
    (2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r) k).2
  unfold witnessTime
  omega

/-- Every returned witness comes with a bounded successful standard time. -/
theorem returned_time_bound {k r N n : Nat} (h : classWitness k r N = some n) :
    ∃ t, orbit t n = 1 ∧ t < 2*k+
      bitLength (3^(oddCount r k)*N+acceleratedOrbit k r)+
      2*periodLength (oddCount r k) := by
  unfold classWitness at h
  cases he : findUnitExponent (oddCount r k) (acceleratedOrbit k r) with
  | none => simp [he] at h
  | some e =>
    have hn : 2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r = n := by
      simpa [he] using h
    refine ⟨witnessTime k r N e, ?_, witnessTime_bound he⟩
    rw [← hn]
    exact witnessTime_hits he

/-- A quantitative existence statement combining class membership and time. -/
theorem quantitative_class_member (k r N : Nat) : ∃ n t,
    N < n ∧ n%2^k = r%2^k ∧ orbit t n = 1 ∧
      t < 2*k+bitLength (3^(oddCount r k)*N+acceleratedOrbit k r)+
        2*periodLength (oddCount r k) := by
  obtain ⟨n, hn⟩ := classWitness_success k r N
  obtain ⟨hlarge, hclass, _⟩ := classWitness_sound hn
  obtain ⟨t, ht, hb⟩ := returned_time_bound hn
  exact ⟨n, t, hlarge, hclass, ht, hb⟩

end Collatz.Exploration.ClassWitnessCost
