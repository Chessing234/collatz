import Collatz.Exploration.ExponentRaise
import Collatz.Exploration.DyadicConvergentClasses

/-!
# Computable convergent witnesses in dyadic classes

`classWitness k r N` searches a finite ternary exponent period, raises the
selected exponent only when necessary, and returns an input 2^k*m+r with m>N.
Its accelerated endpoint is a power of two, so the returned input reaches 1.

Both termination of the modular search and soundness of the returned input are
proved. The function constructs *one member* of a requested class. It does not
verify arbitrary members and is not a universal convergence algorithm.
-/
namespace Collatz.Exploration.ComputedClassWitness

open ExponentSearch ExponentRaise AffinePowerMatch DyadicConvergentClasses
open OrbitFloor Reach Congruence

/-- The explicit nonnegative affine index obtained from a raised matching power. -/
def matchingIndex (a B N e : Nat) : Nat :=
  ((2:Nat)^(raiseExponent a e (3^a*N+B))-B)/3^a

/-- The quotient used by the algorithm is exact and exceeds the requested index. -/
theorem matchingIndex_spec {a B N e : Nat} (hbase : (2:Nat)^e%3^a = B%3^a) :
    N < matchingIndex a B N e ∧
      3^a*matchingIndex a B N e+B = (2:Nat)^(raiseExponent a e (3^a*N+B)) := by
  have hlarge := raised_power_large a e (3^a*N+B)
  have hmod : (2:Nat)^(raiseExponent a e (3^a*N+B))%3^a = B%3^a :=
    (raised_power_residue a e (3^a*N+B)).trans hbase
  have hB : B ≤ (2:Nat)^(raiseExponent a e (3^a*N+B)) := by omega
  obtain ⟨m, hm⟩ := translate_of_residue hB hmod
  have hidx : matchingIndex a B N e = m := by
    unfold matchingIndex
    rw [← hm, Nat.add_sub_cancel_right,
      Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < (3:Nat)))]
  rw [hidx]
  exact ⟨index_large hm hlarge, hm⟩

/-- A requested class witness, or none if the modular search were to fail. -/
def classWitness (k r N : Nat) : Option Nat :=
  (findUnitExponent (oddCount r k) (acceleratedOrbit k r)).map fun e =>
    2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r

/-- Every matched positive-index endpoint proves convergence of its initial value. -/
theorem converges_of_match {k r m e : Nat} (hm : 0 < m)
    (he : 3^(oddCount r k)*m+acceleratedOrbit k r = (2:Nat)^e) :
    Converges (2^k*m+r) := by
  have hp : 0 < 2^k*m+r := by
    have h := Nat.mul_pos (Nat.two_pow_pos k) hm
    omega
  have hend : acceleratedOrbit k (2^k*m+r) = 2^e := by
    rw [accOrbit_pow_two_mul_add, he]
  apply reachesOne_of_accOrbit (k := k) hp
  rw [hend]
  exact reachesOne_two_pow e

/-- Every returned input is large, is in the requested class, and actually reaches 1. -/
theorem classWitness_sound {k r N n : Nat} (h : classWitness k r N = some n) :
    N < n ∧ n%2^k = r%2^k ∧ Converges n := by
  unfold classWitness at h
  cases hf : findUnitExponent (oddCount r k) (acceleratedOrbit k r) with
  | none => simp [hf] at h
  | some e =>
    have hn : 2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r = n := by
      simpa [hf] using h
    have hbase := (findUnitExponent_sound hf).2
    obtain ⟨hm, he⟩ := matchingIndex_spec (N := N) hbase
    have hscale : matchingIndex (oddCount r k) (acceleratedOrbit k r) N e ≤
        2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e := by
      have hp : 1 ≤ 2^k := Nat.two_pow_pos k
      have hh := Nat.mul_le_mul_right
        (matchingIndex (oddCount r k) (acceleratedOrbit k r) N e) hp
      simpa using hh
    refine ⟨by omega, ?_, ?_⟩
    · rw [← hn]
      simp [Nat.add_mod]
    · rw [← hn]
      exact converges_of_match (by omega) he

/-- The modular premise always holds for a Collatz parity-class endpoint. -/
theorem classWitness_success (k r N : Nat) : ∃ n, classWitness k r N = some n := by
  obtain ⟨e, he, _, _⟩ := findUnitExponent_success (oddCount r k) (acceleratedOrbit k r)
    (affine_matching_premise k r)
  exact ⟨2^k*matchingIndex (oddCount r k) (acceleratedOrbit k r) N e+r,
    by simp [classWitness, he]⟩

/-- This combines executable construction and its complete specification. -/
theorem classWitness_total (k r N : Nat) :
    ∃ n, classWitness k r N = some n ∧ N < n ∧ n%2^k = r%2^k ∧ Converges n := by
  obtain ⟨n, hn⟩ := classWitness_success k r N
  exact ⟨n, hn, classWitness_sound hn⟩

/-- A returned exponent is controlled by the binary length plus two ternary
periods, rather than by the numerical magnitude of the requested endpoint. -/
theorem chosen_exponent_bound {a B N e : Nat}
    (he : findUnitExponent a B = some e) :
    raiseExponent a e (3^a*N+B) < bitLength (3^a*N+B)+2*periodLength a := by
  have hf := (findUnitExponent_sound he).1
  have hr := raise_size_bound a e (3^a*N+B)
  omega

end Collatz.Exploration.ComputedClassWitness
