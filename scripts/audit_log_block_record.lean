import Collatz.Strategy.LogBlockRecord
#print axioms Collatz.LogBlockRecord.staysAbove_sound
#print axioms Collatz.LogBlockRecord.no_drop_certificate
#print axioms Collatz.LogBlockRecord.exact_stopping_time
#print axioms Collatz.LogBlockRecord.seed_log2
#print axioms Collatz.LogBlockRecord.not_log_bound
#print axioms Collatz.LogBlockRecord.not_tail_bound
example : ¬ (∀ n : Nat, 1 < n → ∃ k,
    k ≤ 17 * Nat.log2 n ∧ Collatz.acceleratedOrbit k n < n) :=
  Collatz.LogBlockRecord.not_log_bound (by decide)
example : ¬ (∀ n : Nat, 1 < n → ∃ k,
    k ≤ 18 * Nat.log2 n ∧ Collatz.acceleratedOrbit k n < n) :=
  Collatz.LogBlockRecord.not_log_bound (by decide)
