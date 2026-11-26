import IncrementCycles

open IncrementCycles

-- Eq. (2): physical pair reversal for a stationary pair law.
example : ∀ (J : Pair), stationary J →
    (reversePair J = J ↔ q1 J = 0 ∧ q2 J = 0) :=
  pair_iff

-- Eq. (4): the pause-count imbalance is an endpoint term.
example : ∀ (start : S) (tail : List S),
    (count S.E S.P start tail - count S.P S.R start tail) -
    (count S.P S.E start tail - count S.R S.P start tail) =
      indicator (endpoint start tail) S.P - indicator start S.P :=
  finite_window
