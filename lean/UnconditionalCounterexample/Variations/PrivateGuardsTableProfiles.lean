import UnconditionalCounterexample.Variations.PrivateGuardsProfiles
import UnconditionalCounterexample.Variations.PrivateGuardsRealizedProfiles

/-! # Signed profiles on the actual public and private table -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MultivariateSelection WithZero

variable {r d : ℕ} {k : Type*} [Field k] [CharZero k]
    (P : TablePolicy r k) (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)

/-- The retained polynomial coordinate and the public valuation support of the
same table realize the signed profiles and divisibility test in its punctured ring. -/
theorem actualProfileValues : ProfileValues C (tableRule P q c)
    (publicPrimary P q c C) (publicGuard P q c C) where
  toMovingValues := actualMovingValues P q c C
  retained := table_retained C _ _ P q
  guard_above p := by
    let T := publicPath P q c C
    exact (show publicGuard P q c C p (p.val : FunctionField (r+1)) = exp (-1) from
      ((T.places.guard p).valuation_natCast _).trans (T.places.guard_prime p)) ▸ (by decide : exp (-1 : ℤ) < 1)
  primary_late x _ := (publicPath P q c C).primary_eventually x
  guard_finite x hx := (publicPath P q c C).finite_guard x hx

end UnconditionalCounterexample.Variations.PrivateGuards.Live
