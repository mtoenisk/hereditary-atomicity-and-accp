import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Finite generation of the maximal ideal in dimension at most one

In a local domain of Krull dimension at most one, every nonzero prime ideal is
the maximal ideal. If that ideal is finitely generated, Cohen's criterion gives
Noetherianity, and hence ACCP. These are local-algebra statements independent of
hereditary atomicity and of the arithmetic structure used to obtain dimension
at most one in the HA application.
-/

namespace HereditaryAtomicity

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Ring.KrullDimLE 1 R]

/-- A local domain of Krull dimension at most one with finitely generated
maximal ideal is Noetherian. The zero ideal needs no extra finite-generation
hypothesis in Cohen's criterion. -/
theorem local_isNoetherianRing_of_fg_maximalIdeal
    (hfg : (IsLocalRing.maximalIdeal R).FG) : IsNoetherianRing R := by
  apply IsNoetherianRing.of_prime_ne_bot
  intro P hP hP0
  have hPm : P = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (hP.isMaximal_of_ne_bot hP0)
  exact hPm.symm ▸ hfg

/-- A local domain of Krull dimension at most one with finitely generated
maximal ideal satisfies ACCP, expressed by well-founded strict divisibility. -/
theorem local_wfDvdMonoid_of_fg_maximalIdeal
    (hfg : (IsLocalRing.maximalIdeal R).FG) : WfDvdMonoid R := by
  let : IsNoetherianRing R := local_isNoetherianRing_of_fg_maximalIdeal hfg
  infer_instance

end HereditaryAtomicity
