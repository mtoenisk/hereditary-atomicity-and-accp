import UnconditionalCounterexample.SparseAtoms
import UnconditionalCounterexample.PicardProfiles

/-! Elementary realized-construction data shared by the sparse ideal and
principal profile calculations. No ideal realization or principal relation
conclusion is assumed in this bundle. -/

noncomputable section
namespace UnconditionalCounterexample.SparseProfileData
open Polynomial GuardSupport

structure Data where
  raw : ℕ → ℚ[X]
  exponent : ℕ → ℕ
  places : SparsePrimaryDomain.Places
  monic_irreducible : ∀ i, (raw i).Monic ∧ Irreducible (raw i)
  raw_injective : Function.Injective raw
  constant_ne_zero : ∀ i, (raw i).coeff 0 ≠ 0
  columns : SparseProfiles.GeneratorProfiles raw exponent places
  first : (places.primary 0).val.valuation = 2
  guard_unit : ∀ p, IsUnit (places.guard p)
  guardSupport : ∀ x : RatFunc ℚ, x ≠ 0 →
    {p : PrimeIndex | SparsePrimaryDomain.vertical places (.inr p) x ≠ 1}.Finite

namespace Data
abbrev poles (A : Data) := Set.range A.raw
abbrev domain (A : Data) := SparsePrimaryDomain.domain A.poles A.places
abbrev Outside (A : Data) := SparseProfiles.Outside A.poles
abbrev Label (A : Data) := ProfilePlace A.Outside
abbrev Group (A : Data) := PicardProfiles.Profile A.Outside
abbrev valuations (A : Data) := SparseProfiles.valuations A.poles A.places
abbrev generators (A : Data) := SparseProfiles.generators A.raw A.exponent

theorem raw_ne_zero (A : Data) (i : ℕ) : A.raw i ≠ 0 := (A.monic_irreducible i).1.ne_zero

theorem constant_nonzero (A : Data) : ∀ q ∈ A.poles, q.coeff 0 ≠ 0 := by
  rintro q ⟨i, rfl⟩
  exact A.constant_ne_zero i

theorem generators_ne_zero (A : Data) (i : ℕ) : A.generators i ≠ 0 :=
  ReturnPrefix.generators_ne_zero A.raw A.exponent A.raw_ne_zero i

theorem fractionRing (A : Data) : IsFractionRing A.domain (RatFunc ℚ) :=
  SparsePrimaryDomain.fractionRing A.poles A.places

/-- The proved actual natural-order profile, as a convenience for shared consumers. -/
abbrev profiles (A : Data) : ValuationProfiles A.domain A.Outside :=
  SparseProfiles.profiles A.raw A.monic_irreducible A.raw_injective A.constant_ne_zero
    A.exponent A.places A.columns A.guardSupport

theorem profiles_cast (A : Data) (l : A.Label) (x : A.domain) (hx : x ≠ 0) :
    (A.profiles.value l x : ℤ) = DiscreteOrders.order (A.valuations l) (x : RatFunc ℚ) :=
  SparseProfiles.profiles_value_cast A.raw A.monic_irreducible A.raw_injective A.constant_ne_zero
    A.exponent A.places A.columns A.guardSupport l x hx

theorem integerLocalization (A : Data) :
    IsLocalization (IntersectionDomain.integerDenominators A.domain) (PoleAlgebra.generated A.poles) :=
  SparsePrimaryDomain.integerLocalization_of_guard_support A.places A.constant_nonzero A.guardSupport

end Data
end UnconditionalCounterexample.SparseProfileData
