import UnconditionalCounterexample.Variations.PrivateGuardsMoving
import UnconditionalCounterexample.Variations.MultiDomainIntegerReturns

/-! # Integer divisibility across every branch of the punctured domain -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MultiDomain Filter IntersectionDomain WithZero

variable {r d : ℕ} {c : Fin (r+1) → ℚ} {M : ℕ → Type*} (C : Config r d) (L : Rule r M c)
local notation "K" => FunctionField (r+1)
variable (π : ℕ → Valuation (FunctionField (r+1)) ℤᵐ⁰) (γ : PrimeIndex → Valuation (FunctionField (r+1)) ℤᵐ⁰) (primes : ℕ → PrimeIndex)
local notation "V" => branchVal C L π γ
local notation "D" => domain C L π γ

private theorem finite_integer_branches (hinj : Function.Injective primes) (m : ℕ) :
    {i | (branchPrime C L primes i).val ∈ m.primeFactors}.Finite := by
  let S := (m.primeFactors : Set ℕ)
  have hS : S.Finite := m.primeFactors.finite_toSet
  apply Set.finite_preimage_inl_and_inr.mp
  constructor
  · apply Set.finite_preimage_inl_and_inr.mp
    change ((Subtype.val ∘ primes) ⁻¹' S).Finite ∧ ((Subtype.val : PrimeIndex → ℕ) ⁻¹' S).Finite
    exact ⟨hS.preimage (Subtype.val_injective.comp hinj).injOn,hS.preimage Subtype.val_injective.injOn⟩
  · let f := fun n ↦ ((family C L).prime n).val
    have hf : (f ⁻¹' S).Finite := hS.preimage (family C L).prime_increasing.injective.injOn
    exact (hf.prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset fun ⟨_,_⟩ h ↦ ⟨h,Set.mem_univ _⟩

theorem integer_return (hinj : Function.Injective primes) (H : MovingValues C L π γ)
    (hp : ∀ i, (V) i ((branchPrime C L primes i).val : K) = exp (-1))
    (hret : ∀ i, ∀ᶠ n in atTop, (V) i ((movingValue C L n - 1)/(↑(branchPrime C L primes i).val : K)^n) ≤ 1)
    (m : ℕ) (hm : 0 < m) : ∀ᶠ n in atTop, (m : D) ∣ movingElement C L π γ H n - 1 := by
  let S := (finite_integer_branches C L primes hinj m).toFinset
  have h (i) : ∀ᶠ n in atTop, (V) i ((movingValue C L n - 1)/(m : K)) ≤ 1 :=
    eventually_div_integer _ _ (hp i) _ (hret i) m hm
  filter_upwards [(eventually_all_finset S).mpr (fun i _ ↦ h i)] with n hn
  apply (subring_dvd_iff_div_mem _ _ _ (Nat.cast_ne_zero.mpr hm.ne')).mpr
  apply (mem_intersection _ _ _).mpr
  constructor
  · have h1 : ((m : K))⁻¹ ∈ horizontal C L := by
      have := ((horizontal C L).restrictScalars ℚ).algebraMap_mem (m : ℚ)⁻¹
      simpa only [map_inv₀,map_natCast,Subalgebra.mem_restrictScalars] using this
    change (movingValue C L n - 1)/(m : K) ∈ horizontal C L
    exact (horizontal C L).mul_mem ((horizontal C L).sub_mem (moving_pole C L n) (horizontal C L).one_mem) h1
  · intro i
    change (V) i ((movingValue C L n - 1)/(m : K)) ≤ 1
    by_cases hd : (branchPrime C L primes i).val ∣ m
    · exact hn i ((finite_integer_branches C L primes hinj m).mem_toFinset.mpr
        ((branchPrime C L primes i).property.mem_primeFactors hd hm.ne'))
    · rw [map_div₀,unit_nat_of_coprime _ _ (hp i) m hd,div_one]
      exact ((mem_intersection _ _ _).mp (movingElement C L π γ H n - 1).property).2 i

end UnconditionalCounterexample.Variations.PrivateGuards.Live
