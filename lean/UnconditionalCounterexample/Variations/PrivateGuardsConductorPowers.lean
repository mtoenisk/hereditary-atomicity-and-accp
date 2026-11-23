import UnconditionalCounterexample.Variations.PrivateGuardsConductorWords
import UnconditionalCounterexample.Variations.TripleGuardGoodPrimes
import UnconditionalCounterexample.Variations.MultiDomainConductor

/-! # Integral tensor powers and the integer conductor for punctured tables -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection MultiDomain LocalAlgebra
  MultivariateRecovery RadicalConductor TransportedIntegralImage
open scoped TensorProduct

section Local
variable {r : ℕ} {p : PrimeIndex} {τ : Type*} [Finite τ] (G : ScreenedGuard r p)
  {B A : Type*} [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ_[p.val] A]
  [Algebra ℤ_[p.val] A] [IsScalarTower ℤ_[p.val] ℚ_[p.val] A]
  (e : ℚ_[p.val] ⊗[ℚ] B ≃ₐ[ℚ_[p.val]] A) (T D : Subring B)
  (v : ∀ i : Option τ, A →ₐ[ℚ_[p.val]] G.Field i)

/-- Either type of fibre gives a power conductor at a prime dividing the
clearing denominator and the full image at every other prime. -/
theorem tensor_power_at_fibre (n : ℕ) (hs : Function.Surjective (AlgHom.pi v))
    (hclear : ∀ b : B, ∃ a : ℕ, 0 < a ∧ (a : B)*b ∈ T)
    (hint : ∀ i (x : D), ‖v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (x : B)))‖ ≤ 1)
    (hk : (⨅ i, RingHom.ker (v i).toRingHom) ≤ conductorIdeal (image p.val B A e T))
    (hgood : ¬p.val ∣ n → image p.val B A e D ≤ image p.val B A e T) :
    ∃ k : ℕ, (¬p.val ∣ n → k = 0) ∧ ∀ z ∈ IntegralTensorImage.image p.val B D,
      (p.val : ℚ_[p.val] ⊗[ℚ] B)^k*z ∈ IntegralTensorImage.image p.val B T := by
  by_cases hp : p.val ∣ n
  · obtain ⟨k,h⟩ := G.exceptional_tensor_power e T D v hs hclear hint hk
    exact ⟨k,fun h' ↦ (h' hp).elim,tensor_power_of_transport p.val T D e k h⟩
  · exact ⟨0,fun _ ↦ rfl,tensor_power_of_transport p.val T D e 0
      (fun z hz ↦ by simpa using hgood hp hz)⟩

end Local

variable {r d : ℕ} (K : Type) [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
  (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)

local notation "R" => tableRule (genericTablePolicy r K) q c
local notation "B" => actualPole C R

theorem integer_conductor_from_powers (S D : Subring B) (hw : HasMixedWords C R S)
    (hloc : ∀ n : ℕ, 0 < n → (n : B)*algebraMap (Poly r) B (X 0) ∈ S →
      ∀ p : PrimeIndex, ∃ k : ℕ, (¬p.val ∣ n → k = 0) ∧ ∀ z ∈ IntegralTensorImage.image p.val B D,
        (p.val : ℚ_[p.val] ⊗[ℚ] B)^k*z ∈ IntegralTensorImage.image p.val B S) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ D, (m : B)*z ∈ S := by
  classical
  have hh := mixed_hull_eq_top C K q c S hw
  obtain ⟨n,hn,hX⟩ := RationalHull.exists_nat_mul_mem_of_hull_eq_top S hh (algebraMap (Poly r) B (X 0))
  let bad := n.primeFactors.attach.image (fun v ↦ (⟨v.val,Nat.prime_of_mem_primeFactors v.property⟩ : PrimeIndex))
  have hbad (p : PrimeIndex) : p ∈ bad ↔ p.val ∣ n := by
    constructor
    · intro h
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
      exact (congrArg Subtype.val hj) ▸ Nat.dvd_of_mem_primeFactors j.property
    · intro h
      exact Finset.mem_image.mpr ⟨⟨p.val,Nat.mem_primeFactors.mpr ⟨p.property,h,hn.ne'⟩⟩,Finset.mem_attach _ _,rfl⟩
  apply integer_conductor_of_local_powers S D hh bad
  · intro p _
    obtain ⟨k,_,h⟩ := hloc n hn hX p
    exact ⟨k,h⟩
  · intro p hp z hz
    obtain ⟨k,hk,h⟩ := hloc n hn hX p
    simpa only [hk (mt (hbad p).mpr hp),pow_zero,one_mul] using h z hz

end UnconditionalCounterexample.Variations.PrivateGuards.Live
