import UnconditionalCounterexample.Variations.MultiDomainLowRecovery
import UnconditionalCounterexample.LocalAlgebra.TorsionDescent
import UnconditionalCounterexample.LocalAlgebra.TransportedIntegralImage

/-!
# From the local tensor conductor to the multivariate integer conductor

At the primes dividing one coordinate denominator, take the product of the
local conductor powers. At every other prime the full integral tensor
inclusion suffices. Faithfully detecting the quotient through all p-adic
tensors gives the resulting integer conductor in the original subring.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open GuardSupport LocalAlgebra
open scoped TensorProduct

section Global
variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-- A single prime-power conductor transported back along the rational
scalar-extension equivalence. -/
theorem tensor_power_of_transport (p : ℕ) [Fact p.Prime] (S D : Subring B) {L : Type*}
    [CommRing L] [Algebra ℚ_[p] L] (e : ℚ_[p] ⊗[ℚ] B ≃ₐ[ℚ_[p]] L) (k : ℕ)
    (h : ∀ z ∈ TransportedIntegralImage.image p B L e D,
      (p : L)^k * z ∈ TransportedIntegralImage.image p B L e S) :
    ∀ z ∈ IntegralTensorImage.image p B D,
      (p : ℚ_[p] ⊗[ℚ] B)^k * z ∈ IntegralTensorImage.image p B S := by
  intro z hz
  obtain ⟨w,hw,he⟩ := h (e z) ⟨z,hz,rfl⟩
  have hwe : w = (p : ℚ_[p] ⊗[ℚ] B)^k * z := e.injective (by simpa using he)
  exact hwe ▸ hw

theorem integer_conductor_of_local_powers (S D : Subring B) (hhull : RationalHull.hull S = ⊤)
    (bad : Finset PrimeIndex)
    (hbad : ∀ p ∈ bad, ∃ k : ℕ, ∀ z ∈ IntegralTensorImage.image p.val B D,
      (p.val : ℚ_[p.val] ⊗[ℚ] B)^k * z ∈ IntegralTensorImage.image p.val B S)
    (hgood : ∀ p ∉ bad, IntegralTensorImage.image p.val B D ≤ IntegralTensorImage.image p.val B S) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ D, (m : B)*z ∈ S := by
  classical
  let power (p : PrimeIndex) := if hp : p ∈ bad then (hbad p hp).choose else 0
  let m := ∏ p ∈ bad, p.val ^ power p
  have hm : 0 < m := Finset.prod_pos fun p _ ↦ pow_pos p.property.pos _
  refine ⟨m,hm,?_⟩
  have hall := TorsionDescent.integer_conductor_of_all_images S D hhull (m : ℤ)
  apply (show (∀ z ∈ D, ((m : ℤ) : B)*z ∈ S) → _ from fun H ↦ by simpa using H)
  apply hall
  intro q hq z hz
  let p : PrimeIndex := ⟨q,hq.out⟩
  let U := IntegralTensorImage.image q B S
  by_cases hp : p ∈ bad
  · have hb := (hbad p hp).choose_spec z hz
    have hdiv : p.val ^ power p ∣ m := Finset.dvd_prod_of_mem (fun v : PrimeIndex ↦ v.val ^ power v) hp
    obtain ⟨a,ha⟩ := hdiv
    have hz' : (q : ℚ_[q] ⊗[ℚ] B) ^ power p * z ∈ U := by simpa [power,hp] using hb
    have ha' : ((m : ℤ) : ℚ_[q] ⊗[ℚ] B)*z = a*((q : ℚ_[q] ⊗[ℚ] B)^power p * z) := by
      rw [ha]
      push_cast
      change ((q : ℚ_[q] ⊗[ℚ] B)^power p * a) * z = _
      ring
    exact ha' ▸ U.mul_mem (natCast_mem U a) hz'
  · exact U.mul_mem (intCast_mem U _) (hgood p hp hz)

end Global

open MultivariateSelection
variable {r : ℕ} {A : Data (r+1)}

def intoPole : ordinary A →+* poleAlgebra A := IntersectionDomain.inclusion _ _

/-- For an arbitrary domain embedded in the ordinary ring, including the
point pullback, the topology of the local schedule now enters only through
the actual tensor inclusions at each prime. The finite exceptional set is
obtained by clearing the first coordinate in the subring under consideration. -/
theorem ProfileChoices.integer_conductor {M : ℕ → Type*} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (C : ProfileChoices A) (R : Requirements r M K)
    (hp : Function.Surjective R.point) (hP : Function.Surjective R.primesEnumeration)
    (hraw : A.raw = raw (withTriangularWords R)) (he : C.E = normalizationPower)
    {D : Type*} [CommRing D] [IsDomain D] (i : D →+* ordinary A) (hi : Function.Injective i)
    (T : Subring D) (hT : ¬Factorization.IsBFDomain T)
    (localPowers : ∀ n : ℕ, 0 < n →
      let f := intoPole.comp i
      (n : poleAlgebra A) * algebraMap (Polys (r+1)) (poleAlgebra A) (TPoly r) ∈ T.map f →
      (∀ p : PrimeIndex, p.val ∣ n → ∃ k : ℕ, ∀ z ∈ IntegralTensorImage.image p.val (poleAlgebra A) f.range,
        (p.val : ℚ_[p.val] ⊗[ℚ] poleAlgebra A)^k * z ∈ IntegralTensorImage.image p.val (poleAlgebra A) (T.map f)) ∧
      (∀ p : PrimeIndex, ¬ p.val ∣ n → IntegralTensorImage.image p.val (poleAlgebra A) f.range ≤
        IntegralTensorImage.image p.val (poleAlgebra A) (T.map f))) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : D, (m : D)*z ∈ T := by
  classical
  let f := intoPole.comp i
  let S := T.map f
  have hf : Function.Injective f := (fun _ _ h ↦ hi (Subtype.ext (congrArg (poleAlgebra A).subtype h)))
  have hh : RationalHull.hull S = ⊤ := C.generic_recovery R hp hP hraw he (i.comp T.subtype)
    (hi.comp Subtype.val_injective) hT _ (fun y ↦ Algebra.subset_adjoin (show f (y : D) ∈ S from ⟨y,y.property,rfl⟩))
  obtain ⟨n,hn,hnt⟩ := RationalHull.exists_nat_mul_mem_of_hull_eq_top S hh
    (algebraMap (Polys (r+1)) (poleAlgebra A) (TPoly r))
  obtain ⟨hb,hg⟩ := localPowers n hn hnt
  let bad := n.primeFactors.attach.image (fun j ↦ (⟨j.val, Nat.prime_of_mem_primeFactors j.property⟩ : PrimeIndex))
  have hbad (p : PrimeIndex) : p ∈ bad ↔ p.val ∣ n := by
    constructor
    · intro h
      obtain ⟨j, _, h⟩ := Finset.mem_image.mp h
      exact (congrArg Subtype.val h) ▸ Nat.dvd_of_mem_primeFactors j.property
    · intro h
      exact Finset.mem_image.mpr ⟨⟨p.val, Nat.mem_primeFactors.mpr ⟨p.property,h,hn.ne'⟩⟩,Finset.mem_attach _ _,rfl⟩
  obtain ⟨m,hm,h⟩ := integer_conductor_of_local_powers S f.range hh bad
    (fun p hp ↦ hb p ((hbad p).mp hp)) (fun p hp ↦ hg p (mt (hbad p).mpr hp))
  refine ⟨m,hm,fun z ↦ ?_⟩
  obtain ⟨w,hw,heq⟩ := h (f z) ⟨z,rfl⟩
  exact (hf (heq.trans (by simp)) : w = (m : D)*z) ▸ hw

end UnconditionalCounterexample.Variations.MultiDomain
