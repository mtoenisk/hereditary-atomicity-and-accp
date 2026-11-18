import UnconditionalCounterexample.TensorPairLifting

/-!
# Integral lifting through the sole evaluation

At a prime with only its guard, the entire integral value ring is supplied by
constants. Once the single evaluation kernel is in the actual tensor image,
every integral D tensor already belongs to the T image. No coordinate-clearing
integer or fictitious second argument is needed at this prime.
-/

namespace UnconditionalCounterexample.SingleTensorLifting

open Polynomial TensorProduct PoleTensorConductor RadicalConductor LocalAlgebra

/-- Constants lift every integral value through an already-contained kernel. -/
theorem mem_of_integral_value
    {R K A : Type*} [CommRing R] [CommRing K] [CommRing A] [Algebra R K] [Algebra R A]
    (T : Subalgebra R A) (f : A →ₐ[R] K)
    (hker : ∀ z : A, f z = 0 → z ∈ T) (x : A)
    (hx : ∃ c : R, f x = algebraMap R K c) : x ∈ T := by
  obtain ⟨c, hc⟩ := hx
  have he : f (x - algebraMap R A c) = 0 := by rw [map_sub, hc, f.commutes, sub_self]
  have hm := T.add_mem (hker _ he) (T.algebraMap_mem c)
  simpa only [sub_add_cancel] using hm

/-- The kernel of the single literal localized evaluation. -/
theorem single_kernel {K A : Type*} [Field K] [CommRing A] [Algebra K[X] A]
    (M : Submonoid K[X]) [IsLocalization M A] (a : K)
    (f : A →+* K) (h : ∀ g : K[X], f (algebraMap K[X] A g) = g.eval a) :
    RingHom.ker f = Ideal.span {algebraMap K[X] A (X - C a)} := by
  have hpre : (RingHom.ker f).comap (algebraMap K[X] A) = Ideal.span {X - C a} := by
    ext g
    simp only [Ideal.mem_comap, RingHom.mem_ker, h, Ideal.mem_span_singleton]
    exact dvd_iff_isRoot.symm
  rw [← IsLocalization.map_under M A (RingHom.ker f), Ideal.under, hpre,
    Ideal.map_span, Set.image_singleton]

variable (p : ℕ) [Fact p.Prime] (S : Set ℚ[X]) (hS : ∀ f ∈ S, f ≠ 0)
local notation "B" => PoleAlgebra.generated S
local notation "A" => PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] S)

theorem value_polynomial (β : ℚ_[p])
    (hβ : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) β ≠ 0) (g : ℚ_[p][X]) :
    value p S hS β hβ (algebraMap ℚ_[p][X] A g) = g.eval β := by
  change (PoleJets.extendedJet S hS β hβ _).fst = _
  unfold PoleJets.extendedJet
  simp only [PoleJets.jet_polynomial, LocalizedPolynomialJets.firstJet_fst]

/-- At a one-argument prime, integral constants and the exact conductor lift
all of the larger integral image, without any integer multiplier. -/
theorem image_le_of_single_conductor (T D : Subring B) (β : ℚ_[p])
    (hβ : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) β ≠ 0)
    (hvalue : ∀ d : D, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) β ((d : B) : RatFunc ℚ)‖ ≤ 1)
    (hcond : conductorIdeal (image p S hS T) =
      Ideal.span {algebraMap ℚ_[p][X] A (X - C β)}) :
    IntegralTensorImage.image p B D ≤ IntegralTensorImage.image p B T := by
  let e := ScalarExtension.tensorEquiv ℚ ℚ_[p] S hS
  let f := value p S hS β hβ
  let := PoleAlgebra.isLocalization_generated _ (ScalarExtension.extendedSet_nonzero ℚ ℚ_[p] S hS)
  have hker (x : A) (hx : f x = 0) : x ∈ image p S hS T := by
    apply conductorIdeal_subset
    rw [hcond, ← single_kernel (Submonoid.closure (ScalarExtension.extendedSet ℚ ℚ_[p] S)) β
      f.toRingHom (value_polynomial p S hS β hβ)]
    exact hx
  let T' : Subalgebra ℤ_[p] A :=
    { image p S hS T with
      algebraMap_mem' := fun c => TransportedIntegralImage.scalar_mem p _ _ e T c.val c.property }
  intro z hz
  have hDz : e z ∈ image p S hS D := ⟨z, hz, rfl⟩
  have hval : f (e z) ∈ PadicInt.subring p := integral_values p S hS D β hβ hvalue _ hDz
  have hmem := mem_of_integral_value T' (f.restrictScalars ℤ_[p]) hker (e z)
    ⟨⟨f (e z), hval⟩, rfl⟩
  obtain ⟨w, hw, he⟩ := hmem
  exact e.injective he ▸ hw

/-- In particular the same prescribed integer from the paired primes works
at a one-argument prime; here no nt membership is needed. -/
theorem same_integer_in_image (T D : Subring B) (β : ℚ_[p])
    (hβ : ∀ f ∈ S, f.eval₂ (algebraMap ℚ ℚ_[p]) β ≠ 0)
    (hvalue : ∀ d : D, ‖RatFunc.eval (algebraMap ℚ ℚ_[p]) β ((d : B) : RatFunc ℚ)‖ ≤ 1)
    (hcond : conductorIdeal (image p S hS T) =
      Ideal.span {algebraMap ℚ_[p][X] A (X - C β)})
    (n : ℤ) (z : ℚ_[p] ⊗[ℚ] B) (hz : z ∈ IntegralTensorImage.image p B D) :
    (n : ℚ_[p] ⊗[ℚ] B) * z ∈ IntegralTensorImage.image p B T :=
  (IntegralTensorImage.image p B T).mul_mem (intCast_mem _ n)
    (image_le_of_single_conductor p S hS T D β hβ hvalue hcond hz)

end UnconditionalCounterexample.SingleTensorLifting
