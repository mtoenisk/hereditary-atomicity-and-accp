import UnconditionalCounterexample.Variations.MultiDomainLowExtraction
import UnconditionalCounterexample.Variations.MultivariateSelectionWords

/-!
# Generic recovery for both multivariate domains

An injective source subring with unbounded factorization lengths contributes
a cofinal family of actual listed words. On the selected sequence their
rational algebra therefore equals the pole localization.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain.ProfileChoices

open MultivariateSelection

variable {r : ℕ} {A : Data (r+1)} {M : ℕ → Type*} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The image of an ordinary element in its horizontal localization. -/
def inPole (x : ordinary A) : poleAlgebra A := ⟨x, ((mem_ordinary A).mp x.property).1⟩

theorem generic_recovery (C : ProfileChoices A) (R : Requirements r M K)
    (hp : Function.Surjective R.point) (hP : Function.Surjective R.primesEnumeration)
    (hraw : A.raw = raw (withTriangularWords R)) (he : C.E = normalizationPower)
    {T : Type*} [CommRing T] [IsDomain T] (f : T →+* ordinary A) (hf : Function.Injective f)
    (hT : ¬ Factorization.IsBFDomain T) (S : Subalgebra ℚ (poleAlgebra A))
    (hS : ∀ y : T, inPole (f y) ∈ S) : S = ⊤ := by
  let : IsLocalization (Submonoid.closure (Set.range (raw (withTriangularWords R)))) (poleAlgebra A) := by
    rw [← hraw]
    infer_instance
  apply recover_of_normalized_words R hp hP (poleAlgebra A) (FunctionField (r+1))
    (poleAlgebra A).subtype Subtype.val_injective S
  obtain ⟨k, _, h⟩ := C.infinitely_many_bounded_words f hf hT
  apply h.mono
  rintro n ⟨w, _, _, y, hy⟩
  refine ⟨w, ⟨inPole (f y), hS y⟩, ?_⟩
  rw [← hraw, normalizedWord, ← he]
  exact hy

end UnconditionalCounterexample.Variations.MultiDomain.ProfileChoices
