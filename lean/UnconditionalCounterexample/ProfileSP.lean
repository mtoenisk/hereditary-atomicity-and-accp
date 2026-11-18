import UnconditionalCounterexample.IntegralIdealProfiles
import UnconditionalCounterexample.PicardProfiles
import UnconditionalCounterexample.ProfileBounds
import UnconditionalCounterexample.PaperTargets

/-!
# SP factorization from actual restricted ideal profiles

This packages the arbitrary-ideal argument independently of the choice of
primary primes. Every maximal ideal needs an actual normalized profile label;
a bijection of labels and maximal ideals is not required by this consumer.
Realization of restricted fractional profiles then supplies the positive
threshold ideals and the literal list-valued SP-domain target.
-/

noncomputable section
namespace UnconditionalCounterexample.ProfileSP
open WithZero PicardProfiles FractionalIdealProfiles RadicalIdealProducts
open scoped nonZeroDivisors BigOperators
variable {R K O : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-- Positive order-level indicators preserve exactly the restricted-profile
conditions, including eventual primary constancy. -/
theorem threshold_restricted (P : ValuationProfiles R O)
    (x : R) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k) :
    Restricted (fun l => if k ≤ P.value l x then (1 : ℤ) else 0) := by
  obtain ⟨N, hN⟩ := P.eventually_primary x hx
  refine ⟨⟨N, fun j hj => ?_⟩, ?_⟩
  · simp only [hN j hj]
  · apply (P.finite_outside x hx).subset
    intro i hi hz
    apply hi
    simp [hz, Nat.not_le_of_gt hk]

/-- The finite tuple representing one positive order-level indicator. -/
def threshold (P : ValuationProfiles R O) (x : R) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k) :
    Profile O :=
  ofCoordinates _ (threshold_restricted P x hx k hk)

@[simp] theorem threshold_coordinate (P : ValuationProfiles R O)
    (x : R) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k) (l : ProfilePlace O) :
    coordinate (threshold P x hx k hk) l = if k ≤ P.value l x then 1 else 0 := by
  simp only [threshold, coordinate_ofCoordinates]

/-- Realization of all restricted profiles gives the exact ordinary threshold
ideal at every maximal localization. -/
theorem exists_threshold_ideal (P : ValuationProfiles R O)
    (v : ProfilePlace O → Valuation K ℤᵐ⁰)
    (hfull : ∀ x : K, x ∈ (1 : FractionalIdeal R⁰ K) ↔ ∀ l, v l x ≤ 1)
    (label : Maximal R → ProfilePlace O)
    (hvalue : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      v (label M) (algebraMap R K x) = exp (-(P.value (label M) x : ℤ)))
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ P.value (label M) x)
    (hrealize : ∀ f : Profile O, ∃ I : FractionalIdeal R⁰ K, HasProfile v I (coordinate f))
    (x : R) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k) :
    ∃ J : Ideal R, ∀ M : Maximal R,
      localIdeal M J = if k ≤ P.value (label M) x then localMaximal M else ⊤ := by
  obtain ⟨I, hI⟩ := hrealize (threshold P x hx k hk)
  have hnonneg : ∀ l, 0 ≤ coordinate (threshold P x hx k hk) l := by
    intro l
    rw [threshold_coordinate]
    split_ifs <;> norm_num
  obtain ⟨J, hJ⟩ := IntegralIdealProfiles.exists_integral_ideal v hfull I _ hI hnonneg
  refine ⟨J, fun M => ?_⟩
  have hv := hI (label M)
  rw [← hJ, threshold_coordinate] at hv
  let n : ℕ := if k ≤ P.value (label M) x then 1 else 0
  have hvn : HasValue (J : FractionalIdeal R⁰ K) (v (label M)) (n : ℤ) := by
    by_cases h : k ≤ P.value (label M) x <;> simpa [n, h] using hv
  have h := IntegralIdealProfiles.localIdeal_eq_pow_of_hasValue
    (fun M => v (label M)) (fun M => P.value (label M)) hvalue hprincipal J M n hvn
  simpa [n, Ideal.one_eq_top] using h

/-- Every ordinary ideal is a finite product of actual radical ideals; no
finite-generation hypothesis on the ideal is made. -/
theorem exists_radical_ideal_list (P : ValuationProfiles R O)
    (v : ProfilePlace O → Valuation K ℤᵐ⁰)
    (hfull : ∀ x : K, x ∈ (1 : FractionalIdeal R⁰ K) ↔ ∀ l, v l x ≤ 1)
    (label : Maximal R → ProfilePlace O)
    (hvalue : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      v (label M) (algebraMap R K x) = exp (-(P.value (label M) x : ℤ)))
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ P.value (label M) x)
    (hrealize : ∀ f : Profile O, ∃ I : FractionalIdeal R⁰ K, HasProfile v I (coordinate f))
    (I : Ideal R) :
    ∃ L : List (Ideal R), (∀ J ∈ L, J.IsRadical) ∧ L.prod = I := by
  have hbounded (x : R) (hx : x ≠ 0) : ∃ N : ℕ, ∀ M, P.value (label M) x ≤ N := by
    obtain ⟨N, hN⟩ := P.exists_all_coordinate_bound x hx
    exact ⟨N, fun M => hN (label M)⟩
  obtain ⟨N, J, hJ, hI⟩ := every_ideal_radical_product (fun M => P.value (label M))
    hprincipal hbounded (exists_threshold_ideal P v hfull label hvalue hprincipal hrealize) I
  refine ⟨(List.range N).map J, ?_, ?_⟩
  · intro L hL
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hL
    exact hJ k
  · rw [← List.prod_toFinset J (List.nodup_range (n := N))]
    simpa only [List.toFinset_range] using hI.symm

/-- The literal SP-domain target follows from the actual normalized maximal
orders and actual realization of restricted ideal profiles. -/
theorem isSPDomain (P : ValuationProfiles R O)
    (v : ProfilePlace O → Valuation K ℤᵐ⁰)
    (hfull : ∀ x : K, x ∈ (1 : FractionalIdeal R⁰ K) ↔ ∀ l, v l x ≤ 1)
    (label : Maximal R → ProfilePlace O)
    (hvalue : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      v (label M) (algebraMap R K x) = exp (-(P.value (label M) x : ℤ)))
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ P.value (label M) x)
    (hrealize : ∀ f : Profile O, ∃ I : FractionalIdeal R⁰ K, HasProfile v I (coordinate f)) :
    PaperTargets.IsSPDomain R := by
  intro I _ _
  exact exists_radical_ideal_list P v hfull label hvalue hprincipal hrealize I

end UnconditionalCounterexample.ProfileSP
