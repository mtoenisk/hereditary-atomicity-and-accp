import HereditaryAtomicity.CharP.ZeroGapAtomic
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Passing a factorization obstruction to a source intersection

To carry an obstruction to atomic factorization into the source intersection, keep the
restriction on products outside the distinguished subset. Splitting elements inside
the subset uses nonunits whose quotients still lie in the intersection.
-/

namespace HereditaryAtomicity.DVRBase

universe u
variable {K : Type u} [Field K]

/-- The literal denominator ideal for membership in an embedded source. -/
def denominatorIdeal (D : Subring K) (z : K) : Ideal D where
  carrier := {a | (a : K) * z ∈ D}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ((a + b : D) : K) * z ∈ D
    simpa only [Subring.coe_add, add_mul] using D.add_mem ha hb
  smul_mem' := by
    intro a b hb
    change ((a : K) * (b : K)) * z ∈ D
    rw [mul_assoc]
    exact D.mul_mem a.property hb

/-- A domain inside its fraction field is exactly the intersection of its
actual maximal localizations. This is the source-membership test in the semilocal intersection argument. -/
theorem mem_iff_mem_maximal_localizations
    (D : Subring K) [IsFractionRing D K] (z : K) :
    z ∈ D ↔ ∀ M : MaximalSpectrum D,
      z ∈ (Localization.subalgebra.ofField K M.asIdeal.primeCompl
        M.asIdeal.primeCompl_le_nonZeroDivisors).toSubring := by
  constructor
  · intro hz M
    exact (Localization.subalgebra.ofField K M.asIdeal.primeCompl
      M.asIdeal.primeCompl_le_nonZeroDivisors).algebraMap_mem (⟨z, hz⟩ : D)
  · intro h
    let I := denominatorIdeal D z
    have hI : I = ⊤ := by
      by_contra hproper
      obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hproper
      let M : MaximalSpectrum D := ⟨P, hP⟩
      have hz := h M
      change ∃ (a s : D) (_ : s ∈ P.primeCompl),
        z = (a : K) * (s : K)⁻¹ at hz
      obtain ⟨a, s, hs, heq⟩ := hz
      have hs0 : (s : K) ≠ 0 := by
        intro hzero
        have : s = 0 := Subtype.ext hzero
        exact hs (this ▸ P.zero_mem)
      have hsI : s ∈ I := by
        change (s : K) * z ∈ D
        rw [heq, mul_left_comm, mul_inv_cancel₀ hs0, mul_one]
        exact a.property
      exact hs (hIP hsI)
    have hmem : (1 : D) ∈ I := by rw [hI]; trivial
    change ((1 : D) : K) * z ∈ D at hmem
    simpa only [Subring.coe_one, one_mul] using hmem

/-- An outside-set product obstruction in `S` contradicts atomicity of `S ∩ D`
once every element of the distinguished set splits into two intrinsic nonunits
of that intersection. The unit in an associated atomic factorization is kept. -/
theorem not_isAtomicDomain_intersection
    (S D : Subring K) (J : Set K) {z : K}
    (hz : z ≠ 0) (hzS : z ∈ S) (hzD : z ∈ D)
    (hunit : ∀ a : ↥(S ⊓ D), (a : K) ∈ J → ¬ IsUnit a)
    (hsplit : ∀ a : ↥(S ⊓ D), (a : K) ∈ J →
      ∃ b c : ↥(S ⊓ D), ¬ IsUnit b ∧ ¬ IsUnit c ∧ a = b * c)
    (hno : ∀ (ι : Type u) [Fintype ι] (f : ι → S),
      (∏ i, f i) = (⟨z, hzS⟩ : S) → (∀ i, (f i : K) ∉ J) → False) :
    ¬ Factorization.IsAtomicDomain ↥(S ⊓ D) := by
  let T : Subring K := S ⊓ D
  let f : T →+* S := Subring.inclusion inf_le_left
  have hatom : ∀ a : T, (a : K) ∈ J → ¬ Irreducible a := by
    intro a ha hirr
    obtain ⟨b, c, hb, hc, heq⟩ := hsplit a ha
    exact (hirr.isUnit_or_isUnit heq).elim hb hc
  apply CharP.not_isAtomicDomain_of_no_factorization_avoiding_atomless_set
    {a : T | (a : K) ∈ J} hunit hatom (z := (⟨z, hzS, hzD⟩ : T))
    (fun h => hz (congrArg (fun a : T => (a : K)) h))
  intro ι _ a ha hav
  apply hno ι (fun i => f (a i))
  · rw [← map_prod, ha]
    rfl
  · exact hav

/-- If a source is the intersection of a family of overrings, a quotient
returns to the source once it belongs to one chosen overring and its
denominator is a unit at every other overring. No finiteness is needed here. -/
theorem div_mem_of_mem_at_chosen_and_units_elsewhere
    {ι : Type*} (D : Subring K) (R : ι → Subring K)
    (hD : ∀ x : K, x ∈ D ↔ ∀ i, x ∈ R i) (i₀ : ι)
    {g y : K} (hg : g ∈ D) (hy : y ∈ D)
    (hchosen : g / y ∈ R i₀)
    (hunits : ∀ i, i ≠ i₀ → IsUnit (⟨y, (hD y).mp hy i⟩ : R i)) :
    g / y ∈ D := by
  classical
  apply (hD _).mpr
  intro i
  by_cases hi : i = i₀
  · simpa [hi] using hchosen
  · have hinv : y⁻¹ ∈ R i := Submonoid.inv_mem_of_isUnit (hunits i hi)
    simpa only [div_eq_mul_inv] using (R i).mul_mem ((hD g).mp hg i) hinv

end HereditaryAtomicity.DVRBase
