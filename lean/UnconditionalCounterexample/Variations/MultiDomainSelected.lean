import UnconditionalCounterexample.Variations.GuardFiniteSupport
import UnconditionalCounterexample.Variations.MultiDomainLowProfiles
import UnconditionalCounterexample.Variations.MultiDomainVertical
import UnconditionalCounterexample.Variations.MultiDomainTargets

/-!
# The domain attached to the chronological multivariate selector

The same selected raws supply the horizontal localization and normalized
units. The frozen sites supply all vertical valuations, tail properties,
and the generic-fibre clearing certificate.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain Filter WithZero NormalizedWords

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {r : ℕ} {q : PrimeIndex}
  (L : LocalPrescription r q) (G : Geometry r K)

def selectedData : MultiDomain.Data (r+1) := (places L G).data (siteRaw L G)
  (fun i ↦ (raw_irreducible (requirements L G) i).ne_zero)

abbrev selectedGenerator := RawWords.normalizedFactor (rawValue (selectedData L G)) normalizationPower

theorem selectedGenerator_ne (i : ℕ) : selectedGenerator L G i ≠ 0 :=
  div_ne_zero (rawValue_ne_zero _ _) (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (rawValue_ne_zero _ j))

def selectedUnit (i : ℕ) : (poleAlgebra (selectedData L G))ˣ := by
  let h := normalized_pole_mem (selectedData L G) normalizationPower i
  let u := selectedGenerator L G i
  exact ⟨⟨u,h.1⟩, ⟨u⁻¹,h.2⟩, Subtype.ext (mul_inv_cancel₀ (selectedGenerator_ne L G i)),
    Subtype.ext (inv_mul_cancel₀ (selectedGenerator_ne L G i))⟩

theorem selected_guard_t (p : PrimeIndex) :
    (selectedData L G).guard p (coordinate 0) = 1 := by
  let g := (permanentFibre L G p).guard
  have ha : g.avoids (map (Int.castRingHom (ZMod p.val)) (X 0 : IntPolys (r+1))) := by
    simp only [ScreenedGuard.avoids, map_X, aeval_X]
    intro hz
    exact g.outside ⟨0, (map_zero _).trans hz.symm⟩
  change g.tuple.valuation (coordinate 0) = 1
  simpa [coordinate, rationalize] using g.unit_of_avoids (X 0) ha

theorem selected_primary_t (j : ℕ) :
    (selectedData L G).primary j (coordinate 0) = exp (-primaryAtomProfile 0 j) := by
  have h := (primaryBirth L G j).order
  change (primaryBirth L G j).tuple.valuation (coordinate 0) = _
  rw [h]
  simp [firstOrder,primaryAtomProfile]

def selectedClearing (hr : ∀ i, ¬ TPoly r ∣ siteRaw L G i) : Clearing (selectedData L G) where
  primes := (places L G).primes
  primary_prime := (places L G).primary_prime _ _
  guard_prime := (places L G).data_guard_prime _ _
  primary_late z hz := (primary_eventually L G z).mono fun j hj ↦
    hj.trans_le (retained_integral (selectedData L G) X_prime hr ⟨z,hz⟩)
  guard_late z hz := by
    by_cases hzero : z = 0
    · simp [hzero]
    have hf := permanent_finite_guard_support L G z hzero
    apply eventually_cofinite.mpr
    exact hf.subset fun p h e ↦ h e.le

/-- The local valuation columns identify the actual generators. The first
coordinate and the stabilization/finite-support promises already follow
from the frozen choice of the sites. -/
def selectedProfileChoices (hr : ∀ i, ¬ TPoly r ∣ siteRaw L G i)
    (V : VerticalProfiles (selectedData L G) normalizationPower) : ProfileChoices (selectedData L G) where
  b n := selectedUnit L G (Generator.b n).stage
  qRatio n := selectedUnit L G (Generator.q n).stage
  b_primary := V.b
  q_primary := V.q
  b_guard n p := V.guard p _
  q_guard n p := V.guard p _
  t_primary j := (selected_primary_t L G j).trans_le (exp_le_exp.mpr (by
    simp [primaryAtomProfile]; split_ifs <;> omega))
  t_exact := selected_primary_t L G
  t_guard := selected_guard_t L G
  E := normalizationPower
  irreducible_raw := raw_irreducible (requirements L G)
  retained_t := hr
  b_eq _ := rfl
  q_eq _ := rfl
  guard_above p := ((places L G).data_guard_prime _ _ p) ▸ (by decide : exp (-1 : ℤ) < 1)
  primary_late z _ := primary_eventually L G z
  guard_finite := permanent_finite_guard_support L G

end UnconditionalCounterexample.MultivariateSelection
