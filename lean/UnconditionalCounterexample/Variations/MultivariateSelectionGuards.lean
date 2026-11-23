import UnconditionalCounterexample.Variations.MultivariateSelectionSites

/-!
# Guard units for the actual earlier rational polynomials

An unramified integral lift of a nonvanishing residue evaluation has valuation
one. This applies to any integral polynomial model of a rational raw, including
those whose coefficients have denominators at earlier processed primes.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations GuardUnramified MultiDomain

variable {r : ℕ} {p : PrimeIndex}

private theorem factors_reduction {E : Type*} [Field E] [CharP E p.val] [Algebra (ZMod p.val) E]
    (φ : ℤ_[p.val] →+* E) : φ = (algebraMap (ZMod p.val) E).comp PadicInt.toZMod := by
  ext x
  obtain ⟨a,ha⟩ := ZMod.intCast_surjective (PadicInt.toZMod x)
  have hx : x - a ∈ (Ideal.span {(p.val : ℤ_[p.val])} : Ideal ℤ_[p.val]) := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker,map_sub,map_intCast,ha,sub_self]
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hx
  have hfull := congrArg φ hb
  rw [map_sub,map_intCast,map_mul,map_natCast,CharP.cast_eq_zero,zero_mul,sub_eq_zero] at hfull
  simpa only [RingHom.comp_apply,← ha,map_intCast] using hfull

private theorem unit_integral_eval {G : ScreenedGuard r p} (Q : MvPolynomial (Fin (r+1)) ℤ_[p.val])
    (h : G.avoids (MvPolynomial.map PadicInt.toZMod Q)) :
    IsUnit (eval₂Hom (algebraMap ℤ_[p.val] (WittVector p.val (GaloisField p.val G.degree))) G.w Q) := by
  let E := GaloisField p.val G.degree
  let O := WittVector p.val E
  let φ : O →+* E := WittVector.constantCoeff
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  change φ (eval₂Hom (algebraMap ℤ_[p.val] O) G.w Q) ≠ 0
  rw [map_eval₂Hom, factors_reduction (φ.comp (algebraMap ℤ_[p.val] O))]
  change eval₂Hom (algebraMap (ZMod p.val) E) _ (MvPolynomial.map PadicInt.toZMod Q) ≠ 0 at h
  rwa [eval₂Hom_map_hom] at h

private theorem unit_value {k : Type*} [Field k] [CharP k p.val] [Algebra (ZMod p.val) k] [Finite k]
    (a : WittVector p.val k) (ha : IsUnit a) :
    valuation p.val k (algebraMap _ (LocalField p.val k) a) = 1 := by
  obtain ⟨u,rfl⟩ := ha
  let v := valuation p.val k
  let f := algebraMap (WittVector p.val k) (LocalField p.val k)
  have h₁ : v (f (u : WittVector p.val k)) ≤ 1 := (integral_iff _ _ _).mpr ⟨_,rfl⟩
  have h₂ : v (f (↑u⁻¹ : WittVector p.val k)) ≤ 1 := (integral_iff _ _ _).mpr ⟨_,rfl⟩
  apply h₁.antisymm
  calc
    1 = v (f (u : WittVector p.val k)) * v (f (↑u⁻¹ : WittVector p.val k)) := by
      rw [← map_mul,← map_mul,Units.mul_inv,map_one,map_one]
    _ ≤ _ := (mul_le_mul' le_rfl h₂).trans_eq (mul_one _)

theorem ScreenedGuard.unit_of_model (G : ScreenedGuard r p) (f : Poly r)
    (Q : MvPolynomial (Fin (r+1)) ℤ_[p.val])
    (hmodel : MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) f)
    (havoid : G.avoids (reduction p f)) :
    G.tuple.valuation (algebraMap _ (FunctionField (r+1)) f) = 1 := by
  let E := GaloisField p.val G.degree
  let O := WittVector p.val E
  let L := LocalField p.val E
  rw [reduction_of_model hmodel] at havoid
  have hu := unit_value (p := p) _ (unit_integral_eval Q havoid)
  change valuation p.val E (IndependentTuples.evaluation G.tuple.x G.tuple.independent _) = 1
  have he : IndependentTuples.evaluation G.tuple.x G.tuple.independent (algebraMap _ _ f) = aeval G.tuple.x f :=
    IsFractionRing.lift_algebraMap (K := FunctionField (r+1)) (g := (aeval G.tuple.x : Poly r →ₐ[ℚ] L).toRingHom) _ _
  rw [he]
  have hφ := congrArg (eval₂Hom (algebraMap ℚ_[p.val] L) G.tuple.x) hmodel
  rw [eval₂Hom_map_hom,eval₂Hom_map_hom,← IsScalarTower.algebraMap_eq ℚ ℚ_[p.val] L] at hφ
  have hrel : algebraMap O L (eval₂Hom (algebraMap ℤ_[p.val] O) G.w Q) = aeval G.tuple.x f := by
    rw [map_eval₂Hom, ← IsScalarTower.algebraMap_eq ℤ_[p.val] O L,IsScalarTower.algebraMap_eq ℤ_[p.val] ℚ_[p.val] L]
    exact hφ
  rw [← hrel]
  exact hu

/-- Changing the presentation of the residue ring from `p^1` to `p`
commutes with reducing integral polynomial coefficients. -/
def modOne (p : PrimeIndex) : ZMod (p.val^1) →+* ZMod p.val :=
  ZMod.castHom (by rw [pow_one]) _

theorem modOne_comp (p : PrimeIndex) : (modOne p).comp (PadicInt.toZModPow 1) = PadicInt.toZMod := by
  exact (factors_reduction ((modOne p).comp (PadicInt.toZModPow 1))).trans (by ext x; simp)

end UnconditionalCounterexample.MultivariateSelection
