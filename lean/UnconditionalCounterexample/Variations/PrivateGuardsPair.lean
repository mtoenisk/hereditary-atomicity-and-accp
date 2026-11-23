import UnconditionalCounterexample.Variations.PrivateGuardsSeed
import UnconditionalCounterexample.Variations.PrivateGuards

/-! # A paired ordinary and private valuation on the rational function field -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial GuardSupport DiscreteOrders WithZero

variable {r : ℕ}

private theorem model {p : PrimeIndex} {f : MvPolynomial (Fin r) ℚ}
    (h : ∀ q ∈ f.coeffs, ‖(q : ℚ_[p.val])‖ ≤ 1) :
    ∃ F : MvPolynomial (Fin r) ℤ_[p.val],
      map (algebraMap ℤ_[p.val] ℚ_[p.val]) F = map (algebraMap ℚ ℚ_[p.val]) f := by
  apply mem_range_map_iff_coeffs_subset.mpr
  intro z hz
  obtain ⟨q, hq, rfl⟩ := coe_coeffs_map (algebraMap ℚ ℚ_[p.val]) f hz
  exact ⟨⟨_, h _ hq⟩, rfl⟩

private theorem eval_model {p : PrimeIndex} {f : MvPolynomial (Fin r) ℚ}
    {F : MvPolynomial (Fin r) ℤ_[p.val]}
    (he : map (algebraMap ℤ_[p.val] ℚ_[p.val]) F = map (algebraMap ℚ ℚ_[p.val]) f)
    (a : Fin r → ℤ_[p.val]) : (eval a F).val = value p a f := by
  rw [value, aeval_eq_eval₂Hom]
  change algebraMap ℤ_[p.val] ℚ_[p.val] (eval a F) = f.eval₂ _ _
  rw [map_eval, he, eval₂_eq_eval_map]
  rfl

/-- Final independent private and ordinary tuples at one rational prime. -/
structure Pair (p : PrimeIndex) (G : MvPolynomial (Fin (r+1)) ℚ)
    (tests : Finset (MvPolynomial (Fin (r+1)) ℚ)) where
  privately : Fin (r+1) → ℤ_[p.val]
  ordinarily : Fin (r+1) → ℤ_[p.val]
  private_independent : AlgebraicIndependent ℚ (fun i => (privately i).val)
  ordinary_independent : AlgebraicIndependent ℚ (fun i => (ordinarily i).val)
  distinct : PadicInt.toZMod (privately 0) ≠ PadicInt.toZMod (ordinarily 0)
  private_norm : ‖value p privately G‖ = ‖(p.val : ℚ_[p.val])‖
  ordinary_norm : ‖value p ordinarily G‖ = 1
  private_tests : ∀ f ∈ tests, ‖value p privately f‖ = 1
  ordinary_tests : ∀ f ∈ tests, ‖value p ordinarily f‖ = 1

/-- Both tuples give embeddings of the whole rational function field. The
ordinary and private evaluations preserve distinct first-coordinate residues. -/
theorem SmoothSeed.realize {p : PrimeIndex} {G : MvPolynomial (Fin (r+1)) ℚ}
    {tests : Finset (MvPolynomial (Fin (r+1)) ℚ)} (s : SmoothSeed p G tests) :
    Nonempty (Pair p G tests) := by
  classical
  obtain ⟨F, hF⟩ := model (s.integral_coeffs G (Or.inl rfl))
  have hroot : eval s.privatePoint F = 0 := by
    apply Subtype.ext
    exact (eval_model hF _).trans s.root
  have hder : IsUnit (eval s.privatePoint (pderiv s.direction F)) := by
    have he := congrArg (pderiv s.direction) hF
    simp only [pderiv_map] at he
    exact PadicInt.isUnit_iff.mpr ((congrArg norm (eval_model he _)).trans s.partial_norm)
  obtain ⟨a,hai,har,haG,hat⟩ := exists_private_lift p.val F s.privatePoint s.direction hroot hder
  obtain ⟨b,hbi,hbr⟩ := IndependentTuples.exists_padic_lifts p.val (r+1)
    s.ordinaryPoint (fun _ => 1) (fun _ => zero_lt_one)
  have hu (c d : Fin (r+1) → ℤ_[p.val]) (hr : ∀ j, PadicInt.toZMod (c j) = PadicInt.toZMod (d j))
      (f : MvPolynomial (Fin (r+1)) ℚ) (hf : f = G ∨ f ∈ tests)
      (hd : ‖value p d f‖ = 1) : ‖value p c f‖ = 1 := by
    obtain ⟨H,hH⟩ := model (s.integral_coeffs f hf)
    have hdu : IsUnit (eval d H) := PadicInt.isUnit_iff.mpr ((congrArg norm (eval_model hH _)).trans hd)
    have hcu : IsUnit (eval c H) := (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
      ((residue_eval_congr H hr).symm ▸ (padicInt_isUnit_iff_toZMod_ne_zero _).mp hdu)
    exact (congrArg norm (eval_model hH _)).symm.trans (PadicInt.isUnit_iff.mp hcu)
  refine ⟨⟨a,b,hai,hbi,?_,?_,hu b _ (fun j => (hbr j).1) G (Or.inl rfl) s.ordinary_norm,
    fun f hf => hu a _ har f (Or.inr hf) (s.private_tests _ hf),
    fun f hf => hu b _ (fun j => (hbr j).1) f (Or.inr hf) (s.ordinary_tests _ hf)⟩⟩
  · rw [har, (hbr 0).1]
    exact s.distinct
  · exact (congrArg norm (eval_model hF a)).symm.trans haG

/-- The actual discrete place obtained from evaluation of a rational function
at an algebraically independent integral tuple. -/
def place (p : PrimeIndex) (a : Fin r → ℤ_[p.val])
    (ha : AlgebraicIndependent ℚ (fun i => (a i).val)) :
    Valuation (FractionRing (MvPolynomial (Fin r) ℚ)) ℤᵐ⁰ :=
  EvaluationDVR.valuation p.val (IndependentTuples.evaluation _ ha)

theorem place_polynomial (p : PrimeIndex) (a : Fin r → ℤ_[p.val])
    (ha : AlgebraicIndependent ℚ (fun i => (a i).val)) (f : MvPolynomial (Fin r) ℚ) :
    place p a ha (algebraMap (MvPolynomial (Fin r) ℚ) _ f) = Padic.mulValuation (value p a f) := by
  change Padic.mulValuation (IndependentTuples.evaluation _ ha (algebraMap _ _ f)) = _
  congr 1
  exact IsFractionRing.lift_algebraMap (K := FractionRing (MvPolynomial (Fin r) ℚ))
    (g := (MvPolynomial.aeval (fun i => (a i).val) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] ℚ_[p.val]).toRingHom)
    ha f

theorem Pair.detects_self {p : PrimeIndex} {G : MvPolynomial (Fin (r+1)) ℚ}
    {tests : Finset (MvPolynomial (Fin (r+1)) ℚ)} (s : Pair p G tests) :
    order (place p _ s.private_independent) (algebraMap _ _ G) = 1 ∧
      place p _ s.ordinary_independent (algebraMap _ _ G) = 1 := by
  have hp : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  let x := value p s.privately G
  have hx : x ≠ 0 := norm_ne_zero_iff.mp (s.private_norm ▸ norm_ne_zero_iff.mpr hp)
  have he := EvaluationChoices.valuation_eq_of_norm_eq p.val hx hp s.private_norm
  constructor
  · rw [order, place_polynomial]
    change -WithZero.log (Padic.mulValuation x) = 1
    simp [Padic.mulValuation, hx, he]
  · rw [place_polynomial]
    exact mulValuation_eq_one_of_norm_eq_one _ s.ordinary_norm

theorem Pair.tests_are_units {p : PrimeIndex} {G : MvPolynomial (Fin (r+1)) ℚ}
    {tests : Finset (MvPolynomial (Fin (r+1)) ℚ)} (s : Pair p G tests) {f : MvPolynomial (Fin (r+1)) ℚ}
    (hf : f ∈ tests) :
    place p _ s.private_independent (algebraMap _ _ f) = 1 ∧
      place p _ s.ordinary_independent (algebraMap _ _ f) = 1 := by
  rw [place_polynomial, place_polynomial]
  exact ⟨mulValuation_eq_one_of_norm_eq_one _ (s.private_tests _ hf),
    mulValuation_eq_one_of_norm_eq_one _ (s.ordinary_tests _ hf)⟩

end UnconditionalCounterexample.Variations.PrivateGuards
