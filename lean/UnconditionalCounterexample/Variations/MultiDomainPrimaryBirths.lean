import UnconditionalCounterexample.Variations.MultiDomainPrimaryLimit

/-!
# Choosing each actual multivariate primary

The stage keeps every older raw polynomial a unit at the new primary and
also tests an increasing list of integral polynomials. A family of these
births consequently stabilizes at the horizontal order of every fraction.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.MultiDomain

open MvPolynomial IndependentTuples GuardSupport Filter WithZero

variable {r : ℕ}

private theorem screening_for_family (s : Finset (Polys (r+1))) (hs : ∀ f ∈ s, ¬ X 0 ∣ f) :
    ∃ t : Finset (IntPolys (r+1)), (∀ F ∈ t, restrictToCentre r F ≠ 0) ∧
      ∀ v : Valuation (FunctionField (r+1)) ℤᵐ⁰,
        (∀ F ∈ t, v (algebraMap _ _ (rationalize F)) = 1) → ∀ f ∈ s, v (algebraMap _ _ f) = 1 := by
  classical
  choose t ht hu using fun (f : s) ↦ screening_for f.val (hs _ f.property)
  refine ⟨Finset.univ.biUnion t, fun F h ↦ ?_, fun v h f hf ↦ ?_⟩
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
    exact ht i F hi
  · exact hu ⟨f,hf⟩ v fun G hG ↦ h G (Finset.mem_biUnion.mpr ⟨⟨f,hf⟩, Finset.mem_univ _, hG⟩)

/-- A birth records the p-adic coordinates, their exact first order and the
permanent unit promises for all earlier raw polynomials and current tests. -/
structure PrimaryBirth (r j k : ℕ) (old : Finset (Polys (r+1))) where
  prime : PrimeIndex
  tuple : LocalTuple (r+1) (Padic.mulValuation (p := prime.val))
  order : tuple.valuation (coordinate 0) = exp (-(k : ℤ))
  old_units : ∀ f ∈ old, tuple.valuation (algebraMap _ _ f) = 1
  screened : ∀ F ∈ primaryTests r j, tuple.valuation (algebraMap _ _ (rationalize F)) = 1

private theorem integral_tuple (p : PrimeIndex) (a : Fin (r+1) → ℤ_[p.val])
    (hI : AlgebraicIndependent ℚ (fun i ↦ (a i).val)) :
    ∃ T : LocalTuple (r+1) (Padic.mulValuation (p := p.val)), T.x = fun i ↦ (a i).val := by
  refine ⟨⟨_, hI, fun i ↦ ?_⟩, rfl⟩
  apply le_of_not_gt
  intro h
  have hn := (Padic.norm_lt_norm_iff_mulValuation_lt (x := 1) (y := (a i).val)).mpr
    (by simpa only [map_one] using h)
  simp only [norm_one] at hn
  exact (not_lt_of_ge (a i).property) hn

private theorem valuation_screened (p : PrimeIndex) (a : Fin (r+1) → ℤ_[p.val])
    (T : LocalTuple (r+1) (Padic.mulValuation (p := p.val))) (hx : T.x = fun i ↦ (a i).val)
    {F : IntPolys (r+1)} (h : IsUnit (eval₂Hom (Int.castRingHom ℤ_[p.val]) a F)) :
    T.valuation (algebraMap _ _ (rationalize F)) = 1 := by
  let e := eval₂Hom (Int.castRingHom ℤ_[p.val]) a
  have hmaps : ((aeval T.x : Polys (r+1) →ₐ[ℚ] ℚ_[p.val]).toRingHom.comp rationalize) =
      (PadicInt.Coe.ringHom (p := p.val)).comp e := by
    ext i <;> simp [rationalize, e, hx]
    rfl
  change Padic.mulValuation (IndependentTuples.evaluation T.x T.independent _) = 1
  have he : IndependentTuples.evaluation T.x T.independent (algebraMap _ _ (rationalize F)) =
      MvPolynomial.aeval T.x (rationalize F) :=
    IsFractionRing.lift_algebraMap (K := FunctionField (r+1))
      (g := (MvPolynomial.aeval T.x : Polys (r+1) →ₐ[ℚ] ℚ_[p.val]).toRingHom)
      T.independent (rationalize F)
  rw [he]
  change Padic.mulValuation (((aeval T.x : Polys (r+1) →ₐ[ℚ] ℚ_[p.val]).toRingHom.comp rationalize) F) = 1
  rw [hmaps]
  exact GuardSupport.mulValuation_eq_one_of_norm_eq_one _ (PadicInt.isUnit_iff.mp h)

/-- A fresh prime may be chosen above an arbitrary cutoff, even when the
previous rational polynomials have denominators. -/
theorem exists_primary (j k : ℕ) (hk : 0 < k) (old : Finset (Polys (r+1)))
    (hold : ∀ f ∈ old, ¬ X 0 ∣ f) (used : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ B : PrimaryBirth r j k old, cutoff < B.prime.val ∧ B.prime ∉ used := by
  classical
  obtain ⟨s,hs,hs'⟩ := screening_for_family old hold
  let tests := primaryTests r j ∪ s
  have hall : ∀ F ∈ tests, restrictToCentre r F ≠ 0 :=
    fun F h ↦ (Finset.mem_union.mp h).elim primaryTests_nonvanishing (hs F)
  obtain ⟨p,a,hp,hu,hI,hk',ha⟩ := exists_screened_primary r k hk tests hall used cutoff
  obtain ⟨T,hx⟩ := integral_tuple p a hI
  have hv (F) (h : F ∈ tests) := valuation_screened p a T hx (ha F h)
  refine ⟨⟨p,T,?_, hs' T.valuation (fun _ h ↦ hv _ (Finset.mem_union_right _ h)),
    fun _ h ↦ hv _ (Finset.mem_union_left _ h)⟩, hp, hu⟩
  have hne : (a 0).val ≠ 0 := by
    intro h
    rw [h, Padic.valuation_zero] at hk'
    omega
  rw [T.valuation_coordinate, hx]
  simp [Padic.mulValuation, hne, hk']

theorem primaryBirths_stabilize {old : ℕ → Finset (Polys (r+1))}
    (birth : (j : ℕ) → PrimaryBirth r j (if j = 0 then 2 else 1) (old j)) (z : FunctionField (r+1)) :
    ∀ᶠ j in atTop, (birth j).tuple.valuation z = tVal z := by
  apply eventually_primary_horizontal _ (fun j ↦ (birth j).screened)
  filter_upwards [eventually_gt_atTop 0] with j hj
  simpa [hj.ne'] using (birth j).order

end UnconditionalCounterexample.Variations.MultiDomain
