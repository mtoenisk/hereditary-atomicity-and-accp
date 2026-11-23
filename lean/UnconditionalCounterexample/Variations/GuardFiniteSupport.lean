import UnconditionalCounterexample.Variations.MultivariateSelectionFrozen

/-!
# Guard support of an arbitrary element of the function field

The growing residue tests for the assigned guards include the reduction of
each integral polynomial. One of its nonzero coefficients survives away from
finitely many primes. Clearing coefficients and passing to quotients therefore
gives finite guard support for every nonzero rational function.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open Filter GuardSupport MvPolynomial Variations MultiDomain

variable {r : ℕ}

theorem eventually_reduction_ne_zero (F : IntPolys (r+1)) (hF : F ≠ 0) :
    ∀ᶠ p : PrimeIndex in cofinite, MvPolynomial.map (Int.castRingHom (ZMod p.val)) F ≠ 0 := by
  classical
  obtain ⟨m, hc⟩ := MvPolynomial.exists_coeff_ne_zero hF
  have ht : Tendsto (fun p : PrimeIndex => p.val) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Subtype.val_injective.tendsto_cofinite
  filter_upwards [ht.eventually (eventually_gt_atTop (F.coeff m).natAbs)] with p hp
  intro hz
  have hm := congrArg (fun f : MvPolynomial (Fin (r+1)) (ZMod p.val) => f.coeff m) hz
  have hcmod : ((F.coeff m : ℤ) : ZMod p.val) = 0 := by simpa [MvPolynomial.coeff_map] using hm
  have hab := Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcmod)
  exact (not_le_of_gt hp) (Nat.le_of_dvd (Int.natAbs_pos.mpr hc) (by simpa using hab))

theorem ScreenedGuard.unit_of_avoids {p : PrimeIndex} (G : ScreenedGuard r p) (F : IntPolys (r+1))
    (h : G.avoids (MvPolynomial.map (Int.castRingHom (ZMod p.val)) F)) :
    G.tuple.valuation (algebraMap _ _ (rationalize F)) = 1 := by
  let E := GaloisField p.val G.degree
  let O := WittVector p.val E
  let L := GuardUnramified.LocalField p.val E
  let j := algebraMap O L
  let ev := eval₂Hom (Int.castRingHom O) G.w
  let red : O →+* E := WittVector.constantCoeff
  have hu : IsUnit (ev F) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change red.comp ev F ≠ 0
    change eval₂Hom (algebraMap (ZMod p.val) E) (fun i => (G.w i).coeff 0)
      (MvPolynomial.map (Int.castRingHom (ZMod p.val)) F) ≠ 0 at h
    rw [eval₂Hom_map_hom] at h
    have he : red.comp ev = eval₂Hom ((algebraMap (ZMod p.val) E).comp (Int.castRingHom _))
        (fun i => (G.w i).coeff 0) := by
      ext i <;> simp [red, ev]
      rfl
    rwa [he]
  have hm : ((aeval G.tuple.x : Polys (r+1) →ₐ[ℚ] L).toRingHom.comp rationalize) = j.comp ev := by
    ext i <;> simp [j, ev, rationalize, ScreenedGuard.tuple, O, L, E]
  change GuardUnramified.valuation p.val E
    (IndependentTuples.evaluation G.tuple.x G.tuple.independent (algebraMap _ _ (rationalize F))) = 1
  rw [show IndependentTuples.evaluation G.tuple.x G.tuple.independent (algebraMap _ _ (rationalize F)) =
      aeval G.tuple.x (rationalize F) from IsFractionRing.lift_algebraMap
        (K := FunctionField (r+1)) (g := (aeval G.tuple.x : Polys (r+1) →ₐ[ℚ] L).toRingHom) _ _]
  change GuardUnramified.valuation p.val E (((aeval G.tuple.x : Polys (r+1) →ₐ[ℚ] L).toRingHom.comp rationalize) F) = 1
  rw [hm]
  exact Valuation.Integers.one_of_isUnit' hu fun w => (GuardUnramified.integral_iff _ _ _).mpr ⟨w,rfl⟩

theorem finite_guard_support (stage : PrimeIndex → ℕ) (cofinal : Tendsto stage cofinite atTop)
    (G : (p : PrimeIndex) → ScreenedGuard r p)
    (screened : ∀ p f, f ∈ guardTests r (stage p) p → f ≠ 0 → (G p).avoids f)
    (z : FunctionField (r+1)) (hz : z ≠ 0) : {p | (G p).tuple.valuation z ≠ 1}.Finite := by
  classical
  have hInt (F : IntPolys (r+1)) (hF : F ≠ 0) :
      ∀ᶠ p : PrimeIndex in cofinite, (G p).tuple.valuation (algebraMap _ _ (rationalize F)) = 1 := by
    obtain ⟨N, hN⟩ := guardTests_cover F
    filter_upwards [cofinal.eventually (eventually_ge_atTop N), eventually_reduction_ne_zero F hF] with p hp hn
    exact (G p).unit_of_avoids F (screened p _ (hN _ hp p) hn)
  have hPoly (f : Polys (r+1)) (hf : f ≠ 0) :
      ∀ᶠ p : PrimeIndex in cofinite, (G p).tuple.valuation (algebraMap _ _ f) = 1 := by
    obtain ⟨n, hn, F, he⟩ := clear_polynomial f
    have hc : C (σ := Fin (r+1)) (n : ℚ) ≠ 0 := C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
    have hF : F ≠ 0 := fun h => (mul_ne_zero hc hf) (he.symm.trans (by simp [h]))
    filter_upwards [hInt F hF, hInt (C (n : ℤ)) (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne'))] with p h h'
    simp only [rationalize, map_C, Int.coe_castRingHom, Int.cast_natCast] at h'
    rwa [he, map_mul, map_mul, h', one_mul] at h
  obtain ⟨a,b,hb,he⟩ := IsFractionRing.div_surjective (Polys (r+1)) z
  have ha : a ≠ 0 := fun h => hz (by simp [← he, h])
  apply eventually_cofinite.mp
  filter_upwards [hPoly a ha, hPoly b (nonZeroDivisors.ne_zero hb)] with p h₁ h₂
  simp [← he, map_div₀, h₁, h₂]

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {q : PrimeIndex}
    (L : LocalPrescription r q) (G : Geometry r K)

/-- A finite stage can have introduced only finitely many permanent guards. -/
theorem firstAppearance_tendsto : Tendsto (firstAppearance L G) cofinite atTop := by
  apply tendsto_atTop.mpr
  intro n
  apply eventually_cofinite.mpr
  apply (table L G n).covered.finite_toSet.subset
  intro p hp
  change ¬ n ≤ firstAppearance L G p at hp
  exact (table_grows_of_le L G (le_of_lt (lt_of_not_ge hp))).choose (first_mem L G p)

/-- Every nonzero rational function has finite support among the guards of
the actual chronological construction. -/
theorem permanent_finite_guard_support (z : FunctionField (r+1)) (hz : z ≠ 0) :
    {p | ((places L G).guard p).valuation z ≠ 1}.Finite :=
  finite_guard_support (firstAppearance L G) (firstAppearance_tendsto L G)
    (fun p => (permanentFibre L G p).guard) (fun _ => permanent_guard_test L G) z hz

end UnconditionalCounterexample.MultivariateSelection
