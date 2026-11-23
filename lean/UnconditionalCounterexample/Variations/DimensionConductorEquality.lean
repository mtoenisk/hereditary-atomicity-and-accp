import UnconditionalCounterexample.Variations.DimensionLocalBounded
import UnconditionalCounterexample.Variations.DimensionResidueAlgebra
import UnconditionalCounterexample.Variations.DimensionLocalConductor

/-!
# Conductor equality at a finite family of closed points

The word congruences give the radical of the conductor. A nonreduced
conductor quotient would produce a nonzero residue-valued derivation. Every
linear observation on this quotient is bounded on the image of the integral
subring. Divergence of the directional derivatives rules this out, giving the
actual conductor and its finite evaluation fields.
-/

namespace UnconditionalCounterexample.Variations

open RadicalConductor

/-- Every closed residue field of a nilpotent thickening is one of the retained
evaluation fields, with agreement on the original evaluation homomorphism. -/
theorem exists_residue_equiv_of_radical_eq_iInf {k B ι : Type*} [Field k] [CommRing B]
    [Algebra k B] [Finite ι] {E : ι → Type*} [∀ i, Field (E i)] [∀ i, Algebra k (E i)]
    (I : Ideal B) (ev : ∀ i, B →ₐ[k] E i) (hs : ∀ i, Function.Surjective (ev i))
    (hr : I.radical = ⨅ i, RingHom.ker (ev i)) (P : Ideal (B ⧸ I)) (hP : P.IsMaximal) :
    ∃ i, ∃ e : ((B ⧸ I) ⧸ P) ≃ₐ[k] E i, ∀ x,
      e (Ideal.Quotient.mk P (Ideal.Quotient.mk I x)) = ev i x := by
  classical
  let := Fintype.ofFinite ι
  let q := (Ideal.Quotient.mkₐ k P).comp (Ideal.Quotient.mkₐ k I)
  have hq : Function.Surjective q := (Ideal.Quotient.mk_surjective (I := P)).comp
    (Ideal.Quotient.mk_surjective (I := I))
  let := hP
  let J := RingHom.ker q
  have hJ : J.IsPrime := RingHom.ker_isPrime q
  have hle : I ≤ J := by
    intro x hx
    change Ideal.Quotient.mk P (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  have hcap : (⨅ i, RingHom.ker (ev i)) ≤ J := hr ▸ hJ.radical_le_iff.mpr hle
  have hfin : Finset.univ.inf (fun i ↦ RingHom.ker (ev i)) ≤ J := by simpa [Finset.inf_eq_iInf] using hcap
  obtain ⟨i, _, hi⟩ := hJ.prod_le.mp (Ideal.prod_le_inf.trans hfin)
  have hmax := RingHom.ker_isMaximal_of_surjective (ev i).toRingHom (hs i)
  have heq : J = RingHom.ker (ev i) := (hmax.eq_of_le hJ.ne_top hi).symm
  let e1 := Ideal.quotientKerAlgEquivOfSurjective hq
  let e2 := Ideal.quotientEquivAlgOfEq k heq
  let e3 := Ideal.quotientKerAlgEquivOfSurjective (hs i)
  refine ⟨i, e1.symm.trans (e2.trans e3), fun x ↦ ?_⟩
  change e3 (e2 (e1.symm (q x))) = _
  rw [show e1.symm (q x) = Ideal.Quotient.mk J x from Ideal.quotientKerAlgEquivOfSurjective_symm_apply hq x]
  rfl


variable {K B : Type*} [NontriviallyNormedField K] [CompleteSpace K] [ProperSpace K]
    [CommRing B] [Algebra K B]

/-- Escape of every nonzero residue-valued derivation defeats each possible nilpotent
thickening of the conductor quotient. The residue fields are quantified over its maximal ideals. -/
theorem conductor_isRadical_of_derivation_escape (T : Subring B)
    (hstable : ∀ (b : K), ‖b‖ ≤ 1 → ∀ x ∈ T, b • x ∈ T)
    (hclear : ∀ x : B, ∃ c : K, c ≠ 0 ∧ c • x ∈ T)
    [FiniteDimensional K (B ⧸ conductorIdeal T)]
    (hesc : ∀ P : Ideal (B ⧸ conductorIdeal T), P.IsMaximal →
      ∀ d : Derivation K B ((B ⧸ conductorIdeal T) ⧸ P), d ≠ 0 →
        ∃ L : ((B ⧸ conductorIdeal T) ⧸ P) →ₗ[K] K,
          ∀ R : ℝ, ∃ x ∈ T, R < ‖L (d x)‖) :
    (conductorIdeal T).IsRadical := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  apply isReduced_of_residue_derivations_eq_zero K
  intro P hP d
  by_contra hd
  let δ := d.compAlgebraMap B
  have hδ : δ ≠ 0 := by
    intro he
    apply hd
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact DFunLike.congr_fun he x
  obtain ⟨L, hu⟩ := hesc P hP δ hδ
  obtain ⟨R, hR⟩ := bounded_linear_observation_mod_conductor T hstable hclear (L.comp d.toLinearMap)
  obtain ⟨x, hx, hbig⟩ := hu R
  exact hbig.not_ge (hR _ hx)

/-- Recover the actual conductor from its radical and from directional escape at
the specified closed residue points. The derivative product rule uses evaluation
in the indicated residue field. -/
theorem conductor_eq_point_kernels_of_directional_escape {ι : Type*} [Finite ι]
    {E : ι → Type*} [∀ i, NontriviallyNormedField (E i)] [∀ i, NormedAlgebra K (E i)]
    [∀ i, FiniteDimensional K (E i)] [IsNoetherianRing B]
    (T : Subring B) (ev : ∀ i, B →ₐ[K] E i)
    (hsurj : Function.Surjective (AlgHom.pi ev))
    (hrad : (conductorIdeal T).radical = ⨅ i, RingHom.ker (ev i))
    (hstable : ∀ (b : K), ‖b‖ ≤ 1 → ∀ x ∈ T, b • x ∈ T)
    (hclear : ∀ x : B, ∃ c : K, c ≠ 0 ∧ c • x ∈ T)
    (hesc : ∀ i, ∀ δ : B →ₗ[K] E i, δ ≠ 0 →
      (∀ x y, δ (x*y) = ev i x * δ y + ev i y * δ x) → ∀ R : ℝ, ∃ x ∈ T, R < ‖δ x‖) :
    conductorIdeal T = ⨅ i, RingHom.ker (ev i) := by
  classical
  let := Fintype.ofFinite ι
  let I := conductorIdeal T
  have hker : RingHom.ker (AlgHom.pi ev) = I.radical := by
    rw [hrad]
    ext x
    simp only [Ideal.mem_iInf, RingHom.mem_ker]
    exact funext_iff
  have := finite_quotient_of_eval_ker_eq_radical I (AlgHom.pi ev) hsurj hker
  have he (i : ι) : Function.Surjective (ev i) := by
    intro x
    obtain ⟨y, hy⟩ := hsurj (Pi.single i x)
    exact ⟨y, by simpa using congrFun hy i⟩
  suffices hred : IsReduced (B ⧸ I) by
    exact ((Ideal.isRadical_iff_quotient_reduced I).mpr hred).radical.symm.trans hrad
  apply isReduced_of_residue_derivations_eq_zero K
  intro P hP d
  by_contra hd
  obtain ⟨i, e, hev⟩ := exists_residue_equiv_of_radical_eq_iInf I ev he hrad P hP
  let q := Ideal.Quotient.mkₐ K I
  let L := e.toLinearMap.comp d.toLinearMap
  let δ := L.comp q.toLinearMap
  have hδ : δ ≠ 0 := by
    intro h
    apply hd
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact e.map_eq_zero_iff.mp (DFunLike.congr_fun h x)
  have hprod (x y : B) : δ (x*y) = ev i x * δ y + ev i y * δ x := by
    change e (d (q (x*y))) = _
    rw [map_mul, d.leibniz, map_add]
    change e (Ideal.Quotient.mk P (q x) * d (q y)) + e (Ideal.Quotient.mk P (q y) * d (q x)) = _
    have heq (b : B) : e (Ideal.Quotient.mk P (q b)) = _ := hev b
    rw [map_mul, map_mul, heq, heq]
    rfl
  obtain ⟨R, hR⟩ := bounded_linear_observation_mod_conductor T hstable hclear L
  obtain ⟨x, hx, hbig⟩ := hesc i δ hδ hprod R
  exact hbig.not_ge (hR _ hx)

end UnconditionalCounterexample.Variations
