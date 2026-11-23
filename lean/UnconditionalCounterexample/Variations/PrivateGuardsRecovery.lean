import UnconditionalCounterexample.Variations.MultivariateRecovery

/-! # Recovering the localization enlarged by private guard denominators

The main sequence supplies the leading forms, proper intersections and word
numerators. Every generator of the enlarged denominator monoid divides the
denominators of infinitely many such words, including the auxiliary factors.
Thus the integral extension obtained by adjoining the coordinates contains
the inverses of every main and auxiliary denominator.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuardsRecovery

open MvPolynomial MultivariateInfinity MultivariateInversion MultivariateFibres MultivariateRecovery

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]

section FiniteVariables
variable [Finite σ]

private theorem isUnit_of_main_powers {C : Type*} [CommRing C]
    (φ : MvPolynomial σ k →+* C) (F : ℕ → MvPolynomial σ k) (r : ℕ)
    (hgeom : ∀ s : Finset ℕ, s.card = r + 1 → ∀ u : σ → K,
      ∃ i ∈ s, aeval u (F i) ≠ 0)
    (f : MvPolynomial σ k)
    (hword : {i | ∃ a : ℕ, 0 < a ∧ φ f ∣ φ (F i) ^ a}.Infinite) : IsUnit (φ f) := by
  by_contra h
  obtain ⟨m, hm, hj⟩ := exists_max_ideal_of_mem_nonunits h
  obtain ⟨s, hs, hcard⟩ := hword.exists_subset_card_eq (r + 1)
  have hspan : Ideal.span (F '' (s : Set ℕ)) = ⊤ := by
    apply span_eq_top_of_no_common_zero (K := K)
    intro u
    obtain ⟨i, hi, hne⟩ := hgeom s hcard u
    exact ⟨F i, ⟨i, hi, rfl⟩, hne⟩
  have hle : Ideal.span (F '' (s : Set ℕ)) ≤ m.comap φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨a, _, b, hb⟩ := hs hi
    apply hm.isPrime.mem_of_pow_mem a
    rw [hb]; exact m.mul_mem_right b hj
  exact (Ideal.comap_ne_top φ hm.ne_top) (top_unique (hspan ▸ hle))

private theorem finite_of_main_powers {B : Type*} [CommRing B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B]
    (D F : ℕ → MvPolynomial σ k) [IsLocalization (Submonoid.closure (Set.range D)) B]
    (A : Subalgebra k B)
    (hint : ∀ i, IsIntegral A (algebraMap (MvPolynomial σ k) B (X i)))
    (hgeom : ∀ s : Finset ℕ, s.card = Nat.card σ + 1 → ∀ u : σ → K,
      ∃ i ∈ s, aeval u (F i) ≠ 0)
    (hword : ∀ j, {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A), 0 < a ∧ D j ∣ H ∧
      algebraMap (MvPolynomial σ k) B (F i) ^ a = algebraMap (MvPolynomial σ k) B H * w}.Infinite) :
    Module.Finite A B := by
  let x (i : σ) := algebraMap (MvPolynomial σ k) B (X i)
  let E := Algebra.adjoin A (Set.range x)
  have hfg : Module.Finite A E := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x)
    (fun _ ⟨i, hi⟩ => hi ▸ hint i)
  let y (i : σ) : E := ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let φ := (aeval (R := k) y).toRingHom
  have hφall : (E.restrictScalars k).val.comp (aeval (R := k) y) = IsScalarTower.toAlgHom k (MvPolynomial σ k) B := by
    ext i
    change ((aeval (R := k) y (X i) : E) : B) = _
    rw [aeval_X]; rfl
  have hφ (p : MvPolynomial σ k) : (φ p : B) = algebraMap (MvPolynomial σ k) B p :=
    DFunLike.congr_fun hφall p
  have hdiv (j : ℕ) : {i | ∃ a : ℕ, 0 < a ∧ φ (D j) ∣ φ (F i) ^ a}.Infinite := by
    apply (hword j).mono
    rintro i ⟨a,H,w,ha,⟨q,rfl⟩,hw⟩
    refine ⟨a, ha, φ q * algebraMap A E w, Subtype.ext ?_⟩
    change (φ (F i) : B) ^ a = (φ (D j) : B) * ((φ q : B) * w)
    simpa only [hφ, map_mul, mul_assoc] using hw
  have htop := subalgebra_eq_top_of_denominator_units D E φ hφ
    (fun j => isUnit_of_main_powers φ F (Nat.card σ) hgeom (D j) (hdiv j))
  apply Module.Finite.of_surjective E.val.toLinearMap
  exact fun b => ⟨⟨b, htop.ge (by trivial)⟩, rfl⟩

end FiniteVariables

variable [Fintype σ]

/-- Recover the entire enlarged horizontal localization from late main powers.
The denominator sequence `D` can include arbitrary auxiliary polynomials.
Only the separately indexed main sequence `F` satisfies the leading-form
and proper-intersection conditions. -/
theorem recover
    (D F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ)
    (B : Type*) [CommRing B] [IsDomain B] [Algebra k B] [Algebra (MvPolynomial σ k) B]
    [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization (Submonoid.closure (Set.range D)) B]
    (E : Type*) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E]
    [IsLocalization ((Submonoid.closure (Set.range D)).map (MvPolynomial.map (algebraMap k K))) E]
    (A : Subalgebra k B)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (htop : ∀ i, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ s : Finset ℕ, s.card = Fintype.card σ → ∀ j : σ,
      ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i)
    (hgeom : ∀ s : Finset ℕ, s.card = Nat.card σ + 1 → ∀ u : σ → K,
      ∃ i ∈ s, aeval u (F i) ≠ 0)
    (hword : ∀ j, {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A),
      H.totalDegree < a * d i ∧ D j ∣ H ∧
      algebraMap (MvPolynomial σ k) B (F i) ^ a = algebraMap (MvPolynomial σ k) B H * w}.Infinite)
    (hpoints : let M := (Submonoid.closure (Set.range D)).map (MvPolynomial.map (algebraMap k K))
      ∀ P : Ideal (MvPolynomial σ K), P.IsPrime → ¬ P.IsMaximal →
        Disjoint (M : Set (MvPolynomial σ K)) (P : Set (MvPolynomial σ K)) →
        ∃ u : σ → K, Retained M u ∧ P ≤ pointIdeal u)
    (hsep : let M := Submonoid.closure (Set.range D)
      let N := M.map (MvPolynomial.map (algebraMap k K))
      ∀ u v : σ → K, ∀ hu : Retained N u, ∀ hv : Retained N v, u ≠ v →
        ∃ a : A, pointEval N E u hu (baseElement (K := K) M E (a : B)) ≠
          pointEval N E v hv (baseElement (K := K) M E (a : B)))
    (hdir : let M := Submonoid.closure (Set.range D)
      let N := M.map (MvPolynomial.map (algebraMap k K))
      ∀ u : σ → K, Retained N u → ∀ v : σ → K, v ≠ 0 →
        ∃ a : A, ∃ p q : MvPolynomial σ K,
          algebraMap (MvPolynomial σ K) E p = baseElement (K := K) M E (a : B) * algebraMap _ E q ∧
          quotientDerivativeNumerator u v p q ≠ 0) : A = ⊤ := by
  let M := Submonoid.closure (Set.range D)
  let N := M.map (MvPolynomial.map (algebraMap k K))
  let x (i : σ) := algebraMap (MvPolynomial σ k) B (X i)
  have heval : aeval (R := k) x = IsScalarTower.toAlgHom k (MvPolynomial σ k) B := by
    ext i; simp [x]
  have hint (j : σ) : IsIntegral A (x j) := by
    apply integral_coordinates_in_domain A x F l d hl htop hlin _ j
    apply (hword 0).mono
    rintro i ⟨a,H,w,hd,_,hw⟩
    exact ⟨a,H,w,hd,heval ▸ hw⟩
  let : Module.Finite A B := finite_of_main_powers D F A hint hgeom (by
    intro j; apply (hword j).mono
    rintro i ⟨a,H,w,hd,hdiv,hw⟩
    have ha : a ≠ 0 := by rintro rfl; simp at hd
    exact ⟨a,H,w,Nat.pos_of_ne_zero ha,hdiv,hw⟩)
  let e := tensorEquiv (K := K) M B E
  let A' := (ScalarExtension.subalgebraBaseChange k K A).map e.toAlgHom
  let : Module.Finite A' E := ScalarExtension.finite_mapped_subalgebraBaseChange k K A e
  let lift (a : A) : A' := ⟨baseElement (K := K) M E (a : B), baseElement_mem_baseChange M E A a⟩
  apply ScalarExtension.subalgebra_eq_top_of_mapped_baseChange_eq_top k K A e
  apply subalgebra_eq_top_of_separation_and_tangents N E A' (retainedPoint_of_prime N hpoints)
  · intro u v hu hv hne
    obtain ⟨a,ha⟩ := hsep u v hu hv hne
    exact ⟨lift a,ha⟩
  · intro u hu v hv
    obtain ⟨a,p,q,hfrac,hd⟩ := hdir u hu v hv
    obtain ⟨f,hf,hdf⟩ := cleared_tangent N E u hu v (lift a : E) p q hfrac hd
    exact ⟨lift a,f,q,hf,hdf⟩

end UnconditionalCounterexample.Variations.PrivateGuardsRecovery
