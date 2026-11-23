import UnconditionalCounterexample.Variations.PrivateGuardsNumberField
import UnconditionalCounterexample.Variations.PrivateGuardsSmooth
import UnconditionalCounterexample.Variations.PrivateGuardsSeed
import UnconditionalCounterexample.PolynomialAvoidance
import UnconditionalCounterexample.ConstructionReturns

/-! # Simultaneous specialization of the two private guard sites

A finite extension contains the coordinates of the smooth and ordinary points.
One embedding of this field preserves all the test values, the distinguished
partial derivative, and the distinction between the first residues.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial GuardSupport

private theorem ordinary_point {r : ℕ}
    (G : MvPolynomial (Fin (r+1)) ℚ) (hg : Irreducible G)
    (tests : Finset (MvPolynomial (Fin (r+1)) ℚ)) (ht : ∀ f ∈ tests, ¬ G ∣ f)
    (a : AlgebraicClosure ℚ) :
    ∃ y : Fin (r+1) → AlgebraicClosure ℚ,
      y 0 ≠ a ∧ aeval y G ≠ 0 ∧ ∀ f ∈ tests, aeval y f ≠ 0 := by
  classical
  let K := AlgebraicClosure ℚ
  let box : Set K := {a}ᶜ
  have hinf : box.Infinite := Set.Finite.infinite_compl (Set.finite_singleton _)
  obtain ⟨y,hy,hyf⟩ := PolynomialAvoidance.exists_simultaneous_nonzero_on_box
    (fun _ : Fin (r+1) => box) (fun _ => hinf) (insert G tests)
    (MvPolynomial.map (algebraMap ℚ K)) fun f hf => by
      rw [← map_zero (MvPolynomial.map (algebraMap ℚ K))]
      apply (MvPolynomial.map_injective (algebraMap ℚ K) (algebraMap ℚ K).injective).ne
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hg.ne_zero
      · exact fun h => ht f hf (h ▸ dvd_zero _)
  have hn f (hf : f ∈ insert G tests) : aeval y f ≠ 0 := by
    simpa only [eval_map, aeval_def] using hyf f hf
  exact ⟨y, hy 0, hn G (Finset.mem_insert_self ..), fun f hf => hn f (Finset.mem_insert_of_mem hf)⟩

private theorem specialize_points {r : ℕ} (L : Type*) [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (G : MvPolynomial (Fin (r+1)) ℚ)
    (tests : Finset (MvPolynomial (Fin (r+1)) ℚ)) (j : Fin (r+1))
    (x y : Fin (r+1) → L) (hd : x 0 ≠ y 0)
    (hxG : aeval x G = 0) (hxj : aeval x (pderiv j G) ≠ 0) (hyG : aeval y G ≠ 0)
    (hxt : ∀ f ∈ tests, aeval x f ≠ 0) (hyt : ∀ f ∈ tests, aeval y f ≠ 0) (N : ℕ) :
    ∃ p : PrimeIndex, N < p.val ∧ Nonempty (SmoothSeed p G tests) := by
  classical
  let U := insert G tests
  let V := insert (pderiv j G) U
  let coords := Finset.univ.image x ∪ Finset.univ.image y
  let coeffs := U.biUnion fun f => f.coeffs.image (algebraMap ℚ L)
  let Q := {x 0 - y 0} ∪ coords ∪ coeffs ∪ V.image (aeval x) ∪ U.image (aeval y)
  obtain ⟨p,hp,φ,hφ⟩ := PrivateGuardsNumberField.exists_embedding L (Q.erase 0)
    (fun _ hs => (Finset.mem_erase.mp hs).1) N
  have hon (s : L) (hs : s ∈ Q) (hn : s ≠ 0) : ‖φ s‖ = 1 :=
    ConstructionReturns.norm_eq_one_of_mulValuation_eq_one _ (hφ _ (Finset.mem_erase.mpr ⟨hn,hs⟩))
  have hle (s : L) (hs : s ∈ Q) : ‖φ s‖ ≤ 1 := by
    by_cases hn : s = 0
    · simp [hn]
    · exact (hon s hs hn).le
  have hC (s : L) (hs : s ∈ coords) : s ∈ Q := by simp [Q, hs]
  let xp (i) : ℤ_[p.val] := ⟨φ (x i), hle _ (hC _ (Finset.mem_union_left _
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))))⟩
  let yp (i) : ℤ_[p.val] := ⟨φ (y i), hle _ (hC _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))))⟩
  have ex (f : MvPolynomial (Fin (r+1)) ℚ) : value p xp f = φ (aeval x f) :=
    (comp_aeval_apply x φ f).symm
  have ey (f : MvPolynomial (Fin (r+1)) ℚ) : value p yp f = φ (aeval y f) :=
    (comp_aeval_apply y φ f).symm
  have hu f (hf : f ∈ U) (hn : aeval y f ≠ 0) : ‖value p yp f‖ = 1 := by
    rw [ey]; exact hon _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hf)) hn
  have hv f (hf : f ∈ V) (hn : aeval x f ≠ 0) : ‖value p xp f‖ = 1 := by
    rw [ex]; exact hon _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ hf))) hn
  refine ⟨p,hp,⟨⟨xp,yp,j,?_,by simp [ex,hxG],hv _ (Finset.mem_insert_self ..) hxj,
    hu _ (Finset.mem_insert_self ..) hyG,fun f hf => hv f (by simp [V,U,hf]) (hxt f hf),
    fun f hf => hu f (by simp [U,hf]) (hyt f hf),?_⟩⟩⟩
  · have hnorm := hon (x 0 - y 0) (by simp [Q]) (sub_ne_zero.mpr hd)
    rw [map_sub] at hnorm
    have hd' : IsUnit (xp 0 - yp 0) := PadicInt.isUnit_iff.mpr hnorm
    exact sub_ne_zero.mp (by simpa using (padicInt_isUnit_iff_toZMod_ne_zero _).mp hd')
  · intro f hf q hq
    have hc : algebraMap ℚ L q ∈ coeffs := Finset.mem_biUnion.mpr
      ⟨f, Finset.mem_insert.mpr hf, Finset.mem_image_of_mem _ hq⟩
    simpa using hle _ (show algebraMap ℚ L q ∈ Q from Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hc)))

/-- Every irreducible rational hypersurface admits a smooth private seed
and a distinct ordinary seed at arbitrarily large rational primes. -/
theorem exists_smoothSeed {r : ℕ} (G : MvPolynomial (Fin (r+1)) ℚ) (hg : Irreducible G)
    (tests : Finset (MvPolynomial (Fin (r+1)) ℚ)) (ht : ∀ f ∈ tests, ¬ G ∣ f) (N : ℕ) :
    ∃ p : PrimeIndex, N < p.val ∧ Nonempty (SmoothSeed p G tests) := by
  classical
  obtain ⟨j,x,hxG,hxj,hxt⟩ := exists_smooth_point G hg tests ht
  obtain ⟨y,hxy,hyG,hyt⟩ := ordinary_point G hg tests ht (x 0)
  let S := Finset.univ.image x ∪ Finset.univ.image y
  let L := IntermediateField.adjoin ℚ (S : Set (AlgebraicClosure ℚ))
  let : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin
    fun z _ => Algebra.IsIntegral.isIntegral z
  let xL (i) : L := ⟨x i, IntermediateField.subset_adjoin ℚ _ (Finset.mem_union_left _
    (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
  let yL (i) : L := ⟨y i, IntermediateField.subset_adjoin ℚ _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
  have ex (f : MvPolynomial (Fin (r+1)) ℚ) : L.val (aeval xL f) = aeval x f :=
    comp_aeval_apply xL L.val f
  have ey (f : MvPolynomial (Fin (r+1)) ℚ) : L.val (aeval yL f) = aeval y f :=
    comp_aeval_apply yL L.val f
  refine specialize_points L G tests j xL yL (fun h => hxy (congrArg Subtype.val h).symm)
    (L.val.injective ((ex G).trans (hxG.trans (map_zero L.val).symm))) ?_ ?_ ?_ ?_ N
  · exact fun h => hxj (by rw [← ex, h, map_zero])
  · exact fun h => hyG (by rw [← ey, h, map_zero])
  · exact fun f hf h => hxt f hf (by rw [← ex, h, map_zero])
  · exact fun f hf h => hyt f hf (by rw [← ey, h, map_zero])

end UnconditionalCounterexample.Variations.PrivateGuards
