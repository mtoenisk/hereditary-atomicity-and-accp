import UnconditionalCounterexample.IntersectionDomain
import UnconditionalCounterexample.EvaluationDVR

/-!
# Singleton isolators and the actual vertical stalks

The center of a retained valuation is its positive-value ideal. A p-adic residue map
proves maximality. A function whose only positive vertical value occurs at that center
clears denominators and identifies the localization with the valuation ring.

The isolator and its profile remain explicit inputs here; the simultaneous
construction must produce them. No full-stalk or maximal-completeness property
is assumed.
-/

noncomputable section
namespace UnconditionalCounterexample.IntersectionStalks
open WithZero IntersectionDomain
variable {K ι Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]

/-- The actual inclusion into one retained valuation ring. -/
def valuationInclusion (B : Subring K) (v : ι → Valuation K Γ₀) (i : ι) :
    intersection B v →+* (v i).valuationSubring where
  toFun x := ⟨x, (mem_intersection B v x).mp x.property |>.2 i⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The positive-value center in the actual intersection. -/
def center (B : Subring K) (v : ι → Valuation K Γ₀) (i : ι) : Ideal (intersection B v) :=
  Ideal.comap (valuationInclusion B v i) (IsLocalRing.maximalIdeal (v i).valuationSubring)

@[simp] theorem mem_center (B : Subring K) (v : ι → Valuation K Γ₀) (i : ι)
    (x : intersection B v) : x ∈ center B v i ↔ v i x < 1 :=
  Valuation.mem_maximalIdeal_iff K (v i)

instance center_isPrime (B : Subring K) (v : ι → Valuation K Γ₀) (i : ι) :
    (center B v i).IsPrime := by
  dsimp [center]
  infer_instance

/-- A prime-field residue map already makes the center maximal: the intersection
contains all integer constants, so the restricted residue map is surjective. -/
theorem center_isMaximal_of_residueMap (B : Subring K) (v : ι → Valuation K Γ₀) (i : ι)
    (p : ℕ) [Fact p.Prime] (r : (v i).valuationSubring →+* ZMod p)
    (hr : RingHom.ker r = IsLocalRing.maximalIdeal (v i).valuationSubring) :
    (center B v i).IsMaximal := by
  have hker : RingHom.ker (r.comp (valuationInclusion B v i)) = center B v i := by
    rw [← RingHom.comap_ker, hr]
    rfl
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective _ (ZMod.ringHom_surjective _)

/-- Specialization to the actual restricted p-adic evaluation residue maps. -/
theorem evaluation_center_isMaximal (B : Subring K) (p : ι → ℕ)
    [∀ i, Fact (p i).Prime] (e : ∀ i, K →+* ℚ_[p i]) (i : ι) :
    (center B (fun j => EvaluationDVR.valuation (p j) (e j)) i).IsMaximal :=
  center_isMaximal_of_residueMap B _ i (p i) (EvaluationDVR.residueMap (p i) (e i))
    (EvaluationDVR.residueMap_ker (p i) (e i))

/-- Every nonzero integral value has a nonnegative additive exponent. -/
theorem exists_nat_value (v : Valuation K ℤᵐ⁰) (x : K) (hx : x ≠ 0) (hv : v x ≤ 1) :
    ∃ m : ℕ, v x = exp (-(m : ℤ)) := by
  have hlog : log (v x) ≤ 0 := by
    rw [← exp_le_exp, exp_log (v.ne_zero_iff.mpr hx), exp_zero]
    exact hv
  refine ⟨(-log (v x)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (neg_nonneg.mpr hlog), neg_neg, exp_log (v.ne_zero_iff.mpr hx)]

/-- Division by powers of a singleton isolator whose inverse lies in B preserves every other
vertical integrality condition. The remaining place is tested explicitly. -/
theorem div_pow_mem_of_bound (B : Subring K) (v : ι → Valuation K Γ₀) (i : ι)
    (z f : K) (hz : z ∈ intersection B v) (hfinv : f⁻¹ ∈ B)
    (hother : ∀ j, j ≠ i → v j f = 1) (m : ℕ) (hi : v i (z / f ^ m) ≤ 1) :
    z / f ^ m ∈ intersection B v := by
  apply (mem_intersection B v _).mpr
  refine ⟨?_, ?_⟩
  · rw [div_eq_mul_inv, ← inv_pow]
    exact B.mul_mem ((mem_intersection B v z).mp hz).1 (B.pow_mem hfinv m)
  · intro j
    by_cases hj : j = i
    · simpa [hj] using hi
    · rw [map_div₀, map_pow, hother j hj, one_pow, div_one]
      exact ((mem_intersection B v z).mp hz).2 j

/-- The singleton isolator clears any denominator without entering its center. -/
theorem exists_denominator_outside_center (B : Subring K)
    (v : ι → Valuation K ℤᵐ⁰) (i : ι) (f : K) (k : ℕ) (hk : 0 < k)
    (hfinv : f⁻¹ ∈ B) (hfi : v i f = exp (-(k : ℤ)))
    (hfother : ∀ j, j ≠ i → v j f = 1)
    (x : K) (hx : v i x ≤ 1) (b : K) (hb : b ∈ intersection B v) (hb0 : b ≠ 0)
    (hxb : x * b ∈ intersection B v) :
    ∃ s : K, s ∈ intersection B v ∧ v i s = 1 ∧ x * s ∈ intersection B v := by
  obtain ⟨m, hm⟩ := exists_nat_value (v i) b hb0 (((mem_intersection B v b).mp hb).2 i)
  let s := b ^ k / f ^ m
  have hsval : v i s = 1 := by
    dsimp [s]
    rw [map_div₀, map_pow, map_pow, hm, hfi, ← exp_nsmul, ← exp_nsmul, ← exp_sub]
    have hzero : k • (-(m : ℤ)) - m • (-(k : ℤ)) = 0 := by
      simp only [nsmul_eq_mul]
      ring
    rw [hzero, exp_zero]
  have hs : s ∈ intersection B v :=
    div_pow_mem_of_bound B v i (b ^ k) f ((intersection B v).pow_mem hb k)
      hfinv hfother m (by rw [← hsval])
  have hxeq : x * s = ((x * b) * b ^ (k - 1)) / f ^ m := by
    dsimp [s]
    have hpow : b ^ k = b ^ (k - 1) * b := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [hpow]
    ring
  have hxs : x * s ∈ intersection B v := by
    rw [hxeq]
    apply div_pow_mem_of_bound B v i ((x * b) * b ^ (k - 1)) f
      ((intersection B v).mul_mem hxb ((intersection B v).pow_mem hb _)) hfinv hfother m
    rw [← hxeq, map_mul, hsval, mul_one]
    exact hx
  exact ⟨s, hs, hsval, hxs⟩

instance valuationAlgebra (B : Subring K) (v : ι → Valuation K Γ₀) (i : ι) :
    Algebra (intersection B v) (v i).valuationSubring :=
  (valuationInclusion B v i).toAlgebra

instance valuationScalarTower (B : Subring K) (v : ι → Valuation K Γ₀) (i : ι) :
    IsScalarTower (intersection B v) (v i).valuationSubring K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- A singleton isolator identifies the full valuation ring with the actual
localization at its center; no stalk-equality assumption is used. -/
theorem valuation_isLocalization (B : Subring K) (v : ι → Valuation K ℤᵐ⁰) (i : ι)
    [IsFractionRing (intersection B v) K]
    (f : K) (k : ℕ) (hk : 0 < k) (hfinv : f⁻¹ ∈ B)
    (hfi : v i f = exp (-(k : ℤ))) (hfother : ∀ j, j ≠ i → v j f = 1) :
    IsLocalization (center B v i).primeCompl (v i).valuationSubring := by
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hs : ¬ v i (s.val : K) < 1 := by
      simpa only [Ideal.mem_primeCompl_iff, mem_center] using s.property
    by_contra hnunit
    apply hs
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hnunit)
  · intro x
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (intersection B v) (x : K)
    have hb0 : (b : K) ≠ 0 := by
      intro h
      exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) (Subtype.ext h)
    have hxb : (x : K) * b ∈ intersection B v := by
      rw [← hab]
      change (a : K) / (b : K) * b ∈ intersection B v
      rw [div_mul_cancel₀ _ hb0]
      exact a.property
    obtain ⟨s, hs, hsval, hxs⟩ := exists_denominator_outside_center B v i f k hk hfinv
      hfi hfother x x.property b b.property hb0 hxb
    let d : intersection B v := ⟨s, hs⟩
    have hd : d ∈ (center B v i).primeCompl := by
      rw [Ideal.mem_primeCompl_iff, mem_center]
      change ¬ v i s < 1
      rw [hsval]
      exact lt_irrefl _
    refine ⟨⟨⟨(x : K) * s, hxs⟩, ⟨d, hd⟩⟩, ?_⟩
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have heq : x = y := by
      apply Subtype.ext
      exact congrArg (fun z : (v i).valuationSubring => (z : K)) hxy
    simp [heq]

/-- The canonical stalk equivalence obtained from a singleton isolator. -/
def stalkEquiv (B : Subring K) (v : ι → Valuation K ℤᵐ⁰) (i : ι)
    [IsFractionRing (intersection B v) K]
    (f : K) (k : ℕ) (hk : 0 < k) (hfinv : f⁻¹ ∈ B)
    (hfi : v i f = exp (-(k : ℤ))) (hfother : ∀ j, j ≠ i → v j f = 1) :
    Localization.AtPrime (center B v i) ≃ₐ[intersection B v] (v i).valuationSubring := by
  letI := valuation_isLocalization B v i f k hk hfinv hfi hfother
  exact IsLocalization.algEquiv (center B v i).primeCompl _ _

@[simp] theorem stalkEquiv_algebraMap (B : Subring K)
    (v : ι → Valuation K ℤᵐ⁰) (i : ι) [IsFractionRing (intersection B v) K]
    (f : K) (k : ℕ) (hk : 0 < k) (hfinv : f⁻¹ ∈ B)
    (hfi : v i f = exp (-(k : ℤ))) (hfother : ∀ j, j ≠ i → v j f = 1)
    (x : intersection B v) :
    stalkEquiv B v i f k hk hfinv hfi hfother
      (algebraMap (intersection B v) (Localization.AtPrime (center B v i)) x) =
        valuationInclusion B v i x :=
  (stalkEquiv B v i f k hk hfinv hfi hfother).commutes x

/-- The stalk is a DVR whenever the retained valuation ring is a DVR. -/
theorem stalk_isDVR (B : Subring K) (v : ι → Valuation K ℤᵐ⁰) (i : ι)
    [IsFractionRing (intersection B v) K] [IsDiscreteValuationRing (v i).valuationSubring]
    (f : K) (k : ℕ) (hk : 0 < k) (hfinv : f⁻¹ ∈ B)
    (hfi : v i f = exp (-(k : ℤ))) (hfother : ∀ j, j ≠ i → v j f = 1) :
    IsDiscreteValuationRing (Localization.AtPrime (center B v i)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (stalkEquiv B v i f k hk hfinv hfi hfother).symm

/-- The radical of a singleton isolator is its positive-value center. -/
theorem radical_span_isolator (B : Subring K) (v : ι → Valuation K ℤᵐ⁰) (i : ι)
    (f : intersection B v) (k : ℕ) (hk : 0 < k) (hfinv : (f : K)⁻¹ ∈ B)
    (hfi : v i f = exp (-(k : ℤ))) (hfother : ∀ j, j ≠ i → v j f = 1) :
    (Ideal.span ({f} : Set (intersection B v))).radical = center B v i := by
  have hf0 : f ≠ 0 := by
    intro hf
    have := hfi
    exact exp_ne_zero (this.symm.trans (by simp [hf]))
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff (center_isPrime B v i)).mpr
    rw [Ideal.span_singleton_le_iff_mem, mem_center, hfi, exp_lt_one_iff]
    exact neg_neg_of_pos (by exact_mod_cast hk)
  · intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxK : (x : K) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxv := (mem_center B v i x).mp hx
    obtain ⟨m, hm⟩ := exists_nat_value (v i) x hxK hxv.le
    have hmpos : 0 < m := by
      rw [hm, exp_lt_one_iff] at hxv
      omega
    have hbound : v i ((x : K) ^ k / f ^ (1 : ℕ)) ≤ 1 := by
      rw [map_div₀, map_pow, hm, map_pow, hfi, pow_one, ← exp_nsmul, ← exp_sub,
        exp_le_one_iff]
      simp only [nsmul_eq_mul]
      have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hmpos
      have hk0 : (0 : ℤ) ≤ k := by positivity
      nlinarith
    have hquot := div_pow_mem_of_bound B v i ((x : K) ^ k) f
      ((intersection B v).pow_mem x.property k) hfinv hfother 1 hbound
    refine ⟨k, ?_⟩
    rw [Ideal.mem_span_singleton, subring_dvd_iff_div_mem _ f (x ^ k) hf0]
    change (x : K) ^ k / (f : K) ∈ intersection B v
    simpa only [pow_one] using hquot

/-- The paired-isolator identity classifies every prime containing their product. -/
theorem prime_eq_one_of_isolator_radicals {R : Type*} [CommRing R]
    (P M N : Ideal R) [P.IsPrime] [M.IsMaximal] [N.IsMaximal]
    (f g : R) (hf : (Ideal.span ({f} : Set R)).radical = M)
    (hg : (Ideal.span ({g} : Set R)).radical = N) (hfg : f * g ∈ P) :
    P = M ∨ P = N := by
  have hP : P.IsPrime := inferInstance
  rcases hP.mem_or_mem hfg with h | h
  · left
    have hle : M ≤ P := by
      rw [← hf]
      apply hP.radical_le_iff.mpr
      rwa [Ideal.span_singleton_le_iff_mem]
    exact (Ideal.IsMaximal.eq_of_le (inferInstance : M.IsMaximal) hP.ne_top hle).symm
  · right
    have hle : N ≤ P := by
      rw [← hg]
      apply hP.radical_le_iff.mpr
      rwa [Ideal.span_singleton_le_iff_mem]
    exact (Ideal.IsMaximal.eq_of_le (inferInstance : N.IsMaximal) hP.ne_top hle).symm

end UnconditionalCounterexample.IntersectionStalks
