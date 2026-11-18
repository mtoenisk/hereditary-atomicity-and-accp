import HereditaryAtomicity.DVRBase.ComponentClasses
import HereditaryAtomicity.DVRBase.SourceRecurrenceBlocking
import HereditaryAtomicity.DVRBase.MultiplaceConsequencesPicard

/-! Genuine weighted component principalization for support descent. -/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors BigOperators
variable {R ι : Type*} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R] [Fintype ι]

/-- A constant weighted product of genuine component classes along a source
chain gives a new source chain. Its ratios generate the weighted integral
component products. No principal generators or local return are assumed. -/
theorem exists_principalized_chain_of_weighted_component_class_constant
    (π : ι → R) (U : ι → Set (MaximalSpectrum R))
    (hU : ∀ i, IsClopenInFiber (π i) (U i)) (e : ι → ℕ)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hclass : ∀ n, (∏ i, componentClassHom (hU i)
        ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩ ^ e i) =
      ∏ i, componentClassHom (hU i)
        ⟨x 0, mem_nonZeroDivisors_of_ne_zero (hx 0)⟩ ^ e i) :
    ∃ (c a : ℕ → R), (∀ n, c n ≠ 0) ∧ Associated (c 0) (x 0 ^ ∑ i, e i) ∧
      (∀ n, c n = c (n + 1) * a n) ∧
      ∀ n (ht : t n ≠ 0), Ideal.span {a n} =
        ∏ i, componentIdeal (hU i) (t n) ht ^ e i := by
  classical
  have ht (n : ℕ) : t n ≠ 0 := fun hz => hx n (by rw [hxt n, hz, mul_zero])
  let I (n : ℕ) := ∏ i, componentIdeal (hU i) (x n) (hx n) ^ e i
  choose J hIJ hcop using fun i => (componentIdeal_spec (hU i) (x 0) (hx 0)).comaximal
  have hJ (i : ι) : IsUnit (J i : FractionalIdeal R⁰ (FractionRing R)) :=
    (show IsComaximalFactor (x 0) (J i) from ⟨componentIdeal (hU i) (x 0) (hx 0),
      by simpa only [mul_comm] using hIJ i, by simpa only [sup_comm] using hcop i⟩).isUnit (hx 0)
  let H (n : ℕ) := I n * ∏ i, J i ^ e i
  let V (n : ℕ) : (FractionalIdeal R⁰ (FractionRing R))ˣ :=
    (∏ i, componentUnit (hU i) (x n) (hx n) ^ e i) * ∏ i, (hJ i).unit ^ e i
  have hV (n : ℕ) : (V n : FractionalIdeal R⁰ (FractionRing R)) = H n := by
    change (Units.coeHom (FractionalIdeal R⁰ (FractionRing R))) (V n) = _
    simp only [V, map_mul, map_prod, map_pow, Units.coeHom_apply,
      componentUnit_coe, IsUnit.unit_spec]
    change (∏ i, (FractionalIdeal.coeIdealHom R⁰ (FractionRing R))
      (componentIdeal (hU i) (x n) (hx n)) ^ e i) *
      (∏ i, (FractionalIdeal.coeIdealHom R⁰ (FractionRing R)) (J i) ^ e i) = _
    simp only [← map_pow, ← map_prod, ← map_mul]
    rfl
  have hH0 : H 0 = Ideal.span {x 0 ^ ∑ i, e i} := by
    dsimp [H, I]
    rw [← Finset.prod_mul_distrib]
    simp only [← mul_pow, hIJ]
    simp only [Ideal.span_singleton_pow]
    rw [Ideal.prod_span_singleton, Finset.prod_pow_eq_pow_sum]
  have hV0 : ClassGroup.mk (FractionRing R) (V 0) = 1 :=
    (ClassGroup.mk_eq_one_of_coe_ideal (hV 0)).mpr
      ⟨x 0 ^ ∑ i, e i, pow_ne_zero _ (hx 0), hH0⟩
  have hVclass (n : ℕ) : ClassGroup.mk (FractionRing R) (V n) = 1 := by
    have hc := hclass n
    change (∏ i, ClassGroup.mk (FractionRing R) (componentUnit (hU i) (x n) (hx n)) ^ e i) =
      ∏ i, ClassGroup.mk (FractionRing R) (componentUnit (hU i) (x 0) (hx 0)) ^ e i at hc
    calc
      _ = ClassGroup.mk (FractionRing R) (V 0) := by
        simp only [V, map_mul, map_prod, map_pow, hc]
      _ = 1 := hV0
  choose c hc0 hc using fun n => (ClassGroup.mk_eq_one_of_coe_ideal (hV n)).mp (hVclass n)
  have hIstep (n : ℕ) : I n = I (n + 1) *
      ∏ i, componentIdeal (hU i) (t n) (ht n) ^ e i := by
    dsimp [I]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← mul_pow]
    congr 1
    simpa only [hxt n] using componentIdeal_mul (hU i) (x (n + 1)) (t n) (hx (n + 1)) (ht n)
  have hHstep (n : ℕ) : H n = H (n + 1) *
      ∏ i, componentIdeal (hU i) (t n) (ht n) ^ e i := by
    simp only [H, hIstep n]
    ring
  have hcdiv (n : ℕ) : c (n + 1) ∣ c n := by
    apply Ideal.span_singleton_le_span_singleton.mp
    rw [← hc, ← hc, hHstep]
    exact Ideal.mul_le_left
  choose a ha using hcdiv
  refine ⟨c, a, hc0, ?_, ha, ?_⟩
  · exact Ideal.span_singleton_eq_span_singleton.mp ((hc 0).symm.trans hH0)
  · intro n htn
    apply (Ideal.span_singleton_mul_left_inj (hc0 (n + 1))).mp
    rw [Ideal.span_singleton_mul_span_singleton, mul_comm (a n), ← ha,
      ← hc (n + 1), ← hc n, hHstep, mul_comm (H (n + 1))]

/-- A weighted component generator has precisely the union of the positive
weight component supports. Regions need not be disjoint for this identity. -/
theorem support_of_span_eq_weighted_component_product
    (π : ι → R) (U : ι → Set (MaximalSpectrum R))
    (hU : ∀ i, IsClopenInFiber (π i) (U i)) (e : ι → ℕ)
    (d : R) (hd : d ≠ 0) (a : R)
    (ha : Ideal.span {a} = ∏ i, componentIdeal (hU i) d hd ^ e i)
    (P : MaximalSpectrum R) :
    a ∈ P.asIdeal ↔ ∃ i, 0 < e i ∧ P ∈ U i ∧ d ∈ P.asIdeal := by
  classical
  let f := algebraMap R (Localization.AtPrime P.asIdeal)
  let q : ι → Localization.AtPrime P.asIdeal := fun i => if P ∈ U i then f d ^ e i else 1
  have hm (i : ι) : (Ideal.mapHom f) (componentIdeal (hU i) d hd ^ e i) =
      Ideal.span {q i} := by
    change Ideal.map f _ = _
    rw [Ideal.map_pow]
    by_cases hP : P ∈ U i
    · rw [(componentIdeal_spec (hU i) d hd).map_mem P hP]
      simp only [q, hP, ite_true, Ideal.span_singleton_pow, f]
    · rw [(componentIdeal_spec (hU i) d hd).map_not_mem P hP]
      simp only [q, hP, ite_false, ← Ideal.one_eq_top, one_pow, Ideal.span_singleton_one]
  have hassoc : Associated (f a) (∏ i, q i) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    have he := congrArg (Ideal.mapHom f) ha
    rw [map_prod] at he
    simpa only [Ideal.mapHom_apply, Ideal.map_span, Set.image_singleton, hm,
      Ideal.prod_span_singleton] using he
  have hunit : IsUnit (f a) ↔ ∀ i, IsUnit (q i) :=
    hassoc.isUnit_iff.trans (by simp only [IsUnit.prod_iff, Finset.mem_univ, forall_const])
  constructor
  · intro haP
    by_contra hn
    push Not at hn
    have hu : IsUnit (f a) := hunit.mpr (fun i => by
      dsimp [q]
      split_ifs with hP
      · by_cases he : e i = 0
        · simp only [he, pow_zero, isUnit_one]
        · exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ d).mpr
            (hn i (Nat.pos_of_ne_zero he) hP)).pow _
      · exact isUnit_one)
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ a).mp hu) haP
  · rintro ⟨i, he, hP, hdP⟩
    by_contra haP
    have hu := (hunit.mp ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ a).mpr haP)) i
    simp only [q, hP, ite_true] at hu
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ d).mp
      ((isUnit_pow_iff he.ne').mp hu)) hdP

/-- The weighted principalization retains literal source support, in addition
to its exact principal integral ideals. -/
theorem exists_supported_chain_of_weighted_component_class_constant
    (π : ι → R) (U : ι → Set (MaximalSpectrum R))
    (hU : ∀ i, IsClopenInFiber (π i) (U i)) (e : ι → ℕ)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hclass : ∀ n, (∏ i, componentClassHom (hU i)
        ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩ ^ e i) =
      ∏ i, componentClassHom (hU i)
        ⟨x 0, mem_nonZeroDivisors_of_ne_zero (hx 0)⟩ ^ e i) :
    ∃ (c a : ℕ → R), (∀ n, c n ≠ 0) ∧ Associated (c 0) (x 0 ^ ∑ i, e i) ∧
      (∀ n, c n = c (n + 1) * a n) ∧
      ∀ n (P : MaximalSpectrum R), a n ∈ P.asIdeal ↔
        ∃ i, 0 < e i ∧ P ∈ U i ∧ t n ∈ P.asIdeal := by
  obtain ⟨c, a, hc, hc0, hstep, hgen⟩ :=
    exists_principalized_chain_of_weighted_component_class_constant π U hU e x t hx hxt hclass
  refine ⟨c, a, hc, hc0, hstep, ?_⟩
  intro n P
  have ht : t n ≠ 0 := fun hz => hx n (by rw [hxt n, hz, mul_zero])
  exact support_of_span_eq_weighted_component_product π U hU e (t n) ht (a n) (hgen n ht) P

end HereditaryAtomicity.DVRBase
