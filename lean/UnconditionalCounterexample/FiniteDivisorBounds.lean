import UnconditionalCounterexample.Target
import Factorization.LengthSets
import Factorization.PrincipalIdeals
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Sym

noncomputable section
namespace UnconditionalCounterexample.FiniteDivisorBounds

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Finite divisor classes bound all decompositions into nonunits. -/
theorem multiset_card_lt_divisor_ncard (s : Multiset R) (hs0 : s.prod ≠ 0)
    (hs : ∀ a ∈ s, ¬ IsUnit a)
    (hf : (Set.Iic (Associates.mk s.prod)).Finite) :
    s.card < (Set.Iic (Associates.mk s.prod)).ncard := by
  induction s using Multiset.induction_on with
  | empty =>
    exact (Set.ncard_pos hf).mpr ⟨Associates.mk (1 : R), by simp⟩
  | @cons a s ih =>
    have hprod : a * s.prod ≠ 0 := by simpa only [Multiset.prod_cons] using hs0
    have ht : s.prod ≠ 0 := right_ne_zero_of_mul hprod
    have ha := hs a (Multiset.mem_cons_self a s)
    have hlt : Associates.mk s.prod < Associates.mk (a * s.prod) := by
      apply Associates.dvdNotUnit_iff_lt.mp
      apply Associates.mk_dvdNotUnit_mk_iff.mpr
      exact ⟨ht, a, ha, mul_comm a s.prod⟩
    have hsub : Set.Iic (Associates.mk s.prod) ⊂ Set.Iic (Associates.mk (a * s.prod)) :=
      Set.Iic_ssubset_Iic.mpr hlt
    have hf' : (Set.Iic (Associates.mk (a * s.prod))).Finite := by
      simpa only [Multiset.prod_cons] using hf
    have hi := ih ht (fun b hb => hs b (Multiset.mem_cons_of_mem hb)) (hf'.subset hsub.le)
    have hc := Set.ncard_lt_ncard hsub hf'
    simp only [Multiset.card_cons, Multiset.prod_cons]
    omega

theorem hasBoundedFactorizations_of_finite_divisor_classes {x : R} (hx : x ≠ 0)
    (hf : {a : Associates R | a ∣ Associates.mk x}.Finite) :
    Factorization.HasBoundedFactorizations x := by
  refine ⟨(Set.Iic (Associates.mk x)).ncard, ?_⟩
  intro s hs hassoc
  have hmk : Associates.mk s.prod = Associates.mk x := Associates.mk_eq_mk_iff_associated.mpr hassoc
  have hs0 : s.prod ≠ 0 := hassoc.ne_zero_iff.mpr hx
  have hf' : (Set.Iic (Associates.mk s.prod)).Finite := by
    rw [hmk]
    exact hf
  have hb := multiset_card_lt_divisor_ncard s hs0 hs hf'
  rw [hmk] at hb
  exact hb.le

omit [IsDomain R] in
/-- When the only units are signs, each associate class has at most two elements. -/
theorem finite_divisors_of_finite_classes
    (hsigns : ∀ u : R, IsUnit u → u = 1 ∨ u = -1) {x : R}
    (hf : {a : Associates R | a ∣ Associates.mk x}.Finite) : {a : R | a ∣ x}.Finite := by
  apply ((hf.image Quot.out).union ((hf.image Quot.out).image (fun z : R => -z))).subset
  intro z hz
  have hm : Associates.mk z ∈ {a : Associates R | a ∣ Associates.mk x} :=
    Associates.mk_dvd_mk.mpr hz
  obtain ⟨u,hu⟩ := Associates.mk_quot_out z
  rcases hsigns u u.isUnit with h | h
  · exact Or.inl ⟨Associates.mk z, hm, by simpa only [h, mul_one] using hu⟩
  · exact Or.inr ⟨Quot.out (Associates.mk z), ⟨Associates.mk z, hm, rfl⟩,
      by simpa only [h, mul_neg_one] using hu⟩

omit [IsDomain R] in
theorem finite_divisors_subring (T : Subring R) (x : T)
    (hf : {a : R | a ∣ (x : R)}.Finite) : {a : T | a ∣ x}.Finite := by
  apply (hf.preimage Subtype.val_injective.injOn).subset
  intro z hz
  exact map_dvd T.subtype hz

omit [IsDomain R] in
theorem finite_classes_of_finite_divisors {x : R}
    (hf : {a : R | a ∣ x}.Finite) : {a : Associates R | a ∣ Associates.mk x}.Finite := by
  apply (hf.image Associates.mk).subset
  intro a ha
  obtain ⟨z,rfl⟩ := Associates.mk_surjective a
  exact ⟨z, Associates.mk_dvd_mk.mp ha, rfl⟩

omit [IsDomain R] in
theorem not_hasStrictChainAt_of_finite_divisors {x : R}
    (hf : {a : R | a ∣ x}.Finite) : ¬ HasStrictChainAt x := by
  rintro ⟨z,hz0,_,hstrict⟩
  have hmem : Set.range z ⊆ {a : R | a ∣ x} := by
    rintro a ⟨n,rfl⟩
    have h := Ideal.span_singleton_le_span_singleton.mp (hstrict.monotone (Nat.zero_le n))
    rwa [hz0] at h
  have hinj : Function.Injective z := by
    intro i j h
    apply hstrict.injective
    exact congrArg (fun a : R => Ideal.span ({a} : Set R)) h
  exact (Set.infinite_range_of_injective hinj) (hf.subset hmem)

/-- Multisets of bounded cardinality over a finite alphabet form a finite set. -/
theorem finite_multisets_of_mem_of_card {α : Type*} {s : Set α} (hs : s.Finite) (N : ℕ) :
    {m : Multiset α | (∀ a ∈ m, a ∈ s) ∧ m.card ≤ N}.Finite := by
  classical
  let all : Finset (Multiset α) := (Finset.range (N+1)).biUnion
    (fun k => (hs.toFinset.sym k).image (fun m => m.val))
  apply all.finite_toSet.subset
  rintro m ⟨hm,hcard⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨m.card, Finset.mem_range.mpr (by omega), Finset.mem_image.mpr ?_⟩
  refine ⟨⟨m,rfl⟩, ?_, rfl⟩
  apply Finset.mem_sym_iff.mpr
  intro a ha
  exact hs.mem_toFinset.mpr (hm a ha)

/-- Finite actual divisors give finitely many nonunit factorizations as multisets. -/
theorem finite_nonunit_factorizations {x : R} (hx : x ≠ 0)
    (hf : {a : R | a ∣ x}.Finite) :
    {s : Multiset R | (∀ a ∈ s, ¬ IsUnit a) ∧ Associated s.prod x}.Finite := by
  obtain ⟨N,hN⟩ := hasBoundedFactorizations_of_finite_divisor_classes hx
    (finite_classes_of_finite_divisors hf)
  apply (finite_multisets_of_mem_of_card hf N).subset
  rintro s ⟨hs,hprod⟩
  refine ⟨?_,hN s hs hprod⟩
  intro a ha
  exact (Multiset.dvd_prod ha).trans hprod.dvd

theorem finite_atomic_factorizations {x : R} (hx : x ≠ 0)
    (hf : {a : R | a ∣ x}.Finite) :
    {s : Multiset R | (∀ a ∈ s, Irreducible a) ∧ Associated s.prod x}.Finite :=
  (finite_nonunit_factorizations hx hf).subset (fun _ hs =>
    ⟨fun a ha => (hs.1 a ha).not_isUnit, hs.2⟩)

end UnconditionalCounterexample.FiniteDivisorBounds
