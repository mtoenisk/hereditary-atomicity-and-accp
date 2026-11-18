import UnconditionalCounterexample.SparsePrimaryDomain
import UnconditionalCounterexample.PairedResidues
import UnconditionalCounterexample.PrimeIndexSignature

/-!
# Prime residues of the sparse-primary intersection

At a retained primary prime the literal evaluations give two residue factors;
at an omitted prime the sole guard gives one. These are quotients by pD, and
the retained primes are exactly the additive prime indices of unital subrings.
-/

noncomputable section
namespace UnconditionalCounterexample.SparseResidues
open Polynomial GuardSupport WithZero SparsePrimaryDomain

local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (S : Set ℚ[X]) (d : Places)

def primaryIntegerMap (i : ℕ) : domain S d →+* ℤ_[(d.primes i).val] :=
  (EvaluationDVR.integerMap _
    (EvaluationDVR.evaluationHom _ (d.primary i).val (d.primary_trans i))).comp
    (IntersectionStalks.valuationInclusion (PoleAlgebra.generated S).toSubring (vertical d) (.inl i))

def guardIntegerMap (p : PrimeIndex) : domain S d →+* ℤ_[p.val] :=
  (EvaluationDVR.integerMap _ (guardEvaluation d.guard d.guard_trans p)).comp
    (IntersectionStalks.valuationInclusion (PoleAlgebra.generated S).toSubring (vertical d) (.inr p))

@[simp] theorem primaryIntegerMap_X (i : ℕ) :
    primaryIntegerMap S d i ⟨RatFunc.X, X_mem S d⟩ = d.primary i := by
  apply Subtype.ext
  exact EvaluationDVR.evaluationHom_X _ _ _

@[simp] theorem guardIntegerMap_X (p : PrimeIndex) :
    guardIntegerMap S d p ⟨RatFunc.X, X_mem S d⟩ = d.guard p := by
  apply Subtype.ext
  exact EvaluationDVR.evaluationHom_X _ _ _

/-- The first coordinate is the retained primary and the second its guard. -/
def pairResidue (i : ℕ) : domain S d →+* ZMod (d.primes i).val × ZMod (d.primes i).val :=
  (PadicInt.toZMod.comp (primaryIntegerMap S d i)).prod
    (PadicInt.toZMod.comp (guardIntegerMap S d (d.primes i)))

@[simp] theorem pairResidue_X (i : ℕ) :
    pairResidue S d i ⟨RatFunc.X, X_mem S d⟩ =
      (PadicInt.toZMod (d.primary i), PadicInt.toZMod (d.guard (d.primes i))) := by
  simp [pairResidue]

/-- Vanishing of an integral evaluation modulo p permits division by p. -/
theorem valuation_div_le_one_of_residue_zero {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (e : K →+* ℚ_[p]) (x : K) (z : ℤ_[p])
    (hz : e x = z) (hzero : PadicInt.toZMod z = 0) :
    EvaluationDVR.valuation p e (x / (p : K)) ≤ 1 := by
  have hm : z ∈ RingHom.ker PadicInt.toZMod := hzero
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have heq : e (x / (p : K)) = (w : ℚ_[p]) := by
    rw [map_div₀, map_natCast, hz]
    have hw' := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hw
    simp only [PadicInt.coe_mul, PadicInt.coe_natCast] at hw'
    rw [hw', mul_div_cancel_left₀ _ hp]
  exact (EvaluationDVR.mem_valuationSubring p e _).mpr (by rw [heq]; exact w.property)

/-- The other guards, including every unpaired guard, see p as a unit. -/
theorem div_mem_domain_of_pairResidue_eq_zero (i : ℕ) (x : domain S d)
    (hx : pairResidue S d i x = 0) :
    (x : RatFunc ℚ) / ((d.primes i).val : RatFunc ℚ) ∈ domain S d := by
  obtain ⟨hxB, hxv⟩ := (IntersectionDomain.mem_intersection _ _ _).mp x.property
  have hf : PadicInt.toZMod (primaryIntegerMap S d i x) = 0 := congrArg Prod.fst hx
  have hg : PadicInt.toZMod (guardIntegerMap S d (d.primes i) x) = 0 := congrArg Prod.snd hx
  apply (IntersectionDomain.mem_intersection _ _ _).mpr
  constructor
  · rw [div_eq_mul_inv]
    apply (PoleAlgebra.generated S).mul_mem hxB
    simpa using (PoleAlgebra.generated S).algebraMap_mem (((d.primes i).val : ℚ)⁻¹)
  · rintro (j | p)
    · by_cases hji : j = i
      · subst j
        exact valuation_div_le_one_of_residue_zero (d.primes i).val
          (EvaluationDVR.evaluationHom _ (d.primary i).val (d.primary_trans i))
          (x : RatFunc ℚ) (primaryIntegerMap S d i x) rfl hf
      · have hpq : (d.primes i).val ≠ (d.primes j).val := by
          intro heq
          exact hji (d.primes.injective (Subtype.ext heq)).symm
        have hv := PairedResidues.valuation_prime_eq_one_of_ne (d.primes i).val (d.primes j).val
          (EvaluationDVR.evaluationHom _ (d.primary j).val (d.primary_trans j)) hpq
        change vertical d (.inl j) (_ / _) ≤ 1
        rw [map_div₀, show vertical d (.inl j) ((d.primes i).val : RatFunc ℚ) = 1 from hv, div_one]
        exact hxv (.inl j)
    · by_cases hpi : p = d.primes i
      · subst p
        exact valuation_div_le_one_of_residue_zero (d.primes i).val
          (guardEvaluation d.guard d.guard_trans (d.primes i))
          (x : RatFunc ℚ) (guardIntegerMap S d (d.primes i) x) rfl hg
      · have hpq : (d.primes i).val ≠ p.val := fun h => hpi (Subtype.ext h).symm
        have hv := PairedResidues.valuation_prime_eq_one_of_ne (d.primes i).val p.val
          (guardEvaluation d.guard d.guard_trans p) hpq
        change vertical d (.inr p) (_ / _) ≤ 1
        rw [map_div₀, show vertical d (.inr p) ((d.primes i).val : RatFunc ℚ) = 1 from hv, div_one]
        exact hxv (.inr p)

theorem pairResidue_ker (i : ℕ) :
    RingHom.ker (pairResidue S d i) = Ideal.span {((d.primes i).val : domain S d)} := by
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    refine ⟨⟨(x : RatFunc ℚ) / ((d.primes i).val : RatFunc ℚ),
      div_mem_domain_of_pairResidue_eq_zero S d i x hx⟩, ?_⟩
    apply Subtype.ext
    exact (mul_div_cancel₀ (x : RatFunc ℚ)
      (Nat.cast_ne_zero.mpr (d.primes i).property.ne_zero)).symm
  · apply Ideal.span_le.mpr
    rintro x rfl
    change pairResidue S d i ((d.primes i).val : domain S d) = 0
    rw [map_natCast]
    apply Prod.ext <;> exact ZMod.natCast_self _

theorem pairResidue_surjective (i : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i))) :
    Function.Surjective (pairResidue S d i) := by
  apply PairedResidues.pairMap_surjective_of_unit_difference _ _ ⟨RatFunc.X, X_mem S d⟩
  rw [pairResidue_X]
  simpa only [map_sub] using
    (PairedResidues.difference_isUnit (d.primary i) (d.guard (d.primes i)) hα hβ).map
      PadicInt.toZMod

/-- The literal pD quotient has two factors at a retained prime. -/
def pairedQuotientEquiv (i : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i))) :
    (domain S d ⧸ Ideal.span {((d.primes i).val : domain S d)}) ≃+*
      ZMod (d.primes i).val × ZMod (d.primes i).val :=
  (Ideal.quotEquivOfEq (pairResidue_ker S d i).symm).trans
    (RingHom.quotientKerEquivOfSurjective (pairResidue_surjective S d i hα hβ))

/-- The literal pD quotient has only its guard factor at an omitted prime. -/
def unpairedQuotientEquiv (p : PrimeIndex) (hp : p ∉ Set.range d.primes) :
    (domain S d ⧸ Ideal.span {(p.val : domain S d)}) ≃+* ZMod p.val :=
  (Ideal.quotEquivOfEq (guardResidue_ker_unpaired S d p hp).symm).trans
    (RingHom.quotientKerEquivOfSurjective (guardResidue_surjective S d p))

theorem no_index_prime_subring_unpaired (p : PrimeIndex) (hp : p ∉ Set.range d.primes) :
    ¬ ∃ T : Subring (domain S d), T.toAddSubgroup.index = p.val :=
  PrimeIndexSignature.not_hasIndexSubring_of_single_residue p.val p.property
    (guardResidue S d p) (guardResidue_ker_unpaired S d p hp)

theorem index_integerOrder_paired (i : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i))) :
    (PaperTargets.integerOrder (domain S d) (d.primes i).val).toAddSubgroup.index =
      (d.primes i).val :=
  FiniteOrders.index_integerOrder _ (pairResidue S d i)
    (pairResidue_surjective S d i hα hβ) (pairResidue_ker S d i)

theorem primary_not_isUnit (hfirst : ¬ IsUnit (d.primary 0)) (i : ℕ) :
    ¬ IsUnit (d.primary i) := by
  by_cases hi : i = 0
  · subst i
    exact hfirst
  · exact PairedResidues.not_isUnit_of_valuation_pos _
      (by rw [d.primary_late i (Nat.pos_of_ne_zero hi)]; decide)

/-- Abstract additive prime indices recover exactly the retained prime set. -/
theorem retained_iff_exists_index_prime_subring
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ i, IsUnit (d.guard (d.primes i)))
    (p : PrimeIndex) :
    p ∈ Set.range d.primes ↔ ∃ T : Subring (domain S d), T.toAddSubgroup.index = p.val := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨PaperTargets.integerOrder (domain S d) (d.primes i).val,
      index_integerOrder_paired S d i (primary_not_isUnit d hfirst i) (hguard i)⟩
  · intro h
    by_contra hp
    exact no_index_prime_subring_unpaired S d p hp h

/-- At a retained prime the index-p order is uniquely Z+pD. -/
theorem index_prime_subring_eq_integerOrder (i : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i)))
    (T : Subring (domain S d)) (hT : T.toAddSubgroup.index = (d.primes i).val) :
    T = PaperTargets.integerOrder (domain S d) (d.primes i).val :=
  FiniteOrders.finite_index_subring_eq_integerOrder _ (d.primes i).property.pos
    (pairResidue S d i) (pairResidue_surjective S d i hα hβ) (pairResidue_ker S d i) T hT

theorem conductor_integerOrder_paired (i : ℕ)
    (hα : ¬ IsUnit (d.primary i)) (hβ : IsUnit (d.guard (d.primes i))) :
    RadicalConductor.conductorIdeal (PaperTargets.integerOrder (domain S d) (d.primes i).val) =
      Ideal.span {((d.primes i).val : domain S d)} :=
  FiniteOrders.conductor_integerOrder _ (pairResidue S d i)
    (pairResidue_surjective S d i hα hβ) (pairResidue_ker S d i)

/-- For the actual infinite-set enumeration, the recovered set is the given S. -/
theorem selected_iff_exists_index_prime_subring
    (selected : Set PrimeIndex) (hselected : selected.Infinite)
    (guard : ∀ p : PrimeIndex, ℤ_[p.val])
    (htrans : ∀ p, Transcendental ℚ (guard p).val)
    (hunit : ∀ p ∈ selected, IsUnit (guard p)) (p : PrimeIndex) :
    p ∈ selected ↔ ∃ T : Subring (domain S (ofSelected selected hselected guard htrans)),
      T.toAddSubgroup.index = p.val := by
  let d' := ofSelected selected hselected guard htrans
  have hfirst : ¬ IsUnit (d'.primary 0) :=
    PairedResidues.not_isUnit_of_valuation_pos _
      (by rw [ofSelected_primary_zero]; decide)
  have hguard (i : ℕ) : IsUnit (d'.guard (d'.primes i)) := by
    apply hunit
    rw [← ofSelected_range selected hselected guard htrans]
    exact ⟨i, rfl⟩
  simpa only [d', ofSelected_range] using
    retained_iff_exists_index_prime_subring S d' hfirst hguard p

/-- The intrinsic prime-index signature of the literal sparse intersection. -/
theorem signature_eq_range
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ i, IsUnit (d.guard (d.primes i))) :
    PrimeIndexSignature.signature (domain S d) = Set.range d.primes := by
  ext p
  exact (retained_iff_exists_index_prime_subring S d hfirst hguard p).symm

/-- The prescribed infinite set is recovered from the actual ring. -/
theorem signature_eq_selected
    (selected : Set PrimeIndex) (hselected : selected.Infinite)
    (guard : ∀ p : PrimeIndex, ℤ_[p.val])
    (htrans : ∀ p, Transcendental ℚ (guard p).val)
    (hunit : ∀ p ∈ selected, IsUnit (guard p)) :
    PrimeIndexSignature.signature (domain S (ofSelected selected hselected guard htrans)) = selected := by
  ext p
  exact (selected_iff_exists_index_prime_subring S selected hselected guard htrans hunit p).symm

end UnconditionalCounterexample.SparseResidues
