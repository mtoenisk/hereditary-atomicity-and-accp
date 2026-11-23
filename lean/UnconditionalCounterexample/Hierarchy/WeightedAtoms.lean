import UnconditionalCounterexample.Hierarchy.WeightedAtomCriteria
import UnconditionalCounterexample.Hierarchy.WeightedFiber

/-! # The weight obstruction on the intersection with the selected evaluation rings -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open IntersectionDomain DiscreteOrders WithZero Factorization TopologicalSpace

variable {K G : Type*} [Field K] (B : Subring K)
    (v : ((ℕ × Fiber) ⊕ G) → Valuation K ℤᵐ⁰)

local notation "R" => intersection B v

/-- Realization of a single nonnegative clopen patch, with all guard orders zero.
The generator is an actual element of the intersection and a unit in the pole algebra. -/
def RealizesPatch (n : ℕ) (C : Clopens Fiber) (s : ℤ) : Prop :=
  ∃ u : R, IsUnit (inclusion B v u) ∧
    (∀ k y, order (v (.inl (k,y))) (u : K) = if k = n then patch C s y else 0) ∧
    ∀ j, order (v (.inr j)) (u : K) = 0

/-- An atom has order at most one at every point of every selected fiber. -/
theorem atom_order_le_one
    (hpatch : ∀ n C, mark false ∉ C → mark true ∉ C → RealizesPatch B v n C 2)
    (x : R) (hx : Irreducible x) (n : ℕ) (f : LocallyConstant Fiber ℤ)
    (hf : ∀ y, f y = order (v (.inl (n,y))) (x : K)) (y : Fiber) :
    f y ≤ 1 := by
  classical
  by_contra! h
  obtain ⟨C, ⟨z,hz⟩, hy, h₀, h₁, hc⟩ := exists_unmarked_patch f y
  change z ∈ C at hz
  obtain ⟨u,hu,hs,hg⟩ := hpatch n C h₀ h₁
  refine not_irreducible_of_split B v x u hx.ne_zero hu ?_ ?_ ?_ hx
  · rintro (⟨k,w⟩ | j)
    · rw [hs]
      by_cases hk : k = n
      · subst k
        simp only [↓reduceIte, ← hf, patch_apply]
        split_ifs with hw
        · rw [hc w hw]
          omega
        · rw [hf]
          exact order_nonneg_on_ring B v x _
      · simp only [hk, ↓reduceIte]
        exact order_nonneg_on_ring B v x _
    · rw [hg]
      exact order_nonneg_on_ring B v x _
  · exact ⟨.inl (n,z), by simp [hs, hz]⟩
  · exact ⟨.inl (n,y), by simpa [hs, hy, ← hf y] using (show (0:ℤ) < f y by omega)⟩

/-- The actual contraction of a pole unit with given nonnegative orders. -/
theorem realizesPatch_of_unit (n : ℕ) (C : Clopens Fiber) (s : ℤ) (hs : 0 ≤ s)
    (u : Bˣ) (hp : ∀ k y, order (v (.inl (k,y))) (u.val : K) = if k = n then patch C s y else 0)
    (hg : ∀ j, order (v (.inr j)) (u.val : K) = 0) : RealizesPatch B v n C s := by
  classical
  have hu0 : (u.val : K) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hu : (u.val : K) ∈ R := by
    apply (mem_intersection _ _ _).mpr
    refine ⟨u.val.property, fun i => (order_nonneg_iff _ hu0).mp ?_⟩
    rcases i with ⟨k,y⟩ | j
    · rw [hp]
      simp only [patch_apply]
      split_ifs <;> omega
    · rw [hg]
  exact ⟨⟨u.val,hu⟩,u.isUnit,hp,hg⟩

/-- The first coordinate separates the two constant streams. -/
def firstPatch : Clopens Fiber :=
  ⟨{y | y 0 = false}, (isClopen_discrete ({false} : Set Bool)).preimage (continuous_apply 0)⟩

@[simp] theorem markFalse_mem_firstPatch : mark false ∈ firstPatch := rfl
@[simp] theorem markTrue_not_mem_firstPatch : mark true ∉ firstPatch := Bool.noConfusion

/-- An integral marked weight vanishes on atoms because both marked orders lie in {0,1}. -/
theorem atom_profileWeight_zero
    (hpatch : ∀ n C, mark false ∉ C → mark true ∉ C → RealizesPatch B v n C 2)
    (x : R) (hx : Irreducible x) (g : Profile)
    (hg : ∀ n y, g n y = order (v (.inl (n,y))) (x : K))
    (hint : ∃ z : ℤ, profileWeight g = z) : profileWeight g = 0 := by
  apply totalWeight_eq_zero_of_integral _ _ hint
  intro n
  rw [markedDifference_apply]
  have h₀ := atom_order_le_one B v hpatch x hx n (g n) (hg n) (mark false)
  have h₁ := atom_order_le_one B v hpatch x hx n (g n) (hg n) (mark true)
  have hl₀ := order_nonneg_on_ring B v x (.inl (n,mark false))
  have hl₁ := order_nonneg_on_ring B v x (.inl (n,mark true))
  rw [← hg] at hl₀ hl₁
  omega

/-- The first height-eight patch has weight one and divides the eighth power
of the rational prime beneath its fiber. -/
theorem exists_weightOne_dvd_eighth (q : R) (hq : q ≠ 0)
    (hqS : ∀ k y, order (v (.inl (k,y))) (q : K) = if k = 0 then 1 else 0)
    (hqG : ∀ j, order (v (.inr j)) (q : K) = 0)
    (hr : RealizesPatch B v 0 firstPatch 8) :
    ∃ b : R, b ≠ 0 ∧ b ∣ q^8 ∧
      (∀ n y, order (v (.inl (n,y))) (b : K) =
        (Finsupp.single 0 (patch firstPatch 8) : Profile) n y) ∧
      profileWeight (Finsupp.single 0 (patch firstPatch 8)) = 1 := by
  classical
  obtain ⟨b,hb,hs,hg⟩ := hr
  have h₀ : b ≠ 0 := fun h => hb.ne_zero (by rw [h,map_zero])
  refine ⟨b,h₀,poleUnit_dvd_of_order_le B v b _ hb (pow_ne_zero _ hq) ?_,?_,?_⟩
  · intro i
    have he : order (v i) ((q^8 : R) : K) = 8 * order (v i) (q : K) := by
      simpa using order_zpow (v i) (q : K) (8 : ℤ)
    rw [he]
    rcases i with ⟨k,y⟩ | j
    · rw [hs, hqS, patch_apply]
      split_ifs <;> norm_num
    · simp [hg, hqG]
  · intro n y
    by_cases hn : n = 0
    · subst n
      simp [hs]
    · simp [hs, hn]
  · norm_num [profileWeight_single_patch,weight]

/-- A nonzero value of an additive weight vanishing on atoms obstructs every
atomic multiplier on that element. -/
theorem not_almostAtomic_of_weight {S : Type*} [CommRing S] [IsDomain S] (W : S → ℚ)
    (hunit : ∀ x, IsUnit x → W x = 0)
    (hmul : ∀ a b, a ≠ 0 → b ≠ 0 → W (a*b) = W a + W b)
    (hatom : ∀ x, Irreducible x → W x = 0)
    (b : S) (hb : b ≠ 0) (hw : W b ≠ 0) : ¬ IsAlmostAtomicDomain S := by
  intro ha
  obtain ⟨a, hA, hAb⟩ := ha b hb
  have hz := weight_eq_zero_of_atomic W hunit hmul hatom (mul_ne_zero hA.ne_zero hb) hAb
  rw [hmul _ _ hA.ne_zero hb, weight_eq_zero_of_atomic W hunit hmul hatom hA.ne_zero hA,
    zero_add] at hz
  exact hw hz

end UnconditionalCounterexample.Hierarchy.Weighted
