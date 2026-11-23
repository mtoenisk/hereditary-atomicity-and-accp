import UnconditionalCounterexample.Variations.TwoChainConstruction
import UnconditionalCounterexample.Variations.UnivariatePrimaryValues
import UnconditionalCounterexample.Variations.TwoChains

/-!
# Valuations and square chains for the realized two-colour construction

Every normalized generator here is computed from the polynomial chosen at
its actual stage. The same global raw sequence gives the return elements,
which belong to the intersection ring, and the two strictly ascending chains.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open GuardSupport WithZero NormalizedWords
open Variations Univariate UnivariateConductor TwoChainSchedule
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

private theorem weight_nonnegative (k j : ℕ) (c : Bool) : 0 ≤ weight k c j := by
  obtain ⟨d, g, rfl⟩ := stage_surjective k
  cases g with
  | b n => rw [weight_b]; simp only [PrimaryWordProfiles.bWeight]; split_ifs <;> decide
  | q n => rw [weight_q]; simp only [PrimaryWordProfiles.qWeight]; split_ifs <;> decide

theorem primaryVal_generator (c : Bool) (j n : ℕ) :
    primaryVal c j (generators n) = exp (-weight n c j) := by
  let k := allocationStage c j
  let A := family.atStage k
  let ord (m birth : ℕ) := requestedOrder m birth false
  have h := family.generator_primary_norm ord (fun m t hmt => by
    simp [ord, requestedOrder, weight_zero_before_birth m t hmt])
    (fun m i hi => target_norm _ _ _ i false hi) n k
  have htarget : (ord n k : ℤ) = weight n c j := by
    simp only [ord, k, requestedOrder, Bool.false_eq_true, ite_false,
      (allocated_label c j).1, (allocated_label c j).2, Int.toNat_of_nonneg (weight_nonnegative n j c)]
  let e := EvaluationDVR.evaluationHom A.prime.val A.primary.val.val A.primary.property.1
  have he : (permanentSite requirements (family.prime k)).evaluate false (family.prime_active k) = e := by
    unfold Site.evaluate
    congr 1
    rw [family.permanent_eq]
    rfl
  rw [he] at h
  change Padic.mulValuation (e (generators n)) = _
  have hpos := (map_ne_zero_iff e e.injective).mpr ((chain requirements).generators_ne_zero n)
  rw [Padic.mulValuation_toFun, ite_eq_right hpos]
  have hv := ReturnTargets.valuation_of_target_norm (ord n k) (0 : ℚ_[A.prime.val])
    (e (generators n)) (h.trans (ReturnTargets.quotientTarget_norm _ _).symm)
  rw [hv, htarget]

theorem guardVal_generator (p : PrimeIndex) (n : ℕ) : guardVal p (generators n) = 1 := by
  apply mulValuation_eq_one_of_norm_eq_one
  apply generator_guard_norm requirements _ n p
  intro k i
  let P := (chain requirements).approx k
  let B := (selection requirements k).batch
  let sites := extend requirements P (table requirements k) B
  change ‖(targets P B sites).value i true‖ = 1
  rw [target_norm P B sites i true (Or.inl rfl)]
  simp [requestedOrder]

theorem primary_moving (c d : Bool) (n j : ℕ) :
    primaryVal d j (moving generators c n) =
      exp (-(if c = d then primaryAtomProfile n j else 0)) := by
  induction n with
  | zero => exact primary_seed c d j
  | succ n ih =>
    rw [moving, map_div₀, map_mul, ih, primaryVal_generator, primaryVal_generator,
      weight_b, weight_q]
    by_cases h : c=d
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_left h, ← exp_add, ← exp_sub,
        AtomProfiles.primary_recurrence]
      congr 1
      ring
    · simp [h]

theorem guard_moving (c : Bool) (n : ℕ) (p : PrimeIndex) :
    guardVal p (moving generators c n) = 1 := by
  induction n with
  | zero => exact guard_seed p c
  | succ n ih => rw [moving, map_div₀, map_mul, ih, guardVal_generator, guardVal_generator, mul_one, div_one]

theorem seed_mem_pole (c : Bool) : seed c ∈ poleAlgebra requirements := by
  cases c
  · exact PoleAlgebra.X_mem _
  · rw [seed, div_eq_mul_inv]
    apply (poleAlgebra requirements).mul_mem
      ((poleAlgebra requirements).sub_mem (PoleAlgebra.X_mem _) (poleAlgebra requirements).one_mem)
    simpa only [map_inv₀, map_ofNat] using (poleAlgebra requirements).algebraMap_mem ((2 : ℚ)⁻¹)

theorem moving_mem (c : Bool) (n : ℕ) : moving generators c n ∈ domain := by
  rw [domain_eq_intersection, IntersectionDomain.mem_intersection]
  constructor
  · induction n with
    | zero => exact seed_mem_pole c
    | succ n ih =>
      rw [moving, div_eq_mul_inv]
      exact (poleAlgebra requirements).mul_mem ((poleAlgebra requirements).mul_mem ih
        (AtomProfiles.generators_pole_unit raw _ _).1) (AtomProfiles.generators_pole_unit raw _ _).2
  · rintro (⟨d, j⟩ | p)
    · change primaryVal d j _ ≤ 1
      rw [primary_moving, exp_le_one_iff]
      exact neg_nonpos.mpr (by split <;> first | exact primaryAtomProfile_nonneg _ _ | rfl)
    · exact (guard_moving c n p).le

def movingElement (c : Bool) (n : ℕ) : domain := ⟨_, moving_mem c n⟩

@[simp] theorem movingElement_val (c : Bool) (n : ℕ) :
    (movingElement c n : RatFunc ℚ) = moving generators c n := rfl

theorem movingElement_ne_zero (c : Bool) (n : ℕ) : movingElement c n ≠ 0 :=
  fun h => moving_ne_zero _ (chain requirements).generators_ne_zero c n (congrArg Subtype.val h)

/-- The q ratios in the pole algebra, with their inverses from the same
normalized raw polynomials. -/
def ratioUnit (c : Bool) (n : ℕ) : (poleAlgebra requirements).toSubringˣ where
  val := ⟨generators (stage c (.q n)), (AtomProfiles.generators_pole_unit raw _ _).1⟩
  inv := ⟨(generators (stage c (.q n)))⁻¹, (AtomProfiles.generators_pole_unit raw _ _).2⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ ((chain requirements).generators_ne_zero _))
  inv_val := Subtype.ext (inv_mul_cancel₀ ((chain requirements).generators_ne_zero _))

private theorem seed_chain (c : Bool) : HasStrictChainAt ((movingElement c 0)^2) := by
  suffices ∀ (h : seed c ∈ domain), HasStrictChainAt ((⟨seed c, h⟩ : domain)^2) from
    this (moving_mem c 0)
  rw [domain_eq_intersection]
  intro hc
  apply seed_square_chain (poleAlgebra requirements).toSubring vertical ratioUnit _ _ c _ _ _
  · intro b n d i
    change primaryVal d i (generators (stage b (.q n))) = _
    rw [primaryVal_generator, weight_q]
    by_cases h : b=d
    · rw [ite_eq_left h, ite_eq_left h]
      congr 2
      unfold PrimaryWordProfiles.qWeight PaperSquareChain.qProfile
      split_ifs <;> omega
    · simp [h]
  · intro b n p
    exact guardVal_generator p _
  · exact fun h => seed_ne_zero c (congrArg Subtype.val h)
  · intro i
    change primaryVal c i (seed c) ≤ exp (-1)
    rw [primary_seed]
    simp only [eq_self, ite_true, exp_le_exp]
    unfold primaryAtomProfile
    split_ifs <;> omega

/-- The canonical coordinate of the adaptive ring. -/
abbrev parameter : domain := Univariate.coordinate requirements

/-- The two literal chains and failure of weak ACCP in the one constructed domain. -/
theorem square_chains_not_weakACCP :
    HasStrictChainAt (parameter^2) ∧ HasStrictChainAt ((1-parameter)^2) ∧
      IsCoprime (parameter^2) ((1-parameter)^2) ∧ ¬ Factorization.IsWeakACCP domain := by
  have h₀ : HasStrictChainAt (parameter^2) := seed_chain false
  have h₁ := chainAt_mul (seed_chain true) (show (4 : domain) ≠ 0 by norm_num)
  have heq : (1-parameter)^2 = 4*(movingElement true 0)^2 := by
    apply Subtype.ext
    change (1-RatFunc.X)^2 = 4*((RatFunc.X-1)/2 : RatFunc ℚ)^2
    ring
  rw [← heq] at h₁
  exact ⟨h₀, h₁, squares_isCoprime parameter,
    Factorization.not_isWeakACCP_of_isCoprime_of_strictChains (squares_isCoprime parameter) h₀ h₁⟩

end UnconditionalCounterexample.TwoChains
