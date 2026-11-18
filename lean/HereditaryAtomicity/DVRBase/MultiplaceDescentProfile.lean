import HereditaryAtomicity.DVRBase.MultiplaceDescentSingleton
import HereditaryAtomicity.DVRBase.MultiplaceDescentNormalization

/-! Actual source class profiles for support descent. -/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped nonZeroDivisors BigOperators

/-- Reversing the endpoint profile and adding a fixed vector preserves the
exact joint finite-fiber condition. -/
theorem jointFiniteFibers_const_sub
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (c : ι → G) (hθ : JointFiniteFibers θ) :
    JointFiniteFibers (fun n i => c i - θ n i) := by
  intro η hη g
  apply (hθ η hη ((∑ i, η i • c i) - g)).subset
  intro n hn
  change ∑ i, η i • θ n i = (∑ i, η i • c i) - g
  simp only [smul_sub, Finset.sum_sub_distrib] at hn
  have he := sub_sub_cancel (∑ i, η i • c i) (∑ i, η i • θ n i)
  rw [hn] at he
  exact he.symm

theorem jointFiniteFibers_const_sub_iff
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (θ : ℕ → ι → G) (c : ι → G) :
    JointFiniteFibers (fun n i => c i - θ n i) ↔ JointFiniteFibers θ := by
  refine ⟨fun h => ?_, jointFiniteFibers_const_sub θ c⟩
  simpa only [sub_sub_cancel] using jointFiniteFibers_const_sub (fun n i => c i - θ n i) c h

variable {R : Type*} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R]

/-- Actual endpoint classes in additive notation; no abstract profile is supplied. -/
def componentEndpointProfile (S : Finset (MaximalSpectrum R)) (π : S → R)
    (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (x : ℕ → R) (hx : ∀ n, x n ≠ 0) (n : ℕ) (P : S) : Additive (ClassGroup R) :=
  Additive.ofMul (componentClassHom (hU P) ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩)

/-- The prefix profile is the class of x₀/xₙ at each actual centre. -/
def componentPrefixProfile (S : Finset (MaximalSpectrum R)) (π : S → R)
    (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (x : ℕ → R) (hx : ∀ n, x n ≠ 0) (n : ℕ) (P : S) : Additive (ClassGroup R) :=
  componentEndpointProfile S π hU x hx 0 P - componentEndpointProfile S π hU x hx n P

/-- Source support of the top proves the total endpoint-class cancellation
at every level, via the actual product of singleton component ideals. -/
theorem sum_componentEndpointProfile_eq_zero
    (S : Finset (MaximalSpectrum R)) (π : S → R)
    (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupp : ∀ P : MaximalSpectrum R, x 0 ∈ P.asIdeal → P ∈ S) (n : ℕ) :
    ∑ P : S, componentEndpointProfile S π hU x hx n P = 0 := by
  change Additive.ofMul (∏ P : S, componentClassHom (hU P)
    ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩) = 0
  rw [prod_singleton_componentClassHom S π hU _ (fun P hP =>
    hsupp P (P.asIdeal.mem_of_dvd (sourceChain_endpoint_dvd_top x t hxt n) hP))]
  rfl

/-- The same exact joint finite-fibre condition may be tested on endpoint or quotient classes. -/
theorem jointFiniteFibers_componentPrefixProfile_iff
    (S : Finset (MaximalSpectrum R)) (π : S → R)
    (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (x : ℕ → R) (hx : ∀ n, x n ≠ 0) :
    JointFiniteFibers (componentPrefixProfile S π hU x hx) ↔
      JointFiniteFibers (componentEndpointProfile S π hU x hx) :=
  jointFiniteFibers_const_sub_iff _ _

/-- The profile is exactly the actual integral prefix product class. -/
theorem componentPrefixProfile_eq_prefix
    (S : Finset (MaximalSpectrum R)) (π : S → R)
    (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (ht : ∀ n, t n ≠ 0)
    (hxt : ∀ n, x n = x (n + 1) * t n) (n : ℕ) (P : S) :
    componentPrefixProfile S π hU x hx n P = Additive.ofMul (componentClassHom (hU P)
      ⟨∏ j ∈ Finset.range n, t j,
        mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => ht j))⟩) := by
  let q : R⁰ := ⟨∏ j ∈ Finset.range n, t j,
    mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => ht j))⟩
  have he : (⟨x 0, mem_nonZeroDivisors_of_ne_zero (hx 0)⟩ : R⁰) =
      ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩ * q :=
    Subtype.ext (sourceChain_prefix_product x t hxt n)
  change componentClassHom (hU P) ⟨x 0, _⟩ /
    componentClassHom (hU P) ⟨x n, _⟩ = componentClassHom (hU P) q
  rw [he, map_mul, mul_div_cancel_left]

/-- Only the ratio supports, not the endpoint supports, are needed for total
prefix-class cancellation. This is the invariant preserved by component descent. -/
theorem sum_componentPrefixProfile_eq_zero
    (S : Finset (MaximalSpectrum R)) (π : S → R)
    (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hsupp : ∀ n (P : MaximalSpectrum R), t n ∈ P.asIdeal → P ∈ S) (n : ℕ) :
    ∑ P : S, componentPrefixProfile S π hU x hx n P = 0 := by
  have ht (j : ℕ) : t j ≠ 0 := fun hz => hx j (by rw [hxt j, hz, mul_zero])
  simp_rw [componentPrefixProfile_eq_prefix S π hU x t hx ht hxt]
  change Additive.ofMul (∏ P : S, componentClassHom (hU P)
    ⟨∏ j ∈ Finset.range n, t j, _⟩) = 0
  rw [prod_singleton_componentClassHom S π hU _ (fun P hP => ?_)]
  · rfl
  · change (∏ j ∈ Finset.range n, t j) ∈ P.asIdeal at hP
    obtain ⟨j, _, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hP
    exact hsupp j P hj

/-- The actual singleton form of support descent: failure of the original quotient-class
joint finite-fibre condition constructs a strict source chain on fewer recurrent centres.
The prefix cancellation uses only source ratio support and is therefore
preserved at the next descent step. -/
theorem exists_proper_recurrent_chain_of_not_jointFiniteFibers
    (S : Finset (MaximalSpectrum R)) (π : S → R)
    (hU : ∀ P : S, IsClopenInFiber (π P) {P.val})
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hfinite : Set.Finite {P : MaximalSpectrum R | x 0 ∈ P.asIdeal})
    (hrecur : ∀ P : S, Set.Infinite {n | t n ∈ P.val.asIdeal})
    (hsupp : ∀ n (P : MaximalSpectrum R), t n ∈ P.asIdeal → P ∈ S)
    (hfailure : ¬ JointFiniteFibers (componentPrefixProfile S π hU x hx)) :
    ∃ (S' : Finset (MaximalSpectrum R)) (n₀ E : ℕ) (c a : ℕ → R),
      S'.Nonempty ∧ S' ⊂ S ∧ 0 < E ∧ (∀ n, c n ≠ 0) ∧ c 0 = x n₀ ^ E ∧
      (∀ n, c n = c (n + 1) * a n) ∧ (∀ n, ¬ IsUnit (a n)) ∧
      Set.Finite {P : MaximalSpectrum R | c 0 ∈ P.asIdeal} ∧
      (∀ n (P : MaximalSpectrum R), a n ∈ P.asIdeal ↔ P ∈ S') ∧
      ∀ P : MaximalSpectrum R, Set.Infinite {n | a n ∈ P.asIdeal} ↔ P ∈ S' := by
  classical
  have hnc : ∃ η : S → ℤ, JointNonconstant η := by
    by_contra hn
    apply hfailure
    intro η hη
    exact False.elim (hn ⟨η, hη⟩)
  obtain ⟨η, i, j, hij⟩ := hnc
  let : Nonempty S := ⟨i⟩
  obtain ⟨e, γ, hezero, hepos, hγ⟩ :=
    exists_nat_weights_infinite_fiber_of_not_jointFiniteFibers
      (componentPrefixProfile S π hU x hx)
      (sum_componentPrefixProfile_eq_zero S π hU x t hx hxt hsupp) hfailure
  let δ : Additive (ClassGroup R) :=
    (∑ P : S, e P • componentEndpointProfile S π hU x hx 0 P) - γ
  have hδ : Set.Infinite {n | (∏ P : S, componentClassHom (hU P)
      ⟨x n, mem_nonZeroDivisors_of_ne_zero (hx n)⟩ ^ e P) = Additive.toMul δ} := by
    apply hγ.mono
    intro n hn
    change (∑ P : S, e P • componentEndpointProfile S π hU x hx n P) = δ
    change (∑ P : S, e P • (componentEndpointProfile S π hU x hx 0 P -
      componentEndpointProfile S π hU x hx n P)) = γ at hn
    simp only [smul_sub, Finset.sum_sub_distrib] at hn
    have he := sub_sub_cancel (∑ P : S, e P • componentEndpointProfile S π hU x hx 0 P)
      (∑ P : S, e P • componentEndpointProfile S π hU x hx n P)
    rw [hn] at he
    exact he.symm
  obtain ⟨S', n₀, c, a, hS'ne, hS'sub, hc, hc0, hca, hna, hcf, hsa, hrec⟩ :=
    exists_proper_recurrent_chain_of_weighted_component_fiber S π hU x t hx hxt
      hfinite hrecur e hezero hepos (Additive.toMul δ) hδ
  refine ⟨S', n₀, ∑ P, e P, c, a, hS'ne, hS'sub, ?_, hc, hc0, hca, hna, hcf, hsa, hrec⟩
  obtain ⟨P, hP⟩ := hepos
  exact hP.trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ P))

end HereditaryAtomicity.DVRBase
