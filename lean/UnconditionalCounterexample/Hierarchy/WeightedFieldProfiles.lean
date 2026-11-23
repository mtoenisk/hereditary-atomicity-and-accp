import UnconditionalCounterexample.Hierarchy.WeightedDomainBase
import UnconditionalCounterexample.Hierarchy.PoleUnits
import UnconditionalCounterexample.PrimaryStabilization

/-! # Finitely supported integral-weight profiles of rational functions

The finite certificates for monic irreducible polynomials extend to all
nonzero elements of the rational function field. The resulting profile
records the order at every point, including the unmarked points.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted
open Polynomial GuardSupport Filter Topology DiscreteOrders PrincipalProfiles

variable (P : ℕ → FiberPlace)

/-- The two outputs of the freezing schedule for each monic irreducible. -/
def Certified (f : MonicIrreducible ℚ) : Prop :=
  (∃ N, ∀ n ≥ N, ∀ x, (P n).polynomialOrder f.val x = 0) ∧
  ∃ d : ℕ →₀ ℤ, (∀ n, d n = (P n).polynomialOrder f.val (mark false) -
      (P n).polynomialOrder f.val (mark true)) ∧ ∃ z : ℤ, totalWeight d = z

def HasIntegralProfile (f : RatFunc ℚ) : Prop :=
  ∃ g : Profile, (∀ n x, g n x = order (valuation P (.inl (n,x))) f) ∧
    ∃ z : ℤ, profileWeight g = z

private def localOrder (p : FiberPlace) (f : ℚ[X]) (hf : f ≠ 0) : LocallyConstant Fiber ℤ := by
  refine ⟨p.polynomialOrder f,(IsLocallyConstant.iff_eventually_eq _).mpr ?_⟩
  intro x
  let g (y : Fiber) := aeval (p.emb y).val f
  have hg (y : Fiber) : g y ≠ 0 := mt (transcendental_iff.mp (p.transcendental y) f) hf
  have hc : Continuous g := f.continuous_aeval.comp (continuous_subtype_val.comp p.continuous)
  have h := (hc.continuousAt (x := x)).eventually (Metric.ball_mem_nhds (g x) (norm_pos_iff.mpr (hg x)))
  filter_upwards [h] with y hy
  have he : ‖g y‖ = ‖g x‖ := Padic.norm_eq_of_norm_sub_lt_right
    (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hy)
  apply FiberPlace.order_of_norm
  change ‖g y‖ = ‖(p.prime.val : ℚ_[p.prime.val]) ^ (g x).valuation‖
  have hp : (p.prime.val : ℚ_[p.prime.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.prime.property.ne_zero
  rw [he,Padic.norm_eq_zpow_neg_valuation (hg x),Padic.norm_eq_zpow_neg_valuation (zpow_ne_zero _ hp),
    Padic.valuation_zpow,Padic.valuation_p,mul_one]

private def truncate (g : ℕ → LocallyConstant Fiber ℤ) (N : ℕ)
    (h : ∀ n ≥ N, g n = 0) : Profile :=
  Finsupp.onFinset (Finset.range N) g fun n hn => Finset.mem_range.mpr
    (lt_of_not_ge (fun hh => hn (h n hh)))

theorem certified_hasIntegralProfile (f : MonicIrreducible ℚ) (h : Certified P f) :
    HasIntegralProfile P (factor f) := by
  obtain ⟨⟨N,hN⟩,d,hd,z,hz⟩ := h
  let g := truncate (fun n => localOrder (P n) f.val f.property.1.ne_zero) N
    (fun n hn => LocallyConstant.ext (hN n hn))
  have hg (n x) : g n x = (P n).polynomialOrder f.val x := rfl
  refine ⟨g,fun n x => (hg n x).trans (order_polynomial P n x f.val).symm,z,?_⟩
  have he : markedDifference g = d := Finsupp.ext fun n => (hd n).symm
  exact (congrArg totalWeight he).trans hz

theorem constant_hasIntegralProfile (hinj : Function.Injective (fun n => (P n).prime)) (c : ℚ) :
    HasIntegralProfile P (RatFunc.C c) := by
  have hi : Function.Injective (fun n => (P n).prime.val) := Subtype.val_injective.comp hinj
  obtain ⟨N,hN⟩ := eventually_atTop.mp (PrimaryStabilization.eventually_padicValRat_eq_zero _ hi c)
  let g := truncate (fun n => LocallyConstant.const Fiber (padicValRat (P n).prime.val c)) N (fun n hn => by
    ext x; exact hN n hn)
  have hg (n x) : g n x = padicValRat (P n).prime.val c := rfl
  refine ⟨g,?_,0,?_⟩
  · intro n x
    rw [← RatFunc.algebraMap_C,order_polynomial]
    simp [hg,FiberPlace.polynomialOrder,Padic.valuation_ratCast]
  · have he : markedDifference g = 0 := Finsupp.ext (fun n => by
      simp only [markedDifference_apply,hg,sub_self,Finsupp.zero_apply])
    change totalWeight (markedDifference g) = _
    simp [he]

theorem HasIntegralProfile.mul {f g : RatFunc ℚ} (hf : f ≠ 0) (hg : g ≠ 0)
    (a : HasIntegralProfile P f) (b : HasIntegralProfile P g) : HasIntegralProfile P (f*g) := by
  obtain ⟨u,hu,i,hi⟩ := a
  obtain ⟨v,hv,j,hj⟩ := b
  refine ⟨u+v,fun n x => ?_,i+j,?_⟩
  · rw [order_mul _ hf hg,← hu n x,← hv n x]
    rfl
  · simp only [map_add,hi,hj,Int.cast_add]

theorem HasIntegralProfile.zpow {f : RatFunc ℚ} (a : HasIntegralProfile P f) (k : ℤ) :
    HasIntegralProfile P (f^k) := by
  obtain ⟨u,hu,i,hi⟩ := a
  refine ⟨k • u,fun n x => ?_,k*i,?_⟩
  · rw [order_zpow,← hu]
    let ev : Profile →+ ℤ := (LocallyConstant.evalRingHom (Y := ℤ) x).toAddMonoidHom.comp
      (Finsupp.applyAddHom n)
    change ev (k • u) = k * ev u
    rw [map_zsmul,zsmul_eq_mul,Int.cast_id]
  · simp only [map_zsmul,hi,zsmul_eq_mul,Int.cast_mul]

/-- A fair family of polynomial certificates controls every nonzero field element. -/
theorem field_hasIntegralProfile (hinj : Function.Injective (fun n => (P n).prime))
    (h : ∀ f, Certified P f) (x : RatFunc ℚ) (hx : x ≠ 0) : HasIntegralProfile P x := by
  classical
  obtain ⟨c,hc,e,he⟩ := exists_signed_factorization x hx
  rw [he]
  apply HasIntegralProfile.mul P ((map_ne_zero_iff _ RatFunc.C_injective).mpr hc)
    (PoleUnits.word_ne _ factor_ne_zero _) (constant_hasIntegralProfile P hinj c)
  change HasIntegralProfile P (∏ i ∈ e.support, factor i ^ e i)
  generalize e.support = s
  induction s using Finset.induction_on with
  | empty => simpa using constant_hasIntegralProfile P hinj 1
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact HasIntegralProfile.mul P (zpow_ne_zero _ (factor_ne_zero i))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => zpow_ne_zero _ (factor_ne_zero j)))
      ((certified_hasIntegralProfile P i (h i)).zpow P _) ih

section Canonical

variable (h : ∀ f, f ≠ 0 → HasIntegralProfile P f)

include h in
private theorem allProfiles (x : RatFunc ℚ) : HasIntegralProfile P x := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0,fun n y => (order_zero _).symm,0,by simp⟩
  · exact h x hx

/-- The unique finite profile of the orders of a field element on the selected fibers. -/
def fieldProfile (x : RatFunc ℚ) : Profile := (allProfiles P h x).choose

theorem fieldProfile_apply (x : RatFunc ℚ) (n : ℕ) (y : Fiber) :
    fieldProfile P h x n y = order (valuation P (.inl (n,y))) x :=
  (allProfiles P h x).choose_spec.1 n y

theorem fieldProfile_integral (x : RatFunc ℚ) : ∃ z : ℤ, profileWeight (fieldProfile P h x) = z :=
  (allProfiles P h x).choose_spec.2

theorem fieldProfile_mul (x y : RatFunc ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    fieldProfile P h (x*y) = fieldProfile P h x + fieldProfile P h y := by
  ext n a
  change fieldProfile P h (x*y) n a = fieldProfile P h x n a + fieldProfile P h y n a
  rw [fieldProfile_apply,fieldProfile_apply,fieldProfile_apply,order_mul _ hx hy]

end Canonical

end UnconditionalCounterexample.Hierarchy.Weighted
