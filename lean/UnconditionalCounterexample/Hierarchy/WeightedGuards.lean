import UnconditionalCounterexample.Hierarchy.WeightedDomainBase
import UnconditionalCounterexample.IntersectionDomain

/-! # Independent guard corrections and integer clearing

Complementary guard primes have no selected fibre. Their prime powers can
correct all guard orders of a pole unit without altering its selected orders.
On the selected side only finitely many fibres have a nonzero profile, and
each locally constant integer profile on the compact Cantor space has finite
range. These bounds give one integer clearing the entire vertical family.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted

open GuardSupport DiscreteOrders Polynomial IntersectionDomain WithZero

variable (P : ℕ → FiberPlace)

private theorem finite_guard_support (f : RatFunc ℚ) :
    (Function.support (fun q : Guard P => order (valuation P (.inr q)) f)).Finite := by
  by_cases hf : f = 0
  · simp [hf,Function.support]
  · apply ((PaperConstruction.guardSupport f hf).preimage Subtype.val_injective.injOn).subset
    intro q h
    change order (Prescribed.guardVal q.val) f ≠ 0 at h
    exact fun he => h ((order_eq_zero_iff _ hf).mpr he)

/-- The finitely supported integer orders at the complementary primes. -/
def guardProfile (f : RatFunc ℚ) : (Guard P) →₀ ℤ :=
  Finsupp.ofSupportFinite _ (finite_guard_support P f)

@[simp] theorem guardProfile_apply (f : RatFunc ℚ) (q : Guard P) :
    guardProfile P f q = order (valuation P (.inr q)) f := rfl

/-- Prescribe arbitrary finitely supported orders at complementary primes
and order zero simultaneously at every point of every selected fibre. -/
theorem exists_guard_scalar (k : (Guard P) →₀ ℤ) :
    ∃ c : ℚ, c ≠ 0 ∧
      (∀ n x, order (valuation P (.inl (n,x))) (RatFunc.C c) = 0) ∧
      ∀ q : Guard P, order (valuation P (.inr q)) (RatFunc.C c) = k q := by
  classical
  let primes := k.support.image Subtype.val
  let w (p : PrimeIndex) : ℤ := if h : p ∉ Set.range (fun n => (P n).prime) then k ⟨p,h⟩ else 0
  obtain ⟨c,hc,h⟩ := Prescribed.exists_scalar_orders primes w
  refine ⟨c,hc,?_,?_⟩
  · intro n x
    have hp : (P n).prime ∉ primes := by
      rintro hp
      obtain ⟨q,_,he⟩ := Finset.mem_image.mp hp
      exact q.property ⟨n,he.symm⟩
    exact (h _ (EvaluationDVR.evaluationHom _ _ ((P n).transcendental x))).trans (ite_eq_right hp)
  · intro q
    have he := h q.val (guardEvaluation PaperConstruction.places.guard PaperConstruction.places.guard_trans q.val)
    change order (valuation P (.inr q)) (RatFunc.C c) = _ at he
    rw [he]
    by_cases hq : q ∈ k.support
    · rw [ite_eq_left (Finset.mem_image_of_mem _ hq)]
      exact dite_eq_left q.property
    · have hp : q.val ∉ primes := fun h => by
        obtain ⟨r,hr,he⟩ := Finset.mem_image.mp h
        exact hq ((Subtype.ext he : r = q) ▸ hr)
      rw [ite_eq_right hp,Finsupp.notMem_support_iff.mp hq]

/-- Every previously realized selected profile can be realized by a pole unit
having any independently specified finite guard profile. -/
theorem adjust_guard_orders (S : Set ℚ[X]) (u : (PoleAlgebra.generated S)ˣ) (k : Guard P →₀ ℤ) :
    ∃ v : (PoleAlgebra.generated S)ˣ,
      (∀ n x, order (valuation P (.inl (n,x))) ((v : PoleAlgebra.generated S) : RatFunc ℚ) =
        order (valuation P (.inl (n,x))) ((u : PoleAlgebra.generated S) : RatFunc ℚ)) ∧
      ∀ q : Guard P, order (valuation P (.inr q)) ((v : PoleAlgebra.generated S) : RatFunc ℚ) = k q := by
  let f : RatFunc ℚ := (u : PoleAlgebra.generated S)
  have hf : f ≠ 0 := fun hz => u.ne_zero (Subtype.ext hz)
  obtain ⟨c,hc,hsel,hguard⟩ := exists_guard_scalar P (k - guardProfile P f)
  let d := Units.map (algebraMap ℚ (PoleAlgebra.generated S)).toMonoidHom (Units.mk0 c hc)
  have hc' : RatFunc.C c ≠ 0 := (_root_.map_ne_zero RatFunc.C).mpr hc
  have hd : (((d * u : (PoleAlgebra.generated S)ˣ) : PoleAlgebra.generated S) : RatFunc ℚ) = RatFunc.C c * f := rfl
  refine ⟨d*u,fun n x => ?_,fun q => ?_⟩
  · rw [hd,order_mul _ hc' hf,hsel,zero_add]
  · rw [hd,order_mul _ hc' hf,hguard,Finsupp.sub_apply,guardProfile_apply,sub_add_cancel]

private theorem clear_of_dvd (v : Valuation (RatFunc ℚ) ℤᵐ⁰) (f : RatFunc ℚ) {a m : ℕ}
    (ha : a ∣ m) (h : v ((a : RatFunc ℚ)*f) ≤ 1) : v ((m : RatFunc ℚ)*f) ≤ 1 := by
  obtain ⟨b,rfl⟩ := ha
  rw [Nat.cast_mul,mul_right_comm,map_mul]
  exact (mul_le_mul' h (valuation_natCast_le_one _ b)).trans_eq (one_mul _)

/-- A finite profile of locally constant functions on the selected fibres is
enough to clear a rational function at all selected and complementary places. -/
theorem clear_of_profile (f : RatFunc ℚ) (hf : f ≠ 0) (g : Profile)
    (hg : ∀ n x, order (valuation P (.inl (n,x))) f = g n x) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, valuation P i ((m : RatFunc ℚ) * f) ≤ 1 := by
  classical
  let bound (n : ℕ) := (g n).range_finite.toFinset.sup (fun z : ℤ => (-z).toNat)
  have lower (n : ℕ) (x : Fiber) : -(bound n : ℤ) ≤ g n x := by
    have h := Finset.le_sup (f := fun z : ℤ => (-z).toNat)
      ((g n).range_finite.mem_toFinset.mpr (Set.mem_range_self x))
    change (-(g n x)).toNat ≤ bound n at h
    omega
  let factor (n : ℕ) := (P n).prime.val ^ bound n
  let a := ∏ n ∈ g.support, factor n
  have ha : 0 < a := Finset.prod_pos fun n _ => pow_pos (P n).prime.property.pos _
  have hsel (n : ℕ) (x : Fiber) : valuation P (.inl (n,x)) ((a : RatFunc ℚ) * f) ≤ 1 := by
    let v := valuation P (.inl (n,x))
    by_cases h : n ∈ g.support
    · apply clear_of_dvd v f (Finset.dvd_prod_of_mem factor h)
      have hp : v ((P n).prime.val : RatFunc ℚ) = exp (-1) := by
        rw [value_eq_exp_neg_order _ (Nat.cast_ne_zero.mpr (P n).prime.property.ne_zero),order_prime]
        simp only [placePrime,ite_true]
      rw [show factor n = (P n).prime.val ^ bound n from rfl,Nat.cast_pow,map_mul,map_pow,hp,
        value_eq_exp_neg_order v hf,← exp_nsmul,← exp_add,exp_le_one_iff,hg]
      simp only [nsmul_eq_mul,mul_neg,mul_one]
      linarith [lower n x]
    · have hzero : g n x = 0 := by rw [Finsupp.notMem_support_iff.mp h]; rfl
      have hu := (order_eq_zero_iff v hf).mp ((hg n x).trans hzero)
      rw [map_mul,hu,mul_one]
      exact valuation_natCast_le_one _ _
  have hbad : {p : Guard P | 1 < valuation P (.inr p) f}.Finite := by
    apply ((PaperConstruction.guardSupport f hf).preimage Subtype.val_injective.injOn).subset
    exact fun p hp => ne_of_gt hp
  obtain ⟨b,hb,hguard⟩ := exists_nat_mul_integral_of_finite (fun p : Guard P => valuation P (.inr p)) f hbad
    (fun p => exists_nat_mul_integral _ p.val.val p.val.property.pos (EvaluationDVR.valuation_prime _ _) f)
  refine ⟨a*b,Nat.mul_pos ha hb,?_⟩
  rintro (⟨n,x⟩ | p)
  · exact clear_of_dvd _ _ (dvd_mul_right a b) (hsel n x)
  · exact clear_of_dvd _ _ (dvd_mul_left b a) (hguard p)

end UnconditionalCounterexample.Hierarchy.Weighted
