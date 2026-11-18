import UnconditionalCounterexample.SparseProfileData
import UnconditionalCounterexample.PrincipalProfileImage
import UnconditionalCounterexample.PrimaryProfileQuotient
import UnconditionalCounterexample.ProfileElimination

/-! The actual principal profile image for any realized sparse construction.
Only the elementary raw-polynomial and evaluation data in SparseProfileData
are inputs. The existing finite primary quotient and triangular elimination
are reused unchanged; no surjectivity of the primary prime enumeration occurs.
The mixed construction must separately instantiate the data for a given
infinite selected prime set. -/

noncomputable section
namespace UnconditionalCounterexample.SparsePrincipalProfiles
open Polynomial PicardProfiles SparseProfiles DiscreteOrders NormalizedWords

variable (A : SparseProfileData.Data)

/-- The actual additive valuation coordinates of a nonzero rational function. -/
def fractionCoordinates : Additive (RatFunc ℚ)ˣ →+ (ProfilePlace A.Outside → ℤ) where
  toFun u p := order (valuations A.poles A.places p) (u.toMul : RatFunc ℚ)
  map_zero' := by
    funext p
    exact order_one _
  map_add' u v := by
    funext p
    exact order_mul _ u.toMul.ne_zero v.toMul.ne_zero

theorem fractionCoordinates_restricted (u : Additive (RatFunc ℚ)ˣ) :
    Restricted (fractionCoordinates A u) := by
  exact ⟨eventually_primary A.poles A.places _ u.toMul.ne_zero,
    finite_outside A.poles A.places A.guardSupport _ u.toMul.ne_zero⟩

/-- The actual principal profile homomorphism; no ideal or class is chosen here. -/
def profile : Additive (RatFunc ℚ)ˣ →+ A.Group where
  toFun u := ofCoordinates (fractionCoordinates A u) (fractionCoordinates_restricted A u)
  map_zero' := by
    apply coordinate_injective
    rw [coordinate_ofCoordinates, map_zero, map_zero]
  map_add' u v := by
    apply coordinate_injective
    rw [coordinate_ofCoordinates, map_add, map_add, coordinate_ofCoordinates, coordinate_ofCoordinates]

@[simp] theorem coordinate_profile (u : Additive (RatFunc ℚ)ˣ) (p : ProfilePlace A.Outside) :
    coordinate (profile A u) p = order (valuations A.poles A.places p) (u.toMul : RatFunc ℚ) := by
  exact congrFun (coordinate_ofCoordinates (fractionCoordinates A u) (fractionCoordinates_restricted A u)) p

/-- Exactly the profiles of actual nonzero principal fractional ideals. -/
def principals : AddSubgroup A.Group := (profile A).range

theorem mem_principals_iff (x : A.Group) :
    x ∈ principals A ↔ ∃ u : (RatFunc ℚ)ˣ, profile A (Additive.ofMul u) = x := Iff.rfl

/-- A pure primary actual principal relation has the exact finite b/q signed representation. -/
theorem primary_relation_forward (a : ℕ →₀ ℤ) (ha : primary a ∈ principals A) :
    ∃ s u : ℕ →₀ ℤ, Represents s u a := by
  obtain ⟨u, hu⟩ := (mem_principals_iff A _).mp ha
  have hc (p : ProfilePlace A.Outside) :
      order (valuations A.poles A.places p) (u : RatFunc ℚ) = coordinate (primary a) p := by
    exact (coordinate_profile A (Additive.ofMul u) p).symm.trans
      (congrArg (fun x => coordinate x p) hu)
  have hE : order (valuations A.poles A.places .limit) (u : RatFunc ℚ) = 0 := hc .limit
  have ho (i : A.Outside) : order (valuations A.poles A.places (.outside i)) (u : RatFunc ℚ) = 0 := hc (.outside i)
  obtain ⟨e, _, he⟩ := exists_signed_word A.raw A.monic_irreducible A.raw_injective A.exponent A.places A.columns
    (u : RatFunc ℚ) u.ne_zero hE ho
  refine ⟨StageExponents.bExponents e, StageExponents.qExponents e, ?_⟩
  have hp : (fun j => order (valuations A.poles A.places (.primary j)) (u : RatFunc ℚ)) = a := by
    funext j
    simpa only [coordinate_primary_embed] using hc (.primary j)
  simpa only [hp] using he

/-- The actual principal profile of a specified nonzero fraction. -/
def ofFunction (x : RatFunc ℚ) (hx : x ≠ 0) : A.Group :=
  profile A (Additive.ofMul (Units.mk0 x hx))

@[simp] theorem coordinate_ofFunction (x : RatFunc ℚ) (hx : x ≠ 0) (p : ProfilePlace A.Outside) :
    coordinate (ofFunction A x hx) p = order (valuations A.poles A.places p) x :=
  coordinate_profile A _ _

theorem ofFunction_mem (x : RatFunc ℚ) (hx : x ≠ 0) : ofFunction A x hx ∈ principals A :=
  ⟨Additive.ofMul (Units.mk0 x hx), rfl⟩

theorem generator_limit_order (j : ℕ) :
    order (valuations A.poles A.places .limit) (A.generators j) = 0 := by
  apply (order_eq_zero_iff _ (A.generators_ne_zero j)).mpr
  exact AtomProfiles.generators_horizontal_valuation A.raw A.exponent
    A.raw_ne_zero _
    (HorizontalOrders.retained_xPoint_of_constantCoeff_ne_zero A.poles A.constant_nonzero) j

theorem generator_outside_order (j : ℕ) (o : A.Outside) :
    order (valuations A.poles A.places (.outside o)) (A.generators j) = 0 := by
  apply (order_eq_zero_iff _ (A.generators_ne_zero j)).mpr
  cases o with
  | inl p => exact A.columns.guard p j
  | inr p =>
    exact AtomProfiles.generators_horizontal_valuation A.raw A.exponent
      A.raw_ne_zero p.val p.property.1 j

/-- The actual principal b_n gives the independent even relation 3e_(2n). -/
theorem b_profile (n : ℕ) :
    ofFunction A (ReturnPrefix.b A.generators n) (ReturnPrefix.b_ne_zero A.generators A.generators_ne_zero n) =
      primary (Finsupp.single (2 * n) 3) := by
  apply coordinate_injective
  funext p
  rw [coordinate_ofFunction A]
  cases p with
  | limit => exact generator_limit_order A _
  | primary j =>
    rw [coordinate_primary_embed]
    change order (SparsePrimaryDomain.vertical A.places (.inl j))
      (CompleteProfiles.generators A.raw A.exponent (Generator.b n).stage) = _
    simp only [order, A.columns.b, WithZero.log_exp, neg_neg]
    simp [PrimaryWordProfiles.bWeight, Finsupp.single_apply, eq_comm]
  | outside o => exact generator_outside_order A _ o

/-- The actual principal q_n gives exactly its three prescribed primary entries. -/
theorem q_profile (n : ℕ) :
    ofFunction A (ReturnPrefix.q A.generators n) (ReturnPrefix.q_ne_zero A.generators A.generators_ne_zero n) =
      primary (PrimaryProfileQuotient.qVector (Finsupp.single n 1)) := by
  apply coordinate_injective
  funext p
  rw [coordinate_ofFunction A]
  cases p with
  | limit => exact generator_limit_order A _
  | primary j =>
    rw [coordinate_primary_embed, PrincipalProfileImage.qVector_single_apply]
    change order (SparsePrimaryDomain.vertical A.places (.inl j))
      (CompleteProfiles.generators A.raw A.exponent (Generator.q n).stage) = _
    simp only [order, A.columns.q, WithZero.log_exp, neg_neg]
  | outside o => exact generator_outside_order A _ o

private theorem hom_mem_of_basis {A : Type*} [AddCommGroup A]
    (P : AddSubgroup A) (f : (ℕ →₀ ℤ) →+ A)
    (h : ∀ n, f (Finsupp.single n 1) ∈ P) (s : ℕ →₀ ℤ) : f s ∈ P := by
  induction s using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using P.zero_mem
  | add a b ha hb => simpa only [map_add] using P.add_mem ha hb
  | single n z =>
    have he : Finsupp.single n z = z • Finsupp.single n (1 : ℤ) := by
      classical
      ext j
      by_cases hn : n = j <;> simp [hn]
    rw [he, map_zsmul]
    exact P.zsmul_mem (h n) z

theorem b_relations_mem (s : ℕ →₀ ℤ) :
    primary (3 • PrimaryProfileQuotient.even s) ∈ principals A := by
  have hb : ∀ n, (primary.comp (3 • PrimaryProfileQuotient.even)) (Finsupp.single n 1) ∈ principals A := by
    intro n
    have h := ofFunction_mem A (ReturnPrefix.b A.generators n) (ReturnPrefix.b_ne_zero A.generators A.generators_ne_zero n)
    rw [b_profile A] at h
    simpa [AddMonoidHom.comp_apply, PrimaryProfileQuotient.even] using h
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply] using
    hom_mem_of_basis (principals A) (primary.comp (3 • PrimaryProfileQuotient.even)) hb s

theorem q_relations_mem (u : ℕ →₀ ℤ) :
    primary (PrimaryProfileQuotient.qVector u) ∈ principals A := by
  apply hom_mem_of_basis (principals A) (primary.comp PrimaryProfileQuotient.qVector) _ u
  intro n
  have h := ofFunction_mem A (ReturnPrefix.q A.generators n) (ReturnPrefix.q_ne_zero A.generators A.generators_ne_zero n)
  simpa only [AddMonoidHom.comp_apply, q_profile A] using h

/-- Every finite b/q signed relation is the profile of an actual principal fraction. -/
theorem primary_relation_reverse (a : ℕ →₀ ℤ)
    (ha : ∃ s u : ℕ →₀ ℤ, Represents s u a) : primary a ∈ principals A := by
  obtain ⟨s, u, ha⟩ := ha
  have hc := PrimaryProfileQuotient.represents_columns s u
  have he : a = 3 • PrimaryProfileQuotient.even s + PrimaryProfileQuotient.qVector u := by
    ext j
    obtain ⟨n, hj | hj⟩ : ∃ n : ℕ, j = 2 * n ∨ j = 2 * n + 1 := ⟨j / 2, by omega⟩
    · subst j
      cases n with
      | zero => exact ha.initial.trans hc.initial.symm
      | succ n =>
        have h := (ha.even_succ n).trans (hc.even_succ n).symm
        simpa only [Nat.mul_add, Nat.mul_one, Finsupp.coe_add, Finsupp.coe_smul] using h
    · subst j
      exact (ha.odd n).trans (hc.odd n).symm
  rw [he, map_add]
  exact (principals A).add_mem (b_relations_mem A s) (q_relations_mem A u)

theorem primary_relation_iff (a : ℕ →₀ ℤ) :
    primary a ∈ principals A ↔ ∃ s u : ℕ →₀ ℤ, Represents s u a :=
  ⟨primary_relation_forward A a, primary_relation_reverse A a⟩

/-- A rational prime has exactly its own guard entry among the outside entries. -/
theorem prime_profile_outside (p : GuardSupport.PrimeIndex) :
    (ofFunction A (p.val : RatFunc ℚ) (Nat.cast_ne_zero.mpr p.property.ne_zero)).2.2 =
      Finsupp.single (.inl p) 1 := by
  classical
  ext o
  change coordinate (ofFunction A (p.val : RatFunc ℚ) _) (.outside o) = _
  rw [coordinate_ofFunction A]
  cases o with
  | inl q =>
    by_cases hqp : q = p
    · subst q
      change order (EvaluationDVR.valuation p.val _) (p.val : RatFunc ℚ) = _
      simp [order]
    · have hv : SparsePrimaryDomain.vertical A.places (.inr q) (p.val : RatFunc ℚ) = 1 := by
        change Padic.mulValuation ((GuardSupport.guardEvaluation _ _ q) (p.val : RatFunc ℚ)) = 1
        rw [map_natCast]
        apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
        apply Padic.norm_natCast_eq_one_iff.mpr
        exact (Nat.coprime_primes q.property p.property).mpr
          (fun h => hqp (Subtype.ext h))
      change order (SparsePrimaryDomain.vertical A.places (.inr q)) (p.val : RatFunc ℚ) = _
      simp [order, hv, Ne.symm hqp]
  | inr h =>
    have hv : HorizontalOrders.valuation h.val (p.val : RatFunc ℚ) = 1 := by
      have hc := HorizontalOrders.valuation_constant h.val (p.val : ℚ)
        (Nat.cast_ne_zero.mpr p.property.ne_zero)
      simpa only [map_natCast] using hc
    change order (HorizontalOrders.valuation h.val) (p.val : RatFunc ℚ) = _
    simp [order, hv]

theorem guard_lift (p : GuardSupport.PrimeIndex) :
    ∃ x ∈ principals A, x.2.2 = Finsupp.single (.inl p) 1 :=
  ⟨_, ofFunction_mem A _ _, prime_profile_outside A p⟩

/-- A surviving horizontal irreducible has its unique horizontal order one;
its guard and primary entries are unrestricted. -/
theorem horizontal_profile (h : CompleteProfiles.OtherHorizontal A.poles)
    (k : CompleteProfiles.OtherHorizontal A.poles) :
    (ofFunction A (PrincipalProfiles.factor h.val) (PrincipalProfiles.factor_ne_zero _)).2.2 (.inr k) =
      Finsupp.single h 1 k := by
  classical
  change coordinate (ofFunction A (PrincipalProfiles.factor h.val) _) (.outside (.inr k)) = _
  rw [coordinate_ofFunction A]
  change order (HorizontalOrders.valuation k.val) (PrincipalProfiles.factor h.val) = _
  by_cases hhk : h = k
  · subst k
    simp [order]
  · have hne : h.val ≠ k.val := fun he => hhk (Subtype.ext he)
    simp [order, HorizontalOrders.valuation_factor_of_ne _ _ hne, hhk]

theorem horizontal_lift (h : CompleteProfiles.OtherHorizontal A.poles) :
    ∃ x ∈ principals A, ∀ k : CompleteProfiles.OtherHorizontal A.poles,
      x.2.2 (.inr k) = Finsupp.single h 1 k :=
  ⟨_, ofFunction_mem A _ _, horizontal_profile A h⟩

/-- The exceptional first primary has value two, so t has λ+e₀ profile. -/
theorem X_profile : ofFunction A RatFunc.X RatFunc.X_ne_zero = tProfile := by
  apply coordinate_injective
  funext p
  rw [coordinate_ofFunction A]
  cases p with
  | limit =>
    change order (HorizontalOrders.valuation HorizontalOrders.xPoint) RatFunc.X = 1
    simp [order]
  | primary j =>
    change order (SparsePrimaryDomain.vertical A.places (.inl j)) RatFunc.X = 1 + Finsupp.single 0 1 j
    rw [order, SparseAtoms.primary_X_valuation A.places A.first]
    simp only [WithZero.log_exp, neg_neg]
    by_cases hj : j = 0 <;> simp [primaryAtomProfile, hj]
  | outside o =>
    change order (valuations A.poles A.places (.outside o)) RatFunc.X = 0
    apply (order_eq_zero_iff _ RatFunc.X_ne_zero).mpr
    cases o with
    | inl p => exact SparseAtoms.guard_X_valuation A.places A.guard_unit p
    | inr h =>
      exact HorizontalOrders.valuation_factor_of_ne h.val HorizontalOrders.xPoint h.property.2.symm

theorem tProfile_mem : (tProfile : A.Group) ∈ principals A := by
  rw [← X_profile A]
  exact ofFunction_mem A _ _

theorem horizontal_profile_limit (h : CompleteProfiles.OtherHorizontal A.poles) :
    (ofFunction A (PrincipalProfiles.factor h.val) (PrincipalProfiles.factor_ne_zero _)).1 = 0 := by
  change coordinate (ofFunction A (PrincipalProfiles.factor h.val) _) .limit = 0
  rw [coordinate_ofFunction A]
  change order (HorizontalOrders.valuation HorizontalOrders.xPoint) (PrincipalProfiles.factor h.val) = 0
  simp [order, HorizontalOrders.valuation_factor_of_ne _ _ h.property.2]

/-- Every actual ideal-profile class has a finite pure primary representative. -/
theorem clear_to_primary (x : A.Group) : ∃ a : ℕ →₀ ℤ, x - primary a ∈ principals A :=
  ProfileElimination.clear_to_primary (principals A) (guard_lift A) (horizontal_lift A) (tProfile_mem A) x

/-- The quotient by actual principal profiles is the countable direct sum of Z/3. -/
def quotientEquiv : A.Group ⧸ principals A ≃+ (ℕ →₀ ZMod 3) :=
  PrimaryProfileQuotient.quotientEquiv (principals A) (clear_to_primary A) (primary_relation_iff A)

/-- At a prime omitted from the primary enumeration, p itself gives the
entire guard singleton profile, with no primary or limit correction. -/
theorem unpaired_prime_profile (p : GuardSupport.PrimeIndex)
    (hp : p ∉ Set.range A.places.primes) :
    ofFunction A (p.val : RatFunc ℚ) (Nat.cast_ne_zero.mpr p.property.ne_zero) =
      (0, 0, Finsupp.single (.inl p) 1) := by
  apply coordinate_injective
  funext l
  cases l with
  | limit =>
    rw [coordinate_ofFunction]
    change order (HorizontalOrders.valuation HorizontalOrders.xPoint) (p.val : RatFunc ℚ) = 0
    have hv := HorizontalOrders.valuation_constant HorizontalOrders.xPoint (p.val : ℚ)
      (Nat.cast_ne_zero.mpr p.property.ne_zero)
    simp only [map_natCast] at hv
    simp [order, hv]
  | primary j =>
    rw [coordinate_ofFunction]
    change order (SparsePrimaryDomain.vertical A.places (.inl j)) (p.val : RatFunc ℚ) = 0
    have hv := (SparsePrimaryDomain.unpaired_prime_profile A.places p hp).2 (.inl j) (by simp)
    simp [order, hv]
  | outside o =>
    exact congrArg (fun f : A.Outside →₀ ℤ => f o) (prime_profile_outside A p)

end UnconditionalCounterexample.SparsePrincipalProfiles
