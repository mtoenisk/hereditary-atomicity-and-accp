import UnconditionalCounterexample.PaperAtoms
import UnconditionalCounterexample.ReturnChain
import UnconditionalCounterexample.PicardProfiles
import UnconditionalCounterexample.PrimaryProfileQuotient
import UnconditionalCounterexample.ProfileElimination

noncomputable section
namespace UnconditionalCounterexample.PrincipalProfileImage
open Polynomial PaperConstruction PicardProfiles CompleteProfiles DiscreteOrders NormalizedWords

abbrev Outside := CompleteProfiles.Outside poles
abbrev Group := PicardProfiles.Profile Outside

/-- The actual additive valuation coordinates of a nonzero rational function. -/
def fractionCoordinates : Additive (RatFunc ℚ)ˣ →+ (ProfilePlace Outside → ℤ) where
  toFun u p := order (valuations poles places p) (u.toMul : RatFunc ℚ)
  map_zero' := by
    funext p
    exact order_one _
  map_add' u v := by
    funext p
    exact order_mul _ u.toMul.ne_zero v.toMul.ne_zero

theorem fractionCoordinates_restricted (u : Additive (RatFunc ℚ)ˣ) :
    Restricted (fractionCoordinates u) := by
  exact ⟨eventually_primary poles places _ u.toMul.ne_zero,
    finite_outside poles places guardSupport _ u.toMul.ne_zero⟩

/-- The actual principal profile homomorphism; no ideal or class is chosen here. -/
def profile : Additive (RatFunc ℚ)ˣ →+ Group where
  toFun u := ofCoordinates (fractionCoordinates u) (fractionCoordinates_restricted u)
  map_zero' := by
    apply coordinate_injective
    rw [coordinate_ofCoordinates, map_zero, map_zero]
  map_add' u v := by
    apply coordinate_injective
    rw [coordinate_ofCoordinates, map_add, map_add, coordinate_ofCoordinates, coordinate_ofCoordinates]

@[simp] theorem coordinate_profile (u : Additive (RatFunc ℚ)ˣ) (p : ProfilePlace Outside) :
    coordinate (profile u) p = order (valuations poles places p) (u.toMul : RatFunc ℚ) := by
  exact congrFun (coordinate_ofCoordinates (fractionCoordinates u) (fractionCoordinates_restricted u)) p

/-- Exactly the profiles of actual nonzero principal fractional ideals. -/
def principals : AddSubgroup Group := profile.range

theorem mem_principals_iff (x : Group) :
    x ∈ principals ↔ ∃ u : (RatFunc ℚ)ˣ, profile (Additive.ofMul u) = x := Iff.rfl

private theorem rawFacts (j : ℕ) : (raw j).Monic ∧ Irreducible (raw j) :=
  ⟨construction.chain.raw_monic j, construction.chain.raw_irreducible j⟩
private theorem rawInj : Function.Injective raw :=
  fun _ _ h => construction.chain.raw_degree_strict.injective (congrArg Polynomial.natDegree h)

/-- A pureprimary actual principal relation has the exact finite b/q signed representation. -/
theorem primary_relation_forward (a : ℕ →₀ ℤ) (ha : primary a ∈ principals) :
    ∃ s u : ℕ →₀ ℤ, Represents s u a := by
  obtain ⟨u, hu⟩ := (mem_principals_iff _).mp ha
  have hc (p : ProfilePlace Outside) :
      order (valuations poles places p) (u : RatFunc ℚ) = coordinate (primary a) p := by
    exact (coordinate_profile (Additive.ofMul u) p).symm.trans
      (congrArg (fun x => coordinate x p) hu)
  have hE : order (valuations poles places .limit) (u : RatFunc ℚ) = 0 := hc .limit
  have ho (i : Outside) : order (valuations poles places (.outside i)) (u : RatFunc ℚ) = 0 := hc (.outside i)
  obtain ⟨e, _, he⟩ := exists_signed_word raw rawFacts rawInj exponent places generatorProfiles
    (u : RatFunc ℚ) u.ne_zero hE ho
  refine ⟨StageExponents.bExponents e, StageExponents.qExponents e, ?_⟩
  have hp : (fun j => order (valuations poles places (.primary j)) (u : RatFunc ℚ)) = a := by
    funext j
    simpa only [coordinate_primary_embed] using hc (.primary j)
  simpa only [hp] using he

/-- The actual principal profile of a specified nonzero fraction. -/
def ofFunction (x : RatFunc ℚ) (hx : x ≠ 0) : Group :=
  profile (Additive.ofMul (Units.mk0 x hx))

@[simp] theorem coordinate_ofFunction (x : RatFunc ℚ) (hx : x ≠ 0) (p : ProfilePlace Outside) :
    coordinate (ofFunction x hx) p = order (valuations poles places p) x :=
  coordinate_profile _ _

theorem ofFunction_mem (x : RatFunc ℚ) (hx : x ≠ 0) : ofFunction x hx ∈ principals :=
  ⟨Additive.ofMul (Units.mk0 x hx), rfl⟩

theorem generator_limit_order (j : ℕ) :
    order (valuations poles places .limit) (construction.chain.generators j) = 0 := by
  apply (order_eq_zero_iff _ (construction.chain.generators_ne_zero j)).mpr
  exact AtomProfiles.generators_horizontal_valuation raw exponent
    (fun k => (rawFacts k).1.ne_zero) _
    (HorizontalOrders.retained_xPoint_of_constantCoeff_ne_zero poles (fun _ hf => raw_constant hf)) j

theorem generator_outside_order (j : ℕ) (o : Outside) :
    order (valuations poles places (.outside o)) (construction.chain.generators j) = 0 := by
  apply (order_eq_zero_iff _ (construction.chain.generators_ne_zero j)).mpr
  cases o with
  | inl p => exact generator_guard_valuation j p
  | inr p =>
    exact AtomProfiles.generators_horizontal_valuation raw exponent
      (fun k => (rawFacts k).1.ne_zero) p.val p.property.1 j

/-- The actual principal b_n gives the independent even relation 3e_(2n). -/
theorem b_profile (n : ℕ) :
    ofFunction (construction.chain.b n) (construction.chain.b_ne_zero n) =
      primary (Finsupp.single (2 * n) 3) := by
  apply coordinate_injective
  funext p
  rw [coordinate_ofFunction]
  cases p with
  | limit => exact generator_limit_order _
  | primary j =>
    rw [coordinate_primary_embed]
    change order (PairedDomain.vertical places (.inl j))
      (CompleteProfiles.generators raw exponent (Generator.b n).stage) = _
    simp only [order, generator_b_valuation, WithZero.log_exp, neg_neg]
    simp [PrimaryWordProfiles.bWeight, Finsupp.single_apply, eq_comm]
  | outside o => exact generator_outside_order _ o

theorem qVector_single_apply (n j : ℕ) :
    PrimaryProfileQuotient.qVector (Finsupp.single n 1) j = PrimaryWordProfiles.qWeight n j := by
  change (2 • PrimaryProfileQuotient.even (Finsupp.single n 1) +
    PrimaryProfileQuotient.odd (Finsupp.single n 1) +
    2 • PrimaryProfileQuotient.even (PrimaryProfileQuotient.shift (Finsupp.single n 1))) j = _
  simp [PrimaryProfileQuotient.even, PrimaryProfileQuotient.odd, PrimaryProfileQuotient.shift,
    Finsupp.mapDomain_single, Finsupp.single_apply, PrimaryWordProfiles.qWeight, eq_comm, Nat.mul_add]

/-- The actual principal q_n gives exactly its three prescribed primary entries. -/
theorem q_profile (n : ℕ) :
    ofFunction (construction.chain.q n) (construction.chain.q_ne_zero n) =
      primary (PrimaryProfileQuotient.qVector (Finsupp.single n 1)) := by
  apply coordinate_injective
  funext p
  rw [coordinate_ofFunction]
  cases p with
  | limit => exact generator_limit_order _
  | primary j =>
    rw [coordinate_primary_embed, qVector_single_apply]
    change order (PairedDomain.vertical places (.inl j))
      (CompleteProfiles.generators raw exponent (Generator.q n).stage) = _
    simp only [order, generator_q_valuation, WithZero.log_exp, neg_neg]
  | outside o => exact generator_outside_order _ o

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
    primary (3 • PrimaryProfileQuotient.even s) ∈ principals := by
  have hb : ∀ n, (primary.comp (3 • PrimaryProfileQuotient.even)) (Finsupp.single n 1) ∈ principals := by
    intro n
    have h := ofFunction_mem (construction.chain.b n) (construction.chain.b_ne_zero n)
    rw [b_profile] at h
    simpa [AddMonoidHom.comp_apply, PrimaryProfileQuotient.even] using h
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply] using
    hom_mem_of_basis principals (primary.comp (3 • PrimaryProfileQuotient.even)) hb s

theorem q_relations_mem (u : ℕ →₀ ℤ) :
    primary (PrimaryProfileQuotient.qVector u) ∈ principals := by
  apply hom_mem_of_basis principals (primary.comp PrimaryProfileQuotient.qVector) _ u
  intro n
  have h := ofFunction_mem (construction.chain.q n) (construction.chain.q_ne_zero n)
  simpa only [AddMonoidHom.comp_apply, q_profile] using h

/-- Every finite b/q signed relation is the profile of an actual principal fraction. -/
theorem primary_relation_reverse (a : ℕ →₀ ℤ)
    (ha : ∃ s u : ℕ →₀ ℤ, Represents s u a) : primary a ∈ principals := by
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
  exact principals.add_mem (b_relations_mem s) (q_relations_mem u)

theorem primary_relation_iff (a : ℕ →₀ ℤ) :
    primary a ∈ principals ↔ ∃ s u : ℕ →₀ ℤ, Represents s u a :=
  ⟨primary_relation_forward a, primary_relation_reverse a⟩

/-- A rational prime has exactly its own guard entry among the outside entries. -/
theorem prime_profile_outside (p : GuardSupport.PrimeIndex) :
    (ofFunction (p.val : RatFunc ℚ) (Nat.cast_ne_zero.mpr p.property.ne_zero)).2.2 =
      Finsupp.single (.inl p) 1 := by
  classical
  ext o
  change coordinate (ofFunction (p.val : RatFunc ℚ) _) (.outside o) = _
  rw [coordinate_ofFunction]
  cases o with
  | inl q =>
    by_cases hqp : q = p
    · subst q
      change order (EvaluationDVR.valuation p.val _) (p.val : RatFunc ℚ) = _
      simp [order]
    · have hv : PairedDomain.vertical places (.inr q) (p.val : RatFunc ℚ) = 1 := by
        change Padic.mulValuation ((GuardSupport.guardEvaluation _ _ q) (p.val : RatFunc ℚ)) = 1
        rw [map_natCast]
        apply GuardSupport.mulValuation_eq_one_of_norm_eq_one
        apply Padic.norm_natCast_eq_one_iff.mpr
        exact (Nat.coprime_primes q.property p.property).mpr
          (fun h => hqp (Subtype.ext h))
      change order (PairedDomain.vertical places (.inr q)) (p.val : RatFunc ℚ) = _
      simp [order, hv, Ne.symm hqp]
  | inr h =>
    have hv : HorizontalOrders.valuation h.val (p.val : RatFunc ℚ) = 1 := by
      have hc := HorizontalOrders.valuation_constant h.val (p.val : ℚ)
        (Nat.cast_ne_zero.mpr p.property.ne_zero)
      simpa only [map_natCast] using hc
    change order (HorizontalOrders.valuation h.val) (p.val : RatFunc ℚ) = _
    simp [order, hv]

theorem guard_lift (p : GuardSupport.PrimeIndex) :
    ∃ x ∈ principals, x.2.2 = Finsupp.single (.inl p) 1 :=
  ⟨_, ofFunction_mem _ _, prime_profile_outside p⟩

/-- A surviving horizontal irreducible has its unique horizontal order one;
its guard and primary entries are unrestricted. -/
theorem horizontal_profile (h : CompleteProfiles.OtherHorizontal poles)
    (k : CompleteProfiles.OtherHorizontal poles) :
    (ofFunction (PrincipalProfiles.factor h.val) (PrincipalProfiles.factor_ne_zero _)).2.2 (.inr k) =
      Finsupp.single h 1 k := by
  classical
  change coordinate (ofFunction (PrincipalProfiles.factor h.val) _) (.outside (.inr k)) = _
  rw [coordinate_ofFunction]
  change order (HorizontalOrders.valuation k.val) (PrincipalProfiles.factor h.val) = _
  by_cases hhk : h = k
  · subst k
    simp [order]
  · have hne : h.val ≠ k.val := fun he => hhk (Subtype.ext he)
    simp [order, HorizontalOrders.valuation_factor_of_ne _ _ hne, hhk]

theorem horizontal_lift (h : CompleteProfiles.OtherHorizontal poles) :
    ∃ x ∈ principals, ∀ k : CompleteProfiles.OtherHorizontal poles,
      x.2.2 (.inr k) = Finsupp.single h 1 k :=
  ⟨_, ofFunction_mem _ _, horizontal_profile h⟩

/-- The exceptional first primary has value two, so t has λ+e₀ profile. -/
theorem X_profile : ofFunction RatFunc.X RatFunc.X_ne_zero = tProfile := by
  apply coordinate_injective
  funext p
  rw [coordinate_ofFunction]
  cases p with
  | limit =>
    change order (HorizontalOrders.valuation HorizontalOrders.xPoint) RatFunc.X = 1
    simp [order]
  | primary j =>
    change order (PairedDomain.vertical places (.inl j)) RatFunc.X = 1 + Finsupp.single 0 1 j
    rw [order, AtomProfiles.primary_X_valuation places PrimaryChoices.primary_zero]
    simp only [WithZero.log_exp, neg_neg]
    by_cases hj : j = 0 <;> simp [primaryAtomProfile, hj]
  | outside o =>
    change order (valuations poles places (.outside o)) RatFunc.X = 0
    apply (order_eq_zero_iff _ RatFunc.X_ne_zero).mpr
    cases o with
    | inl p => exact AtomProfiles.guard_X_valuation places construction.chain.guardChain.value_unit p
    | inr h =>
      exact HorizontalOrders.valuation_factor_of_ne h.val HorizontalOrders.xPoint h.property.2.symm

theorem tProfile_mem : (tProfile : Group) ∈ principals := by
  rw [← X_profile]
  exact ofFunction_mem _ _

theorem horizontal_profile_limit (h : CompleteProfiles.OtherHorizontal poles) :
    (ofFunction (PrincipalProfiles.factor h.val) (PrincipalProfiles.factor_ne_zero _)).1 = 0 := by
  change coordinate (ofFunction (PrincipalProfiles.factor h.val) _) .limit = 0
  rw [coordinate_ofFunction]
  change order (HorizontalOrders.valuation HorizontalOrders.xPoint) (PrincipalProfiles.factor h.val) = 0
  simp [order, HorizontalOrders.valuation_factor_of_ne _ _ h.property.2]

/-- Every actual ideal-profile class has a finite pureprimary representative. -/
theorem clear_to_primary (x : Group) : ∃ a : ℕ →₀ ℤ, x - primary a ∈ principals :=
  ProfileElimination.clear_to_primary principals guard_lift horizontal_lift tProfile_mem x

/-- The quotient by actual principal profiles is the countable direct sum of Z/3. -/
def quotientEquiv : Group ⧸ principals ≃+ (ℕ →₀ ZMod 3) :=
  PrimaryProfileQuotient.quotientEquiv principals clear_to_primary primary_relation_iff

end UnconditionalCounterexample.PrincipalProfileImage
