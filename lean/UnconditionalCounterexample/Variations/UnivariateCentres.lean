import UnconditionalCounterexample.Variations.UnivariateSelection

/-!
# Univariate primes at translated centres

At a fresh prime the primary is chosen in a ball around the specified integer
centre, with an exact order of approach. Screening the prime against the
values of the earlier polynomials at that centre makes all of them units at
the primary. The simultaneous guard avoids the same polynomials and both
residues zero and one.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.UnivariateCentres

open Polynomial GuardSupport

/-- Moving the primary to an integer centre preserves the exact prescribed
order of its displacement, including the exceptional initial order two. -/
theorem exists_primary_at (p : ℕ) [Fact p.Prime] (c k : ℕ) (hk : 0 < k) :
    ∃ α : ℤ_[p], Transcendental ℚ α.val ∧ PadicInt.toZMod α = c ∧
      (α.val - c).valuation = k := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨a, hclose, ht⟩ := EvaluationChoices.exists_transcendental_near p
    ((c : ℚ_[p]) + (p : ℚ_[p]) ^ k) _ (norm_pos_iff.mpr (pow_ne_zero k hp))
  have hn : ‖a - c‖ = ‖(p : ℚ_[p]) ^ k‖ :=
    Padic.norm_eq_of_norm_sub_lt_right (by simpa only [sub_sub] using hclose)
  have hlt : ‖a - c‖ < 1 := by
    rw [hn, norm_pow]
    apply pow_lt_one₀ (norm_nonneg _) _ (Nat.ne_of_gt hk)
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  let z : ℤ_[p] := ⟨a - c, hlt.le⟩
  let α := z + (c : ℤ_[p])
  have hα : α.val = a := by
    change (a - c) + (c : ℤ_[p]).val = a
    rw [PadicInt.coe_natCast, sub_add_cancel]
  refine ⟨α, hα ▸ ht, ?_, ?_⟩
  · have hz := EvaluationChoices.toZMod_eq_of_norm_sub_lt_one p (a := z) (b := 0)
      (by simpa only [sub_zero, PadicInt.norm_def] using hlt)
    simp [α, hz]
  · rw [hα, EvaluationChoices.valuation_eq_of_norm_eq p
      (norm_ne_zero_iff.mp (hn ▸ (norm_ne_zero_iff.mpr (pow_ne_zero k hp))))
      (pow_ne_zero k hp) hn, Padic.valuation_pow, Padic.valuation_p, mul_one]

/-- A guard prescribed at 2 has residue 3 modulo 4. -/
theorem exists_dyadic_guard :
    ∃ β : ℤ_[2], Transcendental ℚ β.val ∧ IsUnit β ∧ PadicInt.toZModPow 2 β = 3 := by
  obtain ⟨b, hb, ht⟩ := EvaluationChoices.exists_transcendental_near 2 3 (1/4) (by norm_num)
  have h3 : ‖(3 : ℚ_[2])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 2 3)
  have hb1 : ‖b‖ = 1 := (Padic.norm_eq_of_norm_sub_lt_right (by rw [h3]; linarith :
    ‖b - 3‖ < ‖(3 : ℚ_[2])‖)).trans h3
  let β : ℤ_[2] := ⟨b, hb1.le⟩
  refine ⟨β, ht, PadicInt.isUnit_iff.mpr hb1, ?_⟩
  have h : ‖β - 3‖ ≤ (2 : ℝ) ^ (-(2 : ℤ)) := by
    change ‖b - 3‖ ≤ _
    norm_num
    linarith
  have hm := (PadicInt.norm_le_pow_iff_mem_span_pow (β - 3) 2).mp h
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_ofNat] at hm
  exact sub_eq_zero.mp hm

/-- The determinant used for two-point integral lifting works at either
centre, including when both arguments are units. -/
theorem difference_unit {p : ℕ} [Fact p.Prime] {α β : ℤ_[p]}
    (h : PadicInt.toZMod β ≠ PadicInt.toZMod α) : IsUnit (β - α) := by
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  simpa only [map_sub, sub_ne_zero] using h

/-- A rational number and its inverse both have integral evaluations above
the elementary denominator cutoff. -/
private theorem norm_rat_eq_one {p : ℕ} [Fact p.Prime] (q : ℚ) (hq : q ≠ 0)
    (hp : max q.den q⁻¹.den < p) : ‖(q : ℚ_[p])‖ = 1 := by
  have h (r : ℚ) (hr : r.den < p) : ‖(r : ℚ_[p])‖ ≤ 1 := by
    apply Padic.norm_rat_le_one
    intro hd
    exact (Nat.not_lt_of_ge (Nat.le_of_dvd r.den_pos hd)) hr
  have h1 := h q ((le_max_left _ _).trans_lt hp)
  have h2 := h q⁻¹ ((le_max_right _ _).trans_lt hp)
  rw [Rat.cast_inv, norm_inv] at h2
  exact le_antisymm h1 ((inv_le_one₀ (norm_pos_iff.mpr (Rat.cast_ne_zero.mpr hq))).mp h2)

/-- If an integral model takes a unit value at the integer centre, then every
argument in its residue class gives a unit value for the same polynomial. -/
private theorem norm_eval_one_of_same_residue {p : ℕ} [Fact p.Prime]
    (Q : ℚ[X]) (G : ℤ_[p][X])
    (hG : G.map (algebraMap ℤ_[p] ℚ_[p]) = Q.map (algebraMap ℚ ℚ_[p]))
    (c : ℕ) (α : ℤ_[p]) (hr : PadicInt.toZMod α = c)
    (hc : ‖(algebraMap ℚ ℚ_[p] (Q.eval (c : ℚ)))‖ = 1) :
    ‖Q.eval₂ (algebraMap ℚ ℚ_[p]) α.val‖ = 1 := by
  have he := congrArg (fun f : ℚ_[p][X] => f.eval (c : ℚ_[p])) hG
  have hmodel : ((G.eval (c : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) = algebraMap ℚ ℚ_[p] (Q.eval (c : ℚ)) := by
    change (algebraMap ℤ_[p] ℚ_[p]) _ = _
    rw [← eval₂_at_apply, ← eval₂_at_apply, map_natCast, map_natCast]
    simpa only [eval_map] using he
  have hu : IsUnit (G.eval (c : ℤ_[p])) := by
    apply PadicInt.isUnit_iff.mpr
    change ‖((G.eval (c : ℤ_[p]) : ℤ_[p]) : ℚ_[p])‖ = 1
    rw [hmodel]
    exact hc
  apply RationalGuardStage.norm_eval_eq_one_of_integral_model Q G hG
  apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
  have ht := (padicInt_isUnit_iff_toZMod_ne_zero _).mp hu
  simpa only [← eval₂_at_apply, hr, map_natCast] using ht

/-- Pick a fresh paired prime after inspecting a finite polynomial prefix.
Both actual arguments see every old raw as a unit. Its primary has the
requested order at either zero or one and its guard has a logarithmic
representative. The finite forbidden set can contain earlier choices of
either role. -/
theorem exists_fresh_pair {J : Type*} [Fintype J] (A : PaperGuardStages.Assignment)
    (avoid : Finset PrimeIndex) (Q : J → ℚ[X]) (hQ : ∀ j, (Q j).Monic)
    (hsupp : ∀ j n (p : PrimeIndex), p.val ∣ ((Q j).coeff n).den → p ∈ A.primes)
    (c k stage bound : ℕ) (hc : c = 0 ∨ c = 1) (hk : 0 < k)
    (hvalue : ∀ j, (Q j).eval (c : ℚ) ≠ 0) :
    ∃ p : PrimeIndex, bound < p.val ∧ 2 < p.val ∧ p ∉ A.primes ∧ p ∉ avoid ∧
      ∃ (α : ℤ_[p.val]) (g : PaperGuardStages.Guard p),
        Transcendental ℚ α.val ∧ PadicInt.toZMod α = c ∧
        (α.val - c).valuation = k ∧ g.birth = stage ∧
        PadicInt.toZMod g.value ≠ 1 ∧ IsUnit (g.value - α) ∧
        ∀ j, ‖(Q j).eval₂ (algebraMap ℚ ℚ_[p.val]) α.val‖ = 1 ∧
          ‖(Q j).eval₂ (algebraMap ℚ ℚ_[p.val]) g.value.val‖ = 1 := by
  classical
  let cutoff (j : J) := max ((Q j).eval (c : ℚ)).den (((Q j).eval (c : ℚ))⁻¹).den
  let degBound := 2 ^ (4 + ∑ j, (Q j).natDegree)
  obtain ⟨p, hp, hnew⟩ := GuardStages.exists_fresh_prime (A.primes ∪ avoid)
    (max (max bound 2) (max degBound (Finset.univ.sup cutoff)))
  have hb : bound < p.val := by omega
  have h2 : 2 < p.val := by omega
  have hd : degBound < p.val := by omega
  have hcut : Finset.univ.sup cutoff < p.val := by omega
  rw [Finset.mem_union, not_or] at hnew
  obtain ⟨F, hF⟩ := RationalGuardStage.exists_models A Q hQ hsupp
  obtain ⟨g, hbirth, hguard, hraw⟩ := PaperGuardStages.exists_large_guard p stage
    Finset.univ (F p) (fun j _ => (hF p hnew.1 j).2.2) (by
      simpa only [Finset.sum_congr rfl (fun j _ => (hF p hnew.1 j).2.1)] using hd)
  obtain ⟨α, ht, hr, hv⟩ := exists_primary_at p.val c k hk
  refine ⟨p, hb, h2, hnew.1, hnew.2, α, g,
    ht, hr, hv, hbirth, hguard, difference_unit ?_, ?_⟩
  · rw [hr]
    rcases hc with rfl | rfl
    · simpa using (padicInt_isUnit_iff_toZMod_ne_zero _).mp g.unit
    · simpa using hguard
  · intro j
    exact ⟨norm_eval_one_of_same_residue _ _ (hF p hnew.1 j).1 c α hr
      (norm_rat_eq_one _ (hvalue j) ((Finset.le_sup (Finset.mem_univ j) :
        cutoff j ≤ Finset.univ.sup cutoff).trans_lt hcut)),
      RationalGuardStage.norm_eval_eq_one_of_integral_model _ _ (hF p hnew.1 j).1 _
        (hraw j (Finset.mem_univ j))⟩

/-- Three actual fibres supplied to the same polynomial selector. The odd
primes carry independent primary orders. -/
structure ThreeSites (n : ℕ) (P : ℕ → ℚ[X]) (k₀ k₁ : ℕ) where
  guardTwo : ℤ_[2]
  guardTwo_trans : Transcendental ℚ guardTwo.val
  guardTwo_modFour : PadicInt.toZModPow 2 guardTwo = 3
  prime : Bool → PrimeIndex
  odd : ∀ b, 2 < (prime b).val
  distinct : prime false ≠ prime true
  guard : (b : Bool) → PaperGuardStages.Guard (prime b)
  primary : (b : Bool) → Univariate.Primary (prime b) (guard b).value
  primaryResidue : ∀ b, PadicInt.toZMod (primary b).val = if b then 1 else 0
  primaryOrder : ∀ b, ((primary b).val.val - (if b then 1 else 0)).valuation =
    if b then (k₁ : ℤ) else (k₀ : ℤ)
  oldUnits : ∀ b j, j < n →
    ‖(P j).eval₂ (algebraMap ℚ ℚ_[(prime b).val]) (primary b).val.val‖ = 1 ∧
    ‖(P j).eval₂ (algebraMap ℚ ℚ_[(prime b).val]) (guard b).value.val‖ = 1

/-- Both paired primes are selected outside the previous assignments and
beyond an arbitrary prescribed cutoff. -/
theorem exists_three_sites {n : ℕ} (P : ℕ → ℚ[X]) (A : PaperGuardStages.Assignment)
    (avoid : Finset PrimeIndex) (bound k₀ k₁ : ℕ) (hk₀ : 0 < k₀) (hk₁ : 0 < k₁)
    (hP : ∀ j < n, (P j).Monic)
    (hsupp : ∀ j < n, ∀ i (p : PrimeIndex), p.val ∣ ((P j).coeff i).den → p ∈ A.primes)
    (h₀ : ∀ j < n, (P j).eval 0 ≠ 0) (h₁ : ∀ j < n, (P j).eval 1 ≠ 0) :
    ∃ B : ThreeSites n P k₀ k₁, ∀ b, bound < (B.prime b).val ∧
      B.prime b ∉ A.primes ∧ B.prime b ∉ avoid := by
  classical
  let Q (i : Fin n) := P i.val
  obtain ⟨p, hpb, hp2, hpA, hpV, α, g, ht, hr, hv, _, _, hdiff, hold⟩ :=
    exists_fresh_pair A avoid Q (fun i => hP _ i.isLt) (fun i => hsupp _ i.isLt)
      0 k₀ n bound (Or.inl rfl) hk₀ (fun i => by simpa [Q] using h₀ _ i.isLt)
  obtain ⟨q, hqb, hq2, hqA, hqV, α', g', ht', hr', hv', _, _, hdiff', hold'⟩ :=
    exists_fresh_pair A (insert p avoid) Q (fun i => hP _ i.isLt) (fun i => hsupp _ i.isLt)
      1 k₁ n bound (Or.inr rfl) hk₁ (fun i => by simpa [Q] using h₁ _ i.isLt)
  obtain ⟨β, hβ, _, hmod⟩ := exists_dyadic_guard
  have different {p : PrimeIndex} (a b : ℤ_[p.val]) (h : IsUnit (b - a)) :
      PadicInt.toZMod a ≠ PadicInt.toZMod b := by
    have hn := (padicInt_isUnit_iff_toZMod_ne_zero _).mp h
    rw [map_sub, sub_ne_zero] at hn
    exact hn.symm
  let B : ThreeSites n P k₀ k₁ := {
    guardTwo := β, guardTwo_trans := hβ, guardTwo_modFour := hmod
    prime := fun b => Bool.rec p q b
    odd := fun b => by cases b <;> assumption
    distinct := fun he => hqV (Finset.mem_insert.mpr (Or.inl he.symm))
    guard := fun b => by cases b; exact g; exact g'
    primary := fun b => by
      cases b
      · exact ⟨α, ht, different _ _ hdiff⟩
      · exact ⟨α', ht', different _ _ hdiff'⟩
    primaryResidue := fun b => by
      cases b
      · simpa using hr
      · simpa using hr'
    primaryOrder := fun b => by
      cases b
      · simpa using hv
      · simpa using hv'
    oldUnits := fun b j hj => by cases b; exact hold ⟨j, hj⟩; exact hold' ⟨j, hj⟩ }
  refine ⟨B, ?_⟩
  intro b
  cases b
  · exact ⟨hpb, hpA, hpV⟩
  · exact ⟨hqb, hqA, fun h => hqV (Finset.mem_insert_of_mem h)⟩

namespace ThreeSites

variable {n : ℕ} {P : ℕ → ℚ[X]} {k₀ k₁ : ℕ} (B : ThreeSites n P k₀ k₁)

def primeAt : Option Bool → PrimeIndex
  | none => ⟨2, Nat.prime_two⟩
  | some b => B.prime b

def site : (i : Option Bool) → Univariate.Site (B.primeAt i)
  | none => ⟨B.guardTwo, B.guardTwo_trans, none⟩
  | some b => ⟨(B.guard b).value, (B.guard b).transcendental, some (B.primary b)⟩

private theorem primeAt_injective : Function.Injective (fun i => (B.primeAt i).val) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b => exact False.elim ((B.odd b).ne h)
  | some b =>
    cases j with
    | none => exact False.elim ((B.odd b).ne h.symm)
    | some c =>
      cases b <;> cases c
      · rfl
      · exact False.elim (B.distinct (Subtype.ext h))
      · exact False.elim (B.distinct (Subtype.ext h.symm))
      · rfl

/-- The test prescription uses unit guard targets and positive primary
orders, independently chosen for both colours. -/
def target (orders : Bool → ℕ) (i : Option Bool) (branch : Bool) : ℚ_[(B.primeAt i).val] :=
  if branch then 1 else ((B.primeAt i).val : ℚ_[(B.primeAt i).val]) ^ (i.elim 0 orders)

/-- One shifted-Eisenstein numerator meets the arithmetic constraints at all
three primes, all signed words, and all geometric tests for the same prefix. -/
theorem simultaneous_choice {oldE : ℕ → ℕ} (plan : ConstructionWords.DegreePlan n P oldE)
    (hP : ∀ j < n, (P j).Monic) (orders : Bool → ℕ) (precision : Option Bool → Bool → ℕ) :
    ∃ ell : PrimeIndex, (∀ i, (B.primeAt i).val ≠ ell.val) ∧
      Nonempty (MixedConstructionWords.Choice (fun i => (B.primeAt i).val)
        (fun i => (B.site i).paired) ell.val plan (fun i => (B.site i).branch)
        (B.target orders) precision) := by
  classical
  let primes := (Finset.univ : Finset (Option Bool)).image B.primeAt
  obtain ⟨ell, _, hell⟩ := GuardStages.exists_fresh_prime primes 2
  have hfresh (i : Option Bool) : (B.primeAt i).val ≠ ell.val := by
    intro h
    exact hell (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Subtype.ext h⟩)
  refine ⟨ell, hfresh, MixedConstructionWords.choice_nonempty _ _ _ _ _ _ _
    B.primeAt_injective hfresh hP (fun i => (B.site i).branch_transcendental)
    (fun i => (B.site i).branch_ne) ?_⟩
  intro i b _
  have hp : ((B.primeAt i).val : ℚ_[(B.primeAt i).val]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (B.primeAt i).property.ne_zero
  cases b <;> simp [target, hp]

end ThreeSites

/-- End-to-end finite client on the actual recursive prefix. The irreducible
old polynomials have degree at least five and hence avoid both centres. Their
stored support certificates exclude all coefficient denominators. -/
theorem prefix_three_site_choice {n : ℕ} (P : RecursivePrefix.Prefix n)
    (avoid : Finset PrimeIndex) (bound k₀ k₁ : ℕ) (hk₀ : 0 < k₀) (hk₁ : 0 < k₁)
    (orders : Bool → ℕ) (precision : Option Bool → Bool → ℕ) :
    ∃ (B : ThreeSites n P.rawAt k₀ k₁)
      (plan : ConstructionWords.DegreePlan n P.rawAt P.exponentAt) (ell : PrimeIndex),
      (∀ b, bound < (B.prime b).val ∧ B.prime b ∉ P.state.assignment.primes ∧
        B.prime b ∉ avoid) ∧
      (∀ i, (B.primeAt i).val ≠ ell.val) ∧
      Nonempty (MixedConstructionWords.Choice (fun i => (B.primeAt i).val)
        (fun i => (B.site i).paired) ell.val plan (fun i => (B.site i).branch)
        (B.target orders) precision) := by
  have hsupp (j : ℕ) (hj : j < n) (i : ℕ) (p : PrimeIndex)
      (hd : p.val ∣ ((P.rawAt j).coeff i).den) : p ∈ P.state.assignment.primes := by
    rw [P.rawAt_lt j hj] at hd
    exact P.assigned_subset _ ((P.batch ⟨j,hj⟩).processed_subset_assigned (P.raw_support _ i p hd))
  have hnroot (c : ℚ) (j : ℕ) (hj : j < n) : (P.rawAt j).eval c ≠ 0 := by
    rw [P.rawAt_lt j hj]
    exact (P.irreducible _).not_isRoot_of_natDegree_ne_one (by have := P.degree_five ⟨j,hj⟩; omega)
  obtain ⟨B, hB⟩ := exists_three_sites P.rawAt P.state.assignment avoid bound k₀ k₁ hk₀ hk₁
    P.rawAt_monic hsupp (hnroot 0) (hnroot 1)
  obtain ⟨plan⟩ := ConstructionWords.degreePlan_nonempty n P.rawAt P.exponentAt P.rawAt_monic
  obtain ⟨ell, hell, hchoice⟩ := B.simultaneous_choice plan P.rawAt_monic orders precision
  exact ⟨B, plan, ell, hB, hell, hchoice⟩

/-- Horizontal order at a rational centre, obtained by translating the
canonical numerator and denominator. -/
def orderAt (c : ℚ) (f : RatFunc ℚ) : ℤ :=
  ((taylor c f.num).natTrailingDegree : ℤ) - (taylor c f.denom).natTrailingDegree

@[simp] theorem orderAt_zero (f : RatFunc ℚ) : orderAt 0 f = PrimaryStabilization.tOrder f := by
  simp [orderAt, PrimaryStabilization.tOrder]

/-- Primary evaluation of a fixed rational function stabilizes at its
horizontal order on any translated centre. An exceptional finite prefix of
displacement orders is allowed. -/
theorem eventually_order_at (c : ℚ) (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hinj : Function.Injective p) (α : ∀ n, ℚ_[p n])
    (ht : ∀ n, Transcendental ℚ (α n))
    (hv : ∀ᶠ n in Filter.atTop, (α n - (c : ℚ_[p n])).valuation = 1)
    (f : RatFunc ℚ) (hf : f ≠ 0) :
    ∀ᶠ n in Filter.atTop, (EvaluationDVR.evaluationHom (p n) (α n) (ht n) f).valuation =
      orderAt c f := by
  filter_upwards [hv, PrimaryStabilization.eventually_rational_coefficient_units p
    (fun _ => Fact.out) hinj (taylor c f.num),
    PrimaryStabilization.eventually_rational_coefficient_units p
      (fun _ => Fact.out) hinj (taylor c f.denom)] with n hval hnum hden
  have eval (g : ℚ[X]) : aeval (α n - (c : ℚ_[p n])) (taylor c g) = aeval (α n) g := by
    simp [taylor_apply, aeval_comp]
  have h₁ := PrimaryStabilization.padic_aeval_eq_exp_neg_natTrailingDegree (p n) _
    ((taylor_eq_zero c f.num).not.mpr (RatFunc.num_ne_zero hf)) _ hval hnum
  have h₂ := PrimaryStabilization.padic_aeval_eq_exp_neg_natTrailingDegree (p n) _
    ((taylor_eq_zero c f.denom).not.mpr f.denom_ne_zero) _ hval hden
  rw [eval] at h₁ h₂
  let e := EvaluationDVR.evaluationHom (p n) (α n) (ht n)
  have hne : e f ≠ 0 := (map_ne_zero_iff e e.injective).mpr hf
  have h : Padic.mulValuation (e f) = WithZero.exp (-(orderAt c f)) := by
    change Padic.mulValuation (LocalEvaluation.evalAt (α n) (ht n) f) = _
    rw [LocalEvaluation.evalAt_apply, map_div₀, h₁, h₂, ← WithZero.exp_sub]
    congr 1
    dsimp only [orderAt]
    omega
  simp only [Padic.mulValuation_toFun, hne, ite_false] at h
  exact neg_injective (WithZero.exp_injective h)

end UnconditionalCounterexample.Variations.UnivariateCentres
