import UnconditionalCounterexample.Variations.PrivateGuardsChronology

/-!
# Permanent private places of the joint construction

Both the dimension-cutting factors and the main polynomials are taken from
the same chronological selection. An old main polynomial is a unit by the
new pair's tests. A later normalized main generator is a unit by the
neighbourhood prescribed at the already frozen pair.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport DiscreteOrders MultivariateSelection WithZero

variable {r d : ℕ} {c : Fin (r+1) → ℚ} {M : ℕ → Type*}

/-- The height targets and the independent enumeration of polynomial tests. -/
structure Config (r d : ℕ) where
  positive : 1 ≤ d
  bound : d < r+1
  target : ℕ → PrimeSpectrum (Poly r)
  height : ∀ n, (target n).asIdeal.height = (d+1 : ℕ)
  covers : ∀ P : PrimeSpectrum (Poly r), P.asIdeal.height = (d+1 : ℕ) → ∃ n, target n = P
  tests : ℕ → Finset (Poly r)
  nonzero : ∀ n f, f ∈ tests n → f ≠ 0
  seed_test : ∀ n, X 0 ∈ tests n
  exhaustive : ∀ f : Poly r, f ≠ 0 → ∃ n, ∀ j ≥ n, f ∈ tests j

/-- Every admissible small dimension admits such enumerations. -/
theorem config_exists (hd : 1 ≤ d) (hr : d < r+1) : Nonempty (Config r d) := by
  classical
  let A := Poly r
  let : Countable A := Function.Injective.countable
    (f := fun f : A => AddMonoidAlgebra.coeff f) (fun _ _ h => congrArg AddMonoidAlgebra.ofCoeff h)
  have hf : Function.Surjective (fun S : Finset A => Ideal.span (S : Set A)) :=
    fun I => I.fg_of_isNoetherianRing
  let : Countable (Ideal A) := hf.countable
  let : Countable (PrimeSpectrum A) := Function.Injective.countable
    (f := PrimeSpectrum.asIdeal) (fun _ _ h => PrimeSpectrum.ext h)
  let target := {P : PrimeSpectrum A // P.asIdeal.height = (d+1 : ℕ)}
  let : Nonempty target := ⟨⟨coordinatePrime (0 : Fin (r+1) → ℚ) (d+1), coordinate_height _ _ hr⟩⟩
  let : Nonempty {f : A // f ≠ 0} := ⟨⟨1,one_ne_zero⟩⟩
  obtain ⟨t,hT⟩ := exists_surjective_nat target
  obtain ⟨e,hE⟩ := exists_surjective_nat {f : A // f ≠ 0}
  refine ⟨⟨hd,hr,fun j => (t j).val,fun j => (t j).property,?_,
    fun j => insert (X 0) ((Finset.range (j+1)).image (fun i => (e i).val)),?_,
    fun _ => Finset.mem_insert_self ..,?_⟩⟩
  · intro P hp
    obtain ⟨j,hj⟩ := hT ⟨P,hp⟩
    exact ⟨j,congrArg Subtype.val hj⟩
  · intro j f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact X_ne_zero _
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
      exact (e i).property
  · intro f hf
    obtain ⟨j,hj⟩ := hE ⟨f,hf⟩
    exact ⟨j,fun k hk => Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j,Finset.mem_range.mpr (by omega),congrArg Subtype.val hj⟩)⟩

variable (C : Config r d) (L : Rule r M c)

private theorem small (n : ℕ) : (coordinatePrime c d).asIdeal.height < (C.target n).asIdeal.height := by
  rw [C.height,coordinate_height c d C.bound.le]
  exact_mod_cast Nat.lt_succ_self d

private theorem large (n : ℕ) : 1 < (C.target n).asIdeal.height := by
  rw [C.height]
  exact_mod_cast (show 1 < d+1 by have := C.positive; omega)

abbrev event (n : ℕ) := round L C.target (coordinatePrime c d) (small C (c := c)) (large C)
  C.tests C.nonzero n
abbrev main (n : ℕ) := (event C L n).entry.raw n
abbrev puncture (n : ℕ) := (event C L n).puncture
abbrev prime (n : ℕ) := (event C L n).prime
abbrev before (n : ℕ) : History r M n := fun j => event C L j.val

theorem accepted (n : ℕ) :
    Accepted L (C.target n) (coordinatePrime c d).asIdeal (C.tests n) (before C L n) (event C L n) :=
  round_accepted L C.target (coordinatePrime c d) (small C (c := c)) (large C) C.tests C.nonzero n

private theorem old_mem {n j : ℕ} (hj : j < n) :
    main C L j ∈ (event C L n).checked ∧ puncture C L j ∈ (event C L n).checked := by
  classical
  rw [(accepted C L n).checked_eq]
  let i : Fin n := ⟨j,hj⟩
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))),
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)))⟩

private theorem main_mem {n j : ℕ} (hj : j ≤ n) : main C L j ∈ (event C L n).checked := by
  rcases eq_or_lt_of_le hj with rfl | h
  · rw [(accepted C L j).checked_eq]
    exact Finset.mem_insert_self ..
  · exact (old_mem C L h).1

private theorem frozen_subset (n : ℕ) :
    frozenTests C.tests (puncture C L) n ⊆ (event C L n).checked := by
  classical
  intro f hf
  rcases Finset.mem_union.mp hf with h | h
  · rw [(accepted C L n).checked_eq]
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    exact (old_mem C L (Finset.mem_range.mp hj)).2

private theorem avoids_coordinate {f : Poly r} (hc : eval c f ≠ 0) :
    f ∉ (coordinatePrime c d).asIdeal := by
  have he : (eval c).comp (specializeCoordinates c d) = eval c := by
    ext a
    · simp [specializeCoordinates]
    · by_cases ha : (a : ℕ) < d <;> simp [specializeCoordinates,ha]
  intro h
  change specializeCoordinates c d f = 0 at h
  apply hc
  rw [← DFunLike.congr_fun he f,RingHom.comp_apply,h,map_zero]

private theorem main_retained (n : ℕ) : main C L n ∉ (coordinatePrime c d).asIdeal :=
  avoids_coordinate (accepted C L n).survives

theorem seed_mem (n : ℕ) : X 0 ∈ (event C L n).checked := by
  rw [(accepted C L n).checked_eq]
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (C.seed_test n))

theorem puncture_not_dvd_seed (n : ℕ) : ¬ puncture C L n ∣ X 0 :=
  (accepted C L n).avoids_tests _ (seed_mem C L n)

private theorem increasing : StrictMono (fun n => (prime C L n).val) := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply (accepted C L (n+1)).prime_gt
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨⟨n,by omega⟩,Finset.mem_univ _,Finset.mem_insert_self ..⟩)

/-- The dimension-d fibre is built from the very same mutually chosen main
and auxiliary lists, and the private primes are the primes of those rounds. -/
def family : Family c d (Set.range (main C L)) C.tests := by
  classical
  let G := puncture C L
  let M₀ := inverted (Set.range (main C L)) G
  let Q := coordinatePrime c d
  have hret : M₀ ≤ Q.asIdeal.primeCompl := by
    apply Submonoid.closure_le.mpr
    rintro _ (⟨n,rfl⟩ | ⟨n,rfl⟩)
    · exact main_retained C L n
    · exact (accepted C L n).avoids_retained
  have hmeet (P : PrimeSpectrum (Poly r)) (hP : P.asIdeal.height = (d+1 : ℕ)) :
      ∃ n, G n ∈ P.asIdeal := by
    obtain ⟨n,rfl⟩ := C.covers P hP
    exact ⟨n,(accepted C L n).punctures⟩
  refine ⟨G,fun n => (event C L n).irreducible_puncture,fun n => (accepted C L n).avoids_retained,
    fun n j hj => (accepted C L n).avoids_tests _ (old_mem C L hj).2,hmeet,?_,
    prime C L,increasing C L,?_⟩
  · apply dimension_eq_of_punctured c d C.bound.le M₀ (Localization M₀)
      (Set.disjoint_left.mpr fun _ hx => hret hx)
    intro P hP
    obtain ⟨n,hn⟩ := hmeet P hP
    exact ⟨⟨G n,Submonoid.subset_closure (Or.inr ⟨n,rfl⟩)⟩,hn⟩
  · intro n
    let s := (event C L n).pair
    exact ⟨s.privately,s.ordinarily,s.private_independent,s.ordinary_independent,s.distinct,
      s.private_norm,s.ordinary_norm,fun f hf => s.private_tests f (frozen_subset C L n hf),
      fun f hf => s.ordinary_tests f (frozen_subset C L n hf)⟩

theorem finite_support (x : FractionRing (Poly r)) (hx : x ≠ 0) :
    {j | (family C L).places.auxiliary j x ≠ 1 ∨ (family C L).places.ordinary j x ≠ 1}.Finite :=
  (family C L).finite_support C.exhaustive x hx

private theorem generator_eq (n : ℕ) :
    (family C L).generator mixedPower n =
      algebraMap (Poly r) (FractionRing (Poly r)) (main C L n) /
        algebraMap (Poly r) (FractionRing (Poly r)) (oldDenominator (before C L n)) := by
  unfold Family.generator normalizedMain oldDenominator
  simp only [map_prod,map_pow,map_mul]
  congr 1
  exact (Fin.prod_univ_eq_prod_range (fun j =>
    (algebraMap (Poly r) (FractionRing (Poly r)) (main C L j) *
     algebraMap (Poly r) (FractionRing (Poly r)) (puncture C L j)) ^ mixedPower n) n).symm

private theorem unit_normalized {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (F G : ℕ → K) (E : ℕ → ℕ) (n : ℕ) (hF : ∀ j ≤ n, v (F j) = 1)
    (hG : ∀ j < n, v (G j) = 1) : v (normalizedMain F G E n) = 1 := by
  rw [normalizedMain,map_div₀,hF n le_rfl,map_prod]
  have h : (∏ j ∈ Finset.range n, v ((F j * G j) ^ E n)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hlt := Finset.mem_range.mp hj
    rw [map_pow,map_mul,hF j hlt.le,hG j hlt,one_mul,one_pow]
  rw [h,div_one]

/-- Every normalized main generator is an actual unit at both guards of
every round, including each guard born before that generator. -/
theorem generator_units (n j : ℕ) :
    (family C L).places.auxiliary n ((family C L).generator mixedPower j) = 1 ∧
      (family C L).places.ordinary n ((family C L).generator mixedPower j) = 1 := by
  let F := family C L
  let s := (event C L n).pair
  by_cases hj : j ≤ n
  · have hmain (k : ℕ) (hk : k ≤ j) := s.tests_are_units (main_mem C L (hk.trans hj))
    have haux (k : ℕ) (hk : k < j) := s.tests_are_units (old_mem C L (hk.trans_le hj)).2
    exact ⟨unit_normalized (F.places.auxiliary n) _ _ mixedPower j
        (fun k hk => (hmain k hk).1) (fun k hk => (haux k hk).1),
      unit_normalized (F.places.ordinary n) _ _ mixedPower j
        (fun k hk => (hmain k hk).2) (fun k hk => (haux k hk).2)⟩
  · have hu := (accepted C L j).prior_units ⟨n, by omega⟩
    rw [generator_eq, map_div₀, map_div₀]
    change place _ _ s.private_independent _ / place _ _ s.private_independent _ = 1 ∧
      place _ _ s.ordinary_independent _ / place _ _ s.ordinary_independent _ = 1
    simp only [place_polynomial, ← map_div₀]
    exact ⟨mulValuation_eq_one_of_norm_eq_one _ (hu false),
      mulValuation_eq_one_of_norm_eq_one _ (hu true)⟩

/-- Vanishing of the paired orders leaves an actual pole-algebra unit as a
scalar times a signed main word, without any hypothesis on main valuations. -/
theorem pole_unit_elimination (u : ((family C L).poleAlgebra (fun n => (event C L n).irreducible))ˣ)
    (he : ∀ n, order ((family C L).places.auxiliary n)
      (((u : (family C L).poleAlgebra _) : FractionRing (Poly r))) =
      order ((family C L).places.ordinary n) (((u : (family C L).poleAlgebra _) : FractionRing (Poly r)))) :
    ∃ q : ℚ, q ≠ 0 ∧ ∃ a : ℕ →₀ ℤ, (((u : (family C L).poleAlgebra _) : FractionRing (Poly r))) =
      (q : FractionRing (Poly r)) * PrincipalProfiles.word ((family C L).generator mixedPower) a :=
  (family C L).unit_main_word _ mixedPower u (generator_units C L) he

end UnconditionalCounterexample.Variations.PrivateGuards.Live
