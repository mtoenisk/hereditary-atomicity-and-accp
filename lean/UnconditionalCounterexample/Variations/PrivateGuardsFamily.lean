import UnconditionalCounterexample.Variations.PrivateGuardsPair
import UnconditionalCounterexample.Variations.PrivateGuardsSeedExistence
import UnconditionalCounterexample.Variations.PrivateGuardsSchedule

/-!
# The punctured fibre and its private places on one field

The places used to detect an auxiliary exponent are attached to the very
same irreducibles inverted to control the dimension. At stage n the finite
list includes all earlier punctures as well as the external tests.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open MvPolynomial GuardSupport DiscreteOrders WithZero

variable {r d : ℕ}
local notation "A" => PolynomialRing (r+1)
local notation "K" => FractionRing (PolynomialRing (r+1))

def frozenTests {L : Type*} [DecidableEq L] (test : ℕ → Finset L) (G : ℕ → L) (n : ℕ) :
    Finset L := test n ∪ (Finset.range n).image G

structure Family (c : Fin (r+1) → ℚ) (d : ℕ) (main : Set A) (test : ℕ → Finset A) where
  puncture : ℕ → A
  irreducible : ∀ n, Irreducible (puncture n)
  retained : ∀ n, puncture n ∉ (coordinatePrime c d).asIdeal
  fresh : ∀ n j, j < n → ¬ puncture n ∣ puncture j
  meets : ∀ P : PrimeSpectrum A, P.asIdeal.height = (d+1 : ℕ) → ∃ n, puncture n ∈ P.asIdeal
  dimension : ringKrullDim (Localization (inverted main puncture)) = d
  prime : ℕ → PrimeIndex
  prime_increasing : StrictMono (fun n => (prime n).val)
  sites : ∀ n, Pair (prime n) (puncture n) (frozenTests test puncture n)

variable {c : Fin (r+1) → ℚ} {main : Set (PolynomialRing (r+1))} {test : ℕ → Finset (PolynomialRing (r+1))}

def Family.places (F : Family c d main test) :
    Places (fun n => algebraMap A K (F.puncture n)) where
  ordinary n := place _ _ (F.sites n).ordinary_independent
  auxiliary n := place _ _ (F.sites n).private_independent
  private_self n := (F.sites n).detects_self.1
  ordinary_self n := (F.sites n).detects_self.2
  private_earlier n j hj := ((F.sites n).tests_are_units (Finset.mem_union_right _
    (Finset.mem_image_of_mem F.puncture (Finset.mem_range.mpr (show j < n from hj))))).1
  ordinary_earlier n j hj := ((F.sites n).tests_are_units (Finset.mem_union_right _
    (Finset.mem_image_of_mem F.puncture (Finset.mem_range.mpr (show j < n from hj))))).2

theorem Family.same_constant (F : Family c d main test) (n : ℕ) (q : ℚ) :
    F.places.auxiliary n (q : K) = F.places.ordinary n (q : K) := by
  let e : K →+* ℚ_[(F.prime n).val] := IndependentTuples.evaluation _ (F.sites n).private_independent
  let f : K →+* ℚ_[(F.prime n).val] := IndependentTuples.evaluation _ (F.sites n).ordinary_independent
  exact congrArg (Padic.mulValuation (p := (F.prime n).val))
    ((map_ratCast e q).trans (map_ratCast f q).symm)

theorem Family.finite_support (F : Family c d main test)
    (hcover : ∀ f : A, f ≠ 0 → ∃ n, ∀ j ≥ n, f ∈ test j) (x : K) (hx : x ≠ 0) :
    {j | F.places.auxiliary j x ≠ 1 ∨ F.places.ordinary j x ≠ 1}.Finite := by
  obtain ⟨f,g,hg,rfl⟩ := IsFractionRing.div_surjective A x
  have hf : f ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨nf, hnf⟩ := hcover _ hf
  obtain ⟨ng, hng⟩ := hcover _ (nonZeroDivisors.ne_zero hg)
  refine (Finset.range (max nf ng)).finite_toSet.subset ?_
  intro j hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra! h
  have hfv := (F.sites j).tests_are_units
    (Finset.mem_union_left _ (hnf j ((le_max_left _ _).trans h)))
  have hgv := (F.sites j).tests_are_units
    (Finset.mem_union_left _ (hng j ((le_max_right _ _).trans h)))
  rcases hj with hp | ho
  · apply hp
    rw [map_div₀, show F.places.auxiliary j _ = 1 from hfv.1,
      show F.places.auxiliary j _ = 1 from hgv.1, div_one]
  · apply ho
    rw [map_div₀, show F.places.ordinary j _ = 1 from hfv.2,
      show F.places.ordinary j _ = 1 from hgv.2, div_one]

/-- Build a single punctured fibre and all of its actual valuations from the
finite fresh-prime smooth-point theorem. -/
theorem family_of_smooth_seeds (hd : 1 ≤ d) (hr : d < r+1) (c : Fin (r+1) → ℚ)
    (main : Set A) (hm : ∀ f ∈ main, f ∉ (coordinatePrime c d).asIdeal)
    (test : ℕ → Finset A) (ht : ∀ n f, f ∈ test n → f ≠ 0)
    (seed : ∀ (g : A), Irreducible g → ∀ (S : Finset A), (∀ f ∈ S, ¬ g ∣ f) →
      ∀ N : ℕ, ∃ p : PrimeIndex, N < p.val ∧ Nonempty (SmoothSeed p g S)) :
    Nonempty (Family c d main test) := by
  classical
  let H (n : ℕ) := ∏ f ∈ test n, f
  obtain ⟨G, hG, hprev, hmeet, hdim⟩ := exists_punctured_fibre hd hr c H
    (fun n => Finset.prod_ne_zero_iff.mpr (ht n)) main hm
  let S := frozenTests test G
  have havoid (n : ℕ) (f : A) (hf : f ∈ S n) : ¬ G n ∣ f := by
    rcases Finset.mem_union.mp hf with hp | hp
    · exact fun h => (hG n).2.2 n le_rfl (h.trans (Finset.dvd_prod_of_mem id hp))
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      exact hprev n k (Finset.mem_range.mp hk)
  let T (n : ℕ) := Σ p : PrimeIndex, Pair p (G n) (S n)
  have hex (n N : ℕ) : ∃ v : T n, N < v.1.val := by
    obtain ⟨p,hp,⟨s⟩⟩ := seed _ (hG n).1 _ (havoid n) N
    obtain ⟨b⟩ := s.realize
    exact ⟨⟨p,b⟩,hp⟩
  choose step hs using hex
  let seq (n : ℕ) : T n := Nat.rec (motive := T) (step 0 0) (fun k v => step (k+1) v.1.val) n
  exact ⟨⟨G, fun n => (hG n).1, fun n => (hG n).2.1, hprev, hmeet, hdim,
    fun n => (seq n).1, strictMono_nat_of_lt_succ (fun n => hs _ (seq n).1.val), fun n => (seq n).2⟩⟩

/-- The auxiliary irreducibles cut the generic fibre down to the required dimension and have
private/ordinary valuation difference exactly one. -/
theorem exists_family (hd : 1 ≤ d) (hr : d < r+1) (c : Fin (r+1) → ℚ)
    (main : Set A) (hm : ∀ f ∈ main, f ∉ (coordinatePrime c d).asIdeal)
    (test : ℕ → Finset A) (ht : ∀ n f, f ∈ test n → f ≠ 0) :
    Nonempty (Family c d main test) :=
  family_of_smooth_seeds hd hr c main hm test ht exists_smoothSeed

/-- Include both the chronological list of main factors and an exhaustive
list of nonzero rational polynomials in the private tests. All older main
factors are units at each new pair and every fraction has finite support
over the paired guards. -/
theorem exists_exhaustive_family (hd : 1 ≤ d) (hr : d < r+1) (c : Fin (r+1) → ℚ)
    (raw : ℕ → A) (hne : ∀ j, raw j ≠ 0) (hm : ∀ j, raw j ∉ (coordinatePrime c d).asIdeal) :
    ∃ (tests : ℕ → Finset A) (F : Family c d (Set.range raw) tests),
      (∀ n j, j ≤ n → F.places.auxiliary n (algebraMap A K (raw j)) = 1 ∧
        F.places.ordinary n (algebraMap A K (raw j)) = 1) ∧
      (∀ x : K, x ≠ 0 →
        {j | F.places.auxiliary j x ≠ 1 ∨ F.places.ordinary j x ≠ 1}.Finite) := by
  classical
  let : Countable A := Function.Injective.countable
    (f := fun f : A => AddMonoidAlgebra.coeff f) (fun _ _ h => congrArg AddMonoidAlgebra.ofCoeff h)
  let : Nonempty {f : A // f ≠ 0} := ⟨⟨1,one_ne_zero⟩⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat {f : A // f ≠ 0}
  let tests (n : ℕ) := (Finset.range (n+1)).image (fun j => (enum j).val) ∪
    (Finset.range (n+1)).image raw
  obtain ⟨F⟩ := exists_family hd hr c (Set.range raw) (by rintro _ ⟨j,rfl⟩; exact hm j)
    tests (by
      intro n f hf
      rcases Finset.mem_union.mp hf with he | he
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
        exact (enum j).property
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
        exact hne j)
  refine ⟨tests, F, fun n j hj => (F.sites n).tests_are_units (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))), ?_⟩
  apply F.finite_support
  intro f hf
  obtain ⟨n, he⟩ := henum ⟨f,hf⟩
  exact ⟨n, fun j hj => Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨n, Finset.mem_range.mpr (by omega), congrArg Subtype.val he⟩)⟩

end UnconditionalCounterexample.Variations.PrivateGuards
