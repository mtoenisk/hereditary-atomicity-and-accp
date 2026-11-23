import UnconditionalCounterexample.Variations.MultivariateSelectionModels
import UnconditionalCounterexample.RawWords

/-!
# The chronological triangular word list

Choose the normalization exponent before the stage polynomial. Every word
with the stage's bounded previous exponents and a positive latest exponent
has an explicit polynomial denominator containing every prior raw factor.
This same list determines both the degree and finite tests of the selector.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open RawWords MvPolynomial GuardSupport

abbrev BoundedWord (n : ℕ) := StageWord n (n+1)

private def prior {n : ℕ} (h : ∀ i < n, ℕ) (i : ℕ) := if hi : i < n then h i hi else 0

private theorem exponent_congr {E E' : ℕ → ℕ} (c : ℕ → ℤ) (n : ℕ) (h : ∀ i < n, E i = E' i)
    (j : ℕ) : earlierRawExponent E c n j = earlierRawExponent E' c n j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [earlierRawExponent]
    rw [ih (fun i hi => h i (by omega)),h n (by omega)]

private theorem exists_bound (n : ℕ) (E : ℕ → ℕ) : ∃ a : ℕ, 0 < a ∧ ∀ w : BoundedWord n, ∀ i < n,
    earlierRawExponent E w.oldExponent n i < (a*w.latestExponent : ℕ) := by
  obtain ⟨a,ha,hw⟩ := exists_common_denominator_power (Finset.univ : Finset (BoundedWord n)) (Finset.range n)
    (fun w => earlierRawExponent E w.oldExponent n) StageWord.latestExponent (fun w _ => w.latestExponent_bounds.1)
  exact ⟨a,ha,fun w i hi => hw w (Finset.mem_univ _) i (Finset.mem_range.mpr hi)⟩

def normalizationPower (n : ℕ) : ℕ :=
  Nat.strongRecOn n (fun i old => (exists_bound i (prior old)).choose)

private theorem power_spec (n : ℕ) : 0 < normalizationPower n ∧ ∀ w : BoundedWord n, ∀ j < n,
    earlierRawExponent normalizationPower w.oldExponent n j < (normalizationPower n * w.latestExponent : ℕ) := by
  let E := prior (n := n) (fun j _ => normalizationPower j)
  have he : normalizationPower n = (exists_bound n E).choose := Nat.strongRecOn_eq _ _
  obtain ⟨ha,h⟩ := (exists_bound n E).choose_spec
  refine ⟨he ▸ ha,fun w j hj => ?_⟩
  rw [exponent_congr w.oldExponent n (E' := E) (fun i hi => by simp [E,prior,hi]) j, he]
  exact h w j hj

def denominatorPower {n : ℕ} (w : BoundedWord n) (j : ℕ) :=
  denominatorExponent (normalizationPower n) w.latestExponent (earlierRawExponent normalizationPower w.oldExponent n j)

theorem denominatorPower_pos {n : ℕ} (w : BoundedWord n) {j : ℕ} (hj : j < n) :
    0 < denominatorPower w j := denominatorExponent_pos ((power_spec n).2 w j hj)

def denominator {A : Type*} [CommMonoid A] {n : ℕ} (P : ℕ → A) (w : BoundedWord n) : A :=
  ∏ j ∈ Finset.range n, P j ^ denominatorPower w j

theorem dvd_denominator {A : Type*} [CommMonoid A] {n : ℕ} (P : ℕ → A) (w : BoundedWord n) {j : ℕ} (hj : j<n) :
    P j ∣ denominator P w :=
  (dvd_pow_self _ (denominatorPower_pos w hj).ne').trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj))

theorem denominator_mem_closure {A : Type*} [CommMonoid A] {n : ℕ} (P : ℕ → A) (w : BoundedWord n) :
    denominator P w ∈ Submonoid.closure (Set.range P) :=
  Submonoid.prod_mem _ (fun j _ => Submonoid.pow_mem _ (Submonoid.subset_closure (show P j ∈ Set.range P from ⟨j,rfl⟩)) _)

theorem word_eq_fraction {A L : Type*} [CommRing A] [Field L] (f : A →+* L)
    (P : ℕ → A) (hP : ∀ i, f (P i) ≠ 0) {n : ℕ} (w : BoundedWord n) :
    let g := RawWords.normalizedFactor (fun j => f (P j)) normalizationPower
    g n ^ w.latestExponent * (∏ j ∈ Finset.range n, g j ^ w.oldExponent j) =
      f (P n ^ w.latestExponent) / f (denominator P w) := by
  dsimp only
  rw [normalized_factors_expand _ _ _ _ (fun j _ => hP j)]
  simpa only [RawWords.normalizedFactor,denominator,denominatorPower,map_pow,map_prod] using
    normalized_word_eq_single_numerator (Finset.range n) (fun j => f (P j)) (fun j _ => hP j)
      (normalizationPower n) w.latestExponent (earlierRawExponent normalizationPower w.oldExponent n)
      (fun j hj => ((power_spec n).2 w j (Finset.mem_range.mp hj)).le) (f (P n))

variable {r : ℕ} {M : ℕ → Type*} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

private def rawPrefix {n : ℕ} (h : History r M n) (j : ℕ) : Poly r :=
  if hj : j < n then (h ⟨j,hj⟩).raw j else 0

def triangularWords (n : ℕ) (h : History r M n) : Finset (ℕ × Poly r) := by
  classical exact Finset.univ.image (fun w : BoundedWord n => (w.latestExponent, denominator (rawPrefix h) w))

theorem triangularWords_pos (n : ℕ) (h : History r M n) (w : ℕ × Poly r) (hw : w ∈ triangularWords n h) :
    0 < w.1 := by
  classical
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hw
  exact u.latestExponent_bounds.1

theorem triangular_denominator_ne_zero {E : Type*} [Field E] (f : Poly r →+* E) {n : ℕ}
    (h : History r M n) (hF : ∀ j : Fin n, f ((h j).raw j.val) ≠ 0) (w : ℕ × Poly r)
    (hw : w ∈ triangularWords n h) : f w.2 ≠ 0 := by
  classical
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hw
  simp only [denominator,map_prod,map_pow]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by simpa only [rawPrefix,dite_eq_left (Finset.mem_range.mp hj)] using hF ⟨j,Finset.mem_range.mp hj⟩)

/-- Arithmetic site input alone determines the triangular finite word lists
and certified degrees and tests. -/
def withTriangularWords (R : Requirements r M K) : Requirements r M K :=
  { R with words := triangularWords, word_pos := triangularWords_pos }

theorem normalized_word_listed (R : Requirements r M K) {n : ℕ} (w : BoundedWord n) :
    (w.latestExponent, denominator (raw (withTriangularWords R)) w) ∈ words (withTriangularWords R) n := by
  classical
  let S := withTriangularWords R
  have hd : denominator (rawPrefix (fun j : Fin n => chain S j.val)) w = denominator (raw S) w := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [rawPrefix, Finset.mem_range.mp hj, dite_true, raw]
  exact Finset.mem_image.mpr ⟨w,Finset.mem_univ _,Prod.ext rfl hd⟩

/-- The actual signed product in the field of fractions, formed from the
stage's normalized raw factors. -/
def normalizedWord {A L : Type*} [CommRing A] [Field L] (f : A →+* L)
    (P : ℕ → A) {n : ℕ} (w : BoundedWord n) : L :=
  let g := RawWords.normalizedFactor (fun j => f (P j)) normalizationPower
  g n ^ w.latestExponent * (∏ j ∈ Finset.range n, g j ^ w.oldExponent j)

/-- An infinite set of actual normalized words in the specified subalgebra
recovers the full multivariate pole algebra of the chronological sequence. -/
theorem recover_of_normalized_words (R : Requirements r M K)
    (hp : Function.Surjective R.point) (hP : Function.Surjective R.primesEnumeration)
    (B : Type*) [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra (Poly r) B]
    [IsScalarTower ℚ (Poly r) B] [IsLocalization (Submonoid.closure (Set.range (raw (withTriangularWords R)))) B]
    (L : Type*) [Field L] (φ : B →+* L) (hφ : Function.Injective φ) (A : Subalgebra ℚ B)
    (hwords : {n | ∃ (w : BoundedWord n) (x : A), φ (x : B) =
      normalizedWord (φ.comp (algebraMap (Poly r) B)) (raw (withTriangularWords R)) w}.Infinite) :
    A = ⊤ := by
  classical
  let S := withTriangularWords R
  let F := raw S
  let D := Submonoid.closure (Set.range F)
  let G := (D.map (MvPolynomial.map (algebraMap ℚ K)))
  let E := Localization G
  let f := φ.comp (algebraMap (Poly r) B)
  have hreg : D ≤ nonZeroDivisors (Poly r) := by
    apply Submonoid.closure_le.mpr
    rintro t ⟨i,rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (raw_irreducible S i).ne_zero
  have hin : Function.Injective f := hφ.comp (IsLocalization.injective B hreg)
  have hn (i : ℕ) : f (F i) ≠ 0 := (map_ne_zero_iff _ hin).mpr (raw_irreducible S i).ne_zero
  apply MultivariateListedWords.recover_of_stageTests F (MultivariateInfinity.vandermondeForm (r+1))
    (fun n => (chain S n).degree) (words S) R.point hp R.primesEnumeration hP R.fixed B E A
    (vandermonde_degree r) (raw_shape S) _ (stage_tests S)
  · intro j
    apply Set.infinite_of_forall_exists_gt
    intro b
    obtain ⟨n,⟨w,x,hx⟩,hngt⟩ := hwords.exists_gt (max b j)
    let H := denominator F w
    have hHw := normalized_word_listed R w
    have hH : f H ≠ 0 := by
      simp only [H,denominator,map_prod,map_pow]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hn i))
    have hr : φ (x : B) = f (F n ^ w.latestExponent) / f H :=
      hx.trans (word_eq_fraction f F hn w)
    refine ⟨n,⟨w.latestExponent,H,x,hHw,denominator_mem_closure F w,word_degree S n hHw,
      dvd_denominator F w ((le_max_right b j).trans_lt hngt),?_⟩,(le_max_left b j).trans_lt hngt⟩
    apply hφ
    have he := ((eq_div_iff hH).mp hr).symm
    simpa only [f,RingHom.comp_apply,map_pow,map_mul,mul_comm] using he
  · intro t ht j
    exact MultivariateInfinity.vandermondeForm_spans (r+1) t (by simpa using ht) j

end UnconditionalCounterexample.MultivariateSelection
