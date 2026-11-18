import UnconditionalCounterexample.GuardResidues
import UnconditionalCounterexample.GuardSupport
import UnconditionalCounterexample.CoefficientApproximation
import Mathlib.Algebra.Polynomial.Lifts
import UnconditionalCounterexample.EvaluationChoices
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite guard choices for the common construction

A bound on degrees and leading coefficients at one stage permits the next guard
residue to avoid the reductions of the prescribed polynomials. Supported denominators
give integral models at the unassigned primes.

The linear root bound selects an allowed residue and the p-adic lifting theorem
selects an actual transcendental unit. Finite assignments store birth stages and
are extended without changing any earlier argument. Stage zero uses residue one,
so it includes the small primes. The fresh auxiliary prime separately avoids
both zero and one; its guard can be inserted into the same finite assignment.

The later polynomial approximation and the full simultaneous successor remain
separate. These lemmas do not define a second independent guard recursion.
-/

namespace UnconditionalCounterexample.GuardStages

open Polynomial

/-- Any modulus larger than the absolute value of a nonzero integer preserves
its nonzero image. Primality is unnecessary for this reduction fact. -/
theorem intCast_ne_zero_of_natAbs_lt {a : ℤ} {p : ℕ}
    (ha : a ≠ 0) (hp : a.natAbs < p) : (a : ZMod p) ≠ 0 := by
  intro hz
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz
  have hl := Int.natAbs_le_of_dvd_ne_zero hd ha
  exact (not_le_of_gt hp) (by simpa using hl)

/-- Bounding the nonzero leading coefficient preserves nonzero reduction. -/
theorem map_ne_zero_of_leadingCoeff_natAbs_lt {U : ℤ[X]} {p : ℕ}
    (hU : U ≠ 0) (hp : U.leadingCoeff.natAbs < p) :
    U.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  have hc : (U.leadingCoeff : ZMod p) ≠ 0 :=
    intCast_ne_zero_of_natAbs_lt (leadingCoeff_ne_zero.mpr hU) hp
  intro hz
  have heq := congrArg (fun Q : (ZMod p)[X] => Q.coeff U.natDegree) hz
  exact hc (by simpa using heq)

/-- Under the same coefficient bound, natural degree is preserved exactly. -/
theorem natDegree_map_eq_of_leadingCoeff_natAbs_lt {U : ℤ[X]} {p : ℕ}
    (hU : U ≠ 0) (hp : U.leadingCoeff.natAbs < p) :
    (U.map (Int.castRingHom (ZMod p))).natDegree = U.natDegree := by
  exact natDegree_map_of_leadingCoeff_ne_zero _
    (intCast_ne_zero_of_natAbs_lt (leadingCoeff_ne_zero.mpr hU) hp)

/-- A finite leading-coefficient cutoff simultaneously preserves every listed
nonzero integer polynomial and its degree. -/
theorem finite_family_reduction {J : Type*} (I : Finset J) (U : J → ℤ[X]) {p : ℕ}
    (hU : ∀ j ∈ I, U j ≠ 0)
    (hp : I.sup (fun j => (U j).leadingCoeff.natAbs) < p) :
    ∀ j ∈ I, (U j).map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      ((U j).map (Int.castRingHom (ZMod p))).natDegree = (U j).natDegree := by
  intro j hj
  have hc : (U j).leadingCoeff.natAbs < p := (Finset.le_sup hj).trans_lt hp
  exact ⟨map_ne_zero_of_leadingCoeff_natAbs_lt (hU j hj) hc,
    natDegree_map_eq_of_leadingCoeff_natAbs_lt (hU j hj) hc⟩

/-- A linear degree bound leaves a residue different from 0 and 1 and away
from all listed polynomial roots. -/
theorem exists_residue_avoiding_zero_one
    {p : ℕ} [Fact p.Prime] {J : Type*}
    (I : Finset J) (P : J → (ZMod p)[X])
    (hP : ∀ j ∈ I, P j ≠ 0)
    (hp : (∑ j ∈ I, (P j).natDegree) + 2 < p) :
    ∃ w : ZMod p, w ≠ 0 ∧ w ≠ 1 ∧ ∀ j ∈ I, (P j).eval w ≠ 0 := by
  classical
  let Q : (ZMod p)[X] := X * (X - C 1) * ∏ j ∈ I, P j
  have hprod : (∏ j ∈ I, P j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hP
  have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero X_ne_zero (X_sub_C_ne_zero 1)) hprod
  have hdeg : Q.natDegree < p := by
    have h1 : ((X * (X - C (1 : ZMod p))) * ∏ j ∈ I, P j).natDegree ≤
        (X * (X - C (1 : ZMod p))).natDegree + (∏ j ∈ I, P j).natDegree :=
      natDegree_mul_le
    have h2 : ((X : (ZMod p)[X]) * (X - C 1)).natDegree ≤
        (X : (ZMod p)[X]).natDegree + (X - C (1 : ZMod p)).natDegree := natDegree_mul_le
    have h3 := natDegree_prod_le I P
    simp only [natDegree_X, natDegree_X_sub_C] at h2
    dsimp [Q]
    omega
  have hex : ∃ w : ZMod p, Q.eval w ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hQ (eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q Function.injective_id hn
      (by simpa using hdeg))
  obtain ⟨w, hw⟩ := hex
  have hm : w * (w - 1) * (∏ j ∈ I, (P j).eval w) ≠ 0 := by
    simpa only [Q, eval_mul, eval_X, eval_sub, eval_C, eval_prod] using hw
  refine ⟨w, ?_, ?_, ?_⟩
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hm).1).1
  · exact sub_ne_zero.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hm).1).2
  · exact Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hm).2

/-- A nonzero finite-field residue has a transcendental p-adic integer lift. -/
theorem exists_transcendental_lift {p : ℕ} [Fact p.Prime]
    (w : ZMod p) (hw : w ≠ 0) :
    ∃ β : ℤ_[p], Transcendental ℚ β.val ∧ IsUnit β ∧ PadicInt.toZMod β = w := by
  have hnotdvd : ¬ p ∣ w.val := by
    simpa only [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val] using hw
  obtain ⟨β, ht, hu, hr, _⟩ :=
    EvaluationChoices.exists_transcendental_unit_residue p w.val hnotdvd
  exact ⟨β, ht, hu, hr.trans (ZMod.natCast_zmod_val w)⟩

open GuardSupport

/-- At a large new prime, simultaneously avoid all old monic raw factors and
the specified initial segment of the integer polynomial enumeration. -/
theorem exists_guard_for_finite_stage
    {p : ℕ} [Fact p.Prime] {J : Type*}
    (I : Finset J) (F : J → ℤ_[p][X]) (hF : ∀ j ∈ I, (F j).Monic)
    (U : ℕ → NonzeroIntPolynomial) (i : ℕ)
    (hcoeff : ∀ j < i, (U j).val.leadingCoeff.natAbs < p)
    (hsize : (∑ j ∈ I, (F j).natDegree) +
      (∑ j ∈ Finset.range i, (U j).val.natDegree) + 2 < p) :
    ∃ β : ℤ_[p], Transcendental ℚ β.val ∧ IsUnit β ∧
      PadicInt.toZMod β ≠ 1 ∧
      (∀ j ∈ I, IsUnit ((F j).eval β)) ∧
      ∀ j < i, (U j).val.eval₂ (Int.castRingHom (ZMod p)) (PadicInt.toZMod β) ≠ 0 := by
  classical
  let P : J ⊕ ℕ → (ZMod p)[X] := Sum.elim
    (fun j => (F j).map PadicInt.toZMod)
    (fun j => (U j).val.map (Int.castRingHom (ZMod p)))
  have hP : ∀ j ∈ I.disjSum (Finset.range i), P j ≠ 0 := by
    intro j hj
    cases j with
    | inl j => exact ((hF j (Finset.inl_mem_disjSum.mp hj)).map PadicInt.toZMod).ne_zero
    | inr j =>
      exact map_ne_zero_of_leadingCoeff_natAbs_lt (U j).property
        (hcoeff j (Finset.mem_range.mp (Finset.inr_mem_disjSum.mp hj)))
  have hdeg : (∑ j ∈ I.disjSum (Finset.range i), (P j).natDegree) =
      (∑ j ∈ I, (F j).natDegree) + (∑ j ∈ Finset.range i, (U j).val.natDegree) := by
    rw [Finset.sum_disjSum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      exact (hF j hj).natDegree_map PadicInt.toZMod
    · apply Finset.sum_congr rfl
      intro j hj
      exact natDegree_map_eq_of_leadingCoeff_natAbs_lt (U j).property
        (hcoeff j (Finset.mem_range.mp hj))
  obtain ⟨w, hw0, hw1, hw⟩ := exists_residue_avoiding_zero_one
    (I.disjSum (Finset.range i)) P hP (by simpa only [hdeg] using hsize)
  obtain ⟨β, ht, hu, hr⟩ := exists_transcendental_lift w hw0
  refine ⟨β, ht, hu, hr ▸ hw1, ?_, ?_⟩
  · intro j hj
    apply (padicInt_isUnit_iff_toZMod_ne_zero _).mpr
    have hav := hw (Sum.inl j) (Finset.inl_mem_disjSum.mpr hj)
    change ((F j).map PadicInt.toZMod).eval w ≠ 0 at hav
    rw [← hr, eval_map, eval₂_at_apply] at hav
    exact hav
  · intro j hj
    have hav := hw (Sum.inr j) (Finset.inr_mem_disjSum.mpr (Finset.mem_range.mpr hj))
    simpa only [P, Sum.elim_inr, eval_map, hr] using hav

/-- The explicit previous-stage cutoff controls both coefficient survival and
root counting for the next prefix. -/
def guardCutoff (U : ℕ → NonzeroIntPolynomial) (i D : ℕ) : ℕ :=
  max ((Finset.range i).sup (fun j => (U j).val.leadingCoeff.natAbs))
    (D + (∑ j ∈ Finset.range i, (U j).val.natDegree) + 2)

theorem guardCutoff_bounds (U : ℕ → NonzeroIntPolynomial) (i D p : ℕ)
    (hp : guardCutoff U i D < p) :
    (∀ j < i, (U j).val.leadingCoeff.natAbs < p) ∧
      D + (∑ j ∈ Finset.range i, (U j).val.natDegree) + 2 < p := by
  refine ⟨?_, (le_max_right _ _).trans_lt hp⟩
  intro j hj
  exact (Finset.le_sup (Finset.mem_range.mpr hj)).trans_lt
    ((le_max_left _ _).trans_lt hp)

/-- Euclid's theorem supplies an auxiliary prime beyond a cutoff and outside
all already assigned primes. -/
theorem exists_fresh_prime (S : Finset PrimeIndex) (B : ℕ) :
    ∃ ell : PrimeIndex, B < ell.val ∧ ell ∉ S := by
  classical
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max B (S.sup Subtype.val) + 1)
  refine ⟨⟨p, hprime⟩, ?_, ?_⟩
  · change B < p
    have := le_max_left B (S.sup Subtype.val)
    omega
  · intro hmem
    have hsup := Finset.le_sup (f := fun q : PrimeIndex => q.val) hmem
    change p ≤ S.sup Subtype.val at hsup
    have := le_max_right B (S.sup Subtype.val)
    omega

/-- A guard remembers its assignment stage and the exact finite avoidance
condition needed for eventual guard support. -/
structure ScheduledGuard (U : ℕ → NonzeroIntPolynomial) (p : PrimeIndex) where
  value : ℤ_[p.val]
  transcendental : Transcendental ℚ value.val
  unit : IsUnit value
  birth : ℕ
  avoids : ∀ j < birth,
    (U j).val.eval₂ (Int.castRingHom (ZMod p.val)) (PadicInt.toZMod value) ≠ 0

/-- A finite assignment consists of actual guards, not only residue predicates. -/
structure Assignment (U : ℕ → NonzeroIntPolynomial) where
  primes : Finset PrimeIndex
  guard : (p : PrimeIndex) → p ∈ primes → ScheduledGuard U p

/-- At stage zero residue one is available at every prime, including two. -/
theorem exists_initialGuard (U : ℕ → NonzeroIntPolynomial) (p : PrimeIndex) :
    ∃ g : ScheduledGuard U p, g.birth = 0 ∧ PadicInt.toZMod g.value = 1 := by
  obtain ⟨β, ht, hu, hr⟩ := exists_transcendental_lift (1 : ZMod p.val) one_ne_zero
  exact ⟨⟨β, ht, hu, 0, by intro j hj; omega⟩, rfl, hr⟩

/-- Initialize any finite set of primes with no enumeration exclusions. -/
theorem exists_initial_assignment (U : ℕ → NonzeroIntPolynomial) (S : Finset PrimeIndex) :
    ∃ A : Assignment U, A.primes = S ∧
      ∀ p (hp : p ∈ A.primes), (A.guard p hp).birth = 0 := by
  classical
  let g (p : PrimeIndex) := (exists_initialGuard U p).choose
  refine ⟨⟨S, fun p _ => g p⟩, rfl, ?_⟩
  intro p hp
  exact (exists_initialGuard U p).choose_spec.1

/-- Extend a finite assignment by supplied actual guards, retaining every old
argument lying in the target set and its stored birth stage literally. -/
noncomputable def Assignment.extend {U : ℕ → NonzeroIntPolynomial}
    (A : Assignment U) (T : Finset PrimeIndex)
    (g : (p : PrimeIndex) → p ∈ T → p ∉ A.primes → ScheduledGuard U p) : Assignment U := by
  classical
  exact ⟨T, fun p hp => if hold : p ∈ A.primes then A.guard p hold else g p hp hold⟩

@[simp] theorem Assignment.extend_primes {U : ℕ → NonzeroIntPolynomial}
    (A : Assignment U) (T : Finset PrimeIndex) (g) : (A.extend T g).primes = T := rfl

theorem Assignment.extend_old {U : ℕ → NonzeroIntPolynomial}
    (A : Assignment U) (T : Finset PrimeIndex) (g)
    (p : PrimeIndex) (hp : p ∈ A.primes) (hpT : p ∈ T) :
    (A.extend T g).guard p hpT = A.guard p hp := by
  simp only [Assignment.extend, dite_eq_left hp]

theorem Assignment.extend_new {U : ℕ → NonzeroIntPolynomial}
    (A : Assignment U) (T : Finset PrimeIndex) (g)
    (p : PrimeIndex) (hp : p ∉ A.primes) (hpT : p ∈ T) :
    (A.extend T g).guard p hpT = g p hpT hp := by
  simp only [Assignment.extend, dite_eq_right hp]

/-- The guard part of a large-prime successor: every old guard is retained,
and every newly assigned guard avoids earlier raws and the fixed prefix. -/
theorem exists_extension
    {J : Type*} (U : ℕ → NonzeroIntPolynomial) (A : Assignment U)
    (T : Finset PrimeIndex) (hAT : A.primes ⊆ T) (i D : ℕ)
    (I : Finset J) (F : (p : PrimeIndex) → J → ℤ_[p.val][X])
    (hF : ∀ p ∈ T, p ∉ A.primes → ∀ j ∈ I, (F p j).Monic)
    (hdegree : ∀ p ∈ T, p ∉ A.primes → (∑ j ∈ I, (F p j).natDegree) ≤ D)
    (hlarge : ∀ p ∈ T, p ∉ A.primes → guardCutoff U i D < p.val) :
    ∃ B : Assignment U, B.primes = T ∧ A.primes ⊆ B.primes ∧
      (∀ p (hp : p ∈ A.primes) (hpB : p ∈ B.primes), B.guard p hpB = A.guard p hp) ∧
      ∀ p (hp : p ∈ B.primes), p ∉ A.primes →
        (B.guard p hp).birth = i ∧ PadicInt.toZMod (B.guard p hp).value ≠ 1 ∧
        ∀ j ∈ I, IsUnit ((F p j).eval (B.guard p hp).value) := by
  classical
  have hex (p : PrimeIndex) (hp : p ∈ T) (hn : p ∉ A.primes) :
      ∃ g : ScheduledGuard U p, g.birth = i ∧ PadicInt.toZMod g.value ≠ 1 ∧
        ∀ j ∈ I, IsUnit ((F p j).eval g.value) := by
    obtain ⟨hc, hd⟩ := guardCutoff_bounds U i D p.val (hlarge p hp hn)
    obtain ⟨β, ht, hu, hr, hraw, hav⟩ := exists_guard_for_finite_stage I (F p)
      (hF p hp hn) U i hc (by have := hdegree p hp hn; omega)
    exact ⟨⟨β, ht, hu, i, hav⟩, rfl, hr, hraw⟩
  let g (p : PrimeIndex) (hp : p ∈ T) (hn : p ∉ A.primes) := (hex p hp hn).choose
  refine ⟨A.extend T g, rfl, hAT, ?_, ?_⟩
  · intro p hp hpB
    exact A.extend_old T g p hp hpB
  · intro p hp hn
    rw [A.extend_new T g p hn hp]
    exact (hex p hp hn).choose_spec

/-- The actual finite set of all rational primes through a natural cutoff. -/
def primesThrough (M : ℕ) : Finset PrimeIndex :=
  (Finset.range (M + 1)).subtype Nat.Prime

@[simp] theorem mem_primesThrough (p : PrimeIndex) (M : ℕ) :
    p ∈ primesThrough M ↔ p.val ≤ M := by
  simp only [primesThrough, Finset.mem_subtype, Finset.mem_range]
  omega

/-- If all primes through the previous cutoff were assigned, every new prime
satisfies the large-prime hypotheses for the current prefix. -/
theorem cutoff_lt_of_unassigned (U : ℕ → NonzeroIntPolynomial) (i D : ℕ)
    (S : Finset PrimeIndex) (hcovered : primesThrough (guardCutoff U i D) ⊆ S)
    (p : PrimeIndex) (hp : p ∉ S) : guardCutoff U i D < p.val := by
  by_contra hn
  exact hp (hcovered ((mem_primesThrough p _).mpr (by omega)))

/-- The finite prime-processing step includes the new cutoff and all finitely
many independently requested primary primes. -/
def nextPrimes {U : ℕ → NonzeroIntPolynomial} (A : Assignment U)
    (M : ℕ) (required : Finset PrimeIndex) : Finset PrimeIndex :=
  A.primes ∪ primesThrough M ∪ required

theorem subset_nextPrimes {U : ℕ → NonzeroIntPolynomial} (A : Assignment U)
    (M : ℕ) (required : Finset PrimeIndex) : A.primes ⊆ nextPrimes A M required := by
  intro p hp
  simp only [nextPrimes, Finset.mem_union]
  exact Or.inl (Or.inl hp)

theorem cutoff_subset_nextPrimes {U : ℕ → NonzeroIntPolynomial} (A : Assignment U)
    (M : ℕ) (required : Finset PrimeIndex) : primesThrough M ⊆ nextPrimes A M required := by
  intro p hp
  simp only [nextPrimes, Finset.mem_union]
  exact Or.inl (Or.inr hp)

/-- Cover a larger cutoff and a finite set of requests. The previous coverage
invariant supplies all finite-reduction bounds, and old guards are preserved. -/
theorem exists_stage_transition
    {J : Type*} (U : ℕ → NonzeroIntPolynomial) (A : Assignment U)
    (i D M : ℕ) (required : Finset PrimeIndex)
    (hcovered : primesThrough (guardCutoff U i D) ⊆ A.primes)
    (I : Finset J) (F : (p : PrimeIndex) → J → ℤ_[p.val][X])
    (hF : ∀ p ∉ A.primes, ∀ j ∈ I, (F p j).Monic)
    (hdegree : ∀ p ∉ A.primes, (∑ j ∈ I, (F p j).natDegree) ≤ D) :
    ∃ B : Assignment U, B.primes = nextPrimes A M required ∧
      A.primes ⊆ B.primes ∧
      (∀ p (hp : p ∈ A.primes) (hpB : p ∈ B.primes), B.guard p hpB = A.guard p hp) ∧
      ∀ p (hp : p ∈ B.primes), p ∉ A.primes →
        (B.guard p hp).birth = i ∧ PadicInt.toZMod (B.guard p hp).value ≠ 1 ∧
        ∀ j ∈ I, IsUnit ((F p j).eval (B.guard p hp).value) := by
  apply exists_extension U A (nextPrimes A M required) (subset_nextPrimes A M required)
    i D I F
  · intro p _ hn
    exact hF p hn
  · intro p _ hn
    exact hdegree p hn
  · intro p _ hn
    exact cutoff_lt_of_unassigned U i D A.primes hcovered p hn

/-- After the ordinary processing step, choose a fresh auxiliary prime and an
actual guard avoiding both zero and one, the prefix, and all old raw factors. -/
theorem exists_fresh_auxiliary_guard
    {J : Type*} (U : ℕ → NonzeroIntPolynomial) (A : Assignment U)
    (i D M : ℕ) (I : Finset J) (F : (p : PrimeIndex) → J → ℤ_[p.val][X])
    (hF : ∀ p ∉ A.primes, ∀ j ∈ I, (F p j).Monic)
    (hdegree : ∀ p ∉ A.primes, (∑ j ∈ I, (F p j).natDegree) ≤ D) :
    ∃ ell : PrimeIndex, ∃ g : ScheduledGuard U ell,
      M < ell.val ∧ ell ∉ A.primes ∧ g.birth = i ∧
      PadicInt.toZMod g.value ≠ 1 ∧ ∀ j ∈ I, IsUnit ((F ell j).eval g.value) := by
  obtain ⟨ell, hlarge, hfresh⟩ := exists_fresh_prime A.primes (max M (guardCutoff U i D))
  have hcutoff : guardCutoff U i D < ell.val := (le_max_right _ _).trans_lt hlarge
  obtain ⟨hc, hd⟩ := guardCutoff_bounds U i D ell.val hcutoff
  obtain ⟨β, ht, hu, hr, hraw, hav⟩ := exists_guard_for_finite_stage I (F ell)
    (hF ell hfresh) U i hc (by have := hdegree ell hfresh; omega)
  exact ⟨ell, ⟨β, ht, hu, i, hav⟩, (le_max_left _ _).trans_lt hlarge,
    hfresh, rfl, hr, hraw⟩

/-- A prior rational raw polynomial with supported coefficient denominators
has an actual integral polynomial model at every unassigned prime. -/
theorem exists_integral_polynomial_model
    {ι : Type*} (processed : ι → ℕ) (F : ℚ[X])
    (hsupp : ∀ n prime : ℕ, prime.Prime → prime ∣ (F.coeff n).den →
      ∃ k, prime = processed k)
    (p : ℕ) [Fact p.Prime] (hfresh : ∀ k, processed k ≠ p) :
    ∃ G : ℤ_[p][X], G.map (algebraMap ℤ_[p] ℚ_[p]) = F.map (algebraMap ℚ ℚ_[p]) ∧
      G.natDegree = F.natDegree ∧ (F.Monic → G.Monic) := by
  have hlift : F.map (algebraMap ℚ ℚ_[p]) ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro n
    obtain ⟨a, ha⟩ := CoefficientApproximation.exists_padicInt_of_denominator_support
      processed (F.coeff n) (hsupp n) p hfresh
    refine ⟨a, ?_⟩
    rw [coeff_map]
    exact ha
  obtain ⟨G, hG⟩ := (Polynomial.mem_lifts _).mp hlift
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) :=
    FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]
  refine ⟨G, hG, ?_, ?_⟩
  · rw [← natDegree_map_eq_of_injective hinj G, hG]
    exact natDegree_map_eq_of_injective (algebraMap ℚ ℚ_[p]).injective F
  · intro hF
    apply Polynomial.monic_of_injective hinj
    rw [hG]
    exact hF.map _

/-- Insert the selected auxiliary guard into the finite assignment. This is
separate from choosing it so the fresh-prime CRT step may use the same prime. -/
noncomputable def Assignment.insert {U : ℕ → NonzeroIntPolynomial}
    (A : Assignment U) (ell : PrimeIndex) (g : ScheduledGuard U ell) : Assignment U := by
  classical
  exact A.extend (Insert.insert ell A.primes) fun p hp hn => by
    have heq : p = ell := (Finset.mem_insert.mp hp).resolve_right hn
    subst p
    exact g

@[simp] theorem Assignment.insert_primes {U : ℕ → NonzeroIntPolynomial}
    (A : Assignment U) (ell : PrimeIndex) (g : ScheduledGuard U ell) :
    (A.insert ell g).primes = Insert.insert ell A.primes := rfl

theorem Assignment.insert_old {U : ℕ → NonzeroIntPolynomial}
    (A : Assignment U) (ell : PrimeIndex) (g : ScheduledGuard U ell)
    (p : PrimeIndex) (hp : p ∈ A.primes) :
    (A.insert ell g).guard p (Finset.mem_insert_of_mem hp) = A.guard p hp := by
  apply Assignment.extend_old

theorem Assignment.insert_fresh {U : ℕ → NonzeroIntPolynomial}
    (A : Assignment U) (ell : PrimeIndex) (g : ScheduledGuard U ell) (hell : ell ∉ A.primes) :
    (A.insert ell g).guard ell (Finset.mem_insert_self ell A.primes) = g := by
  simp only [Assignment.insert, Assignment.extend, dite_eq_right hell]

end UnconditionalCounterexample.GuardStages
