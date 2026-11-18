import Factorization.HereditaryHierarchy

/-!
# Atomicity of subrings containing a conductor

An additive order, bounded factorizations at low order, and congruences for late
order-one divisors give atomicity of subrings containing a conductor.
-/

namespace UnconditionalCounterexample

universe u

variable {R : Type u} [CommRing R]

/-- If all ambient units are signs, every unital subring reflects units. -/
theorem subring_isUnit_of_signUnits
    (hsigns : ∀ x : R, IsUnit x → x = 1 ∨ x = -1)
    (T : Subring R) (x : T) (hx : IsUnit (x : R)) : IsUnit x := by
  rcases hsigns x hx with h | h
  · have hxone : x = 1 := Subtype.ext h
    rw [hxone]
    exact isUnit_one
  · have hxneg : x = -1 := Subtype.ext h
    rw [hxneg]
    exact isUnit_neg_one

/-- A congruence to one modulo an ambient conductor puts the element itself
in the subring. No nonzero condition on the conductor is needed here. -/
theorem mem_subring_of_conductor_dvd_sub_one
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m * z ∈ T)
    {a : R} (ha : m ∣ a - 1) : a ∈ T := by
  obtain ⟨c, hc⟩ := ha
  have hsub : a - 1 ∈ T := hc ▸ hconductor c
  simpa only [sub_add_cancel] using T.add_mem hsub T.one_mem

/-- Dividing an element of a subring by an ambient divisor congruent to one
modulo the conductor leaves an element of the same subring. -/
theorem cofactor_mem_subring_of_conductor
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m * z ∈ T)
    {a b : R} (hab : a * b ∈ T) (ha : m ∣ a - 1) : b ∈ T := by
  obtain ⟨c, hc⟩ := ha
  have hdiff : a * b - b ∈ T := by
    have heq : a * b - b = m * (c * b) := by
      rw [← mul_assoc, ← hc, sub_mul, one_mul]
    rw [heq]
    exact hconductor (c * b)
  simpa only [sub_sub_cancel] using T.sub_mem hab hdiff

/-- Bounded ambient factorizations at low order descend to each subring as
soon as ambient units are reflected. -/
theorem subring_hasAtomicFactorization_of_lowOrderBound
    (T : Subring R) (ord : R → ℕ)
    (hunit : ∀ x : T, IsUnit (x : R) → IsUnit x)
    (hlow : ∀ z : R, z ≠ 0 → ord z ≤ 1 →
      Factorization.HasBoundedFactorizations z)
    (x : T) (hx : x ≠ 0) (hord : ord x ≤ 1) :
    Factorization.HasAtomicFactorization x := by
  apply Factorization.HasBoundedFactorizations.hasAtomicFactorization
  apply Factorization.hasBoundedFactorizations_of_unitReflectingMap
    T.subtype.toMonoidHom hunit
  exact hlow x (fun h => hx (Subtype.ext h)) hord

variable [IsDomain R]

/-- Strong induction on the actual order proves atomicity of a
conductor-containing subring. The splitting hypothesis asks for an ambient
order-one divisor with a conductor congruence, not for a factorization into
irreducibles. -/
theorem isAtomicDomain_of_conductor_splitting
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m * z ∈ T)
    (ord : R → ℕ)
    (hmul : ∀ a b : R, a ≠ 0 → b ≠ 0 → ord (a * b) = ord a + ord b)
    (hunit : ∀ x : T, IsUnit (x : R) → IsUnit x)
    (hlow : ∀ z : R, z ≠ 0 → ord z ≤ 1 →
      Factorization.HasBoundedFactorizations z)
    (hsplit : ∀ x : R, x ∈ T → x ≠ 0 → 2 ≤ ord x →
      ∃ a b : R, x = a * b ∧ ord a = 1 ∧ m ∣ a - 1) :
    Factorization.IsAtomicDomain T := by
  intro x hx
  generalize hn : ord (x : R) = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases hsmall : n ≤ 1
    · exact subring_hasAtomicFactorization_of_lowOrderBound
        T ord hunit hlow x hx (hn ▸ hsmall)
    · have hxzero : (x : R) ≠ 0 := fun h => hx (Subtype.ext h)
      obtain ⟨a, b, hxab, haord, hacong⟩ :=
        hsplit x x.property hxzero (by omega)
      have ha0 : a ≠ 0 := by
        intro h
        apply hxzero
        simpa only [h, zero_mul] using hxab
      have hb0 : b ≠ 0 := by
        intro h
        apply hxzero
        simpa only [h, mul_zero] using hxab
      have haT : a ∈ T := mem_subring_of_conductor_dvd_sub_one T m hconductor hacong
      have hbT : b ∈ T := cofactor_mem_subring_of_conductor
        T m hconductor (hxab ▸ x.property) hacong
      let aT : T := ⟨a, haT⟩
      let bT : T := ⟨b, hbT⟩
      have haT0 : aT ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
      have hbT0 : bT ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
      have hsum : n = 1 + ord b := by
        rw [← hn, hxab, hmul a b ha0 hb0, haord]
      have hbsmall : ord b < n := by omega
      have haatomic : Factorization.HasAtomicFactorization aT :=
        subring_hasAtomicFactorization_of_lowOrderBound
          T ord hunit hlow aT haT0 (by dsimp [aT]; omega)
      have hbatomic : Factorization.HasAtomicFactorization bT :=
        ih (ord b) hbsmall bT hbT0 rfl
      have heq : x = aT * bT := Subtype.ext hxab
      rw [heq]
      exact haatomic.mul hbatomic

/-- The construction-facing version uses one sequence of order-one elements:
each high-order top is divisible by every sufficiently late member, and
congruences to one occur arbitrarily late. -/
theorem isAtomicDomain_of_conductor_and_late_divisors
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m * z ∈ T)
    (ord : R → ℕ)
    (hmul : ∀ a b : R, a ≠ 0 → b ≠ 0 → ord (a * b) = ord a + ord b)
    (hunit : ∀ x : T, IsUnit (x : R) → IsUnit x)
    (hlow : ∀ z : R, z ≠ 0 → ord z ≤ 1 →
      Factorization.HasBoundedFactorizations z)
    (a : ℕ → R) (haord : ∀ n, ord (a n) = 1)
    (hdiv : ∀ x : R, x ≠ 0 → 2 ≤ ord x →
      ∃ N : ℕ, ∀ n ≥ N, a n ∣ x)
    (hcongr : ∀ N : ℕ, ∃ n ≥ N, m ∣ a n - 1) :
    Factorization.IsAtomicDomain T := by
  apply isAtomicDomain_of_conductor_splitting T m hconductor ord hmul hunit hlow
  intro x _ hx hord
  obtain ⟨N, hN⟩ := hdiv x hx hord
  obtain ⟨n, hn, hcong⟩ := hcongr N
  obtain ⟨b, hb⟩ := hN n hn
  exact ⟨a n, b, hb, haord n, hcong⟩

/-- The final hereditary assembly leaves the integer-conductor theorem as an
explicit input. Its proof does not assume that a subring is already atomic. -/
theorem hereditarilyAtomic_of_integerConductors
    (hsigns : ∀ x : R, IsUnit x → x = 1 ∨ x = -1)
    (ord : R → ℕ)
    (hmul : ∀ a b : R, a ≠ 0 → b ≠ 0 → ord (a * b) = ord a + ord b)
    (hlow : ∀ z : R, z ≠ 0 → ord z ≤ 1 →
      Factorization.HasBoundedFactorizations z)
    (a : ℕ → R) (haord : ∀ n, ord (a n) = 1)
    (hdiv : ∀ x : R, x ≠ 0 → 2 ≤ ord x →
      ∃ N : ℕ, ∀ n ≥ N, a n ∣ x)
    (hcongr : ∀ m : ℕ, 0 < m → ∀ N : ℕ,
      ∃ n ≥ N, (m : R) ∣ a n - 1)
    (hconductors : ∀ T : Subring R, ¬ Factorization.IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : R, (m : R) * z ∈ T) :
    Factorization.IsHereditarilyAtomic R := by
  intro T
  by_cases hBF : Factorization.IsBFDomain T
  · exact hBF.isAtomicDomain
  · obtain ⟨m, hm, hconductor⟩ := hconductors T hBF
    exact isAtomicDomain_of_conductor_and_late_divisors T m hconductor ord hmul
      (subring_isUnit_of_signUnits hsigns T) hlow a haord hdiv (hcongr m hm)

end UnconditionalCounterexample
