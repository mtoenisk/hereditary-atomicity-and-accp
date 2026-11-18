import UnconditionalCounterexample.ProfileCriterion
import Factorization.Bounds

/-!
# Exact order-one atom counts in conductor subrings

Proposition 7.2 counts the factors of order one. Actual conductor splitting excludes intrinsic
subring atoms of order greater than one. Additivity then counts order-one atom
occurrences in every factorization multiset, including repeated factors and
an arbitrary associated unit. Every other factor has order zero.

The final valuation-profile theorem derives late divisibility from the
specified a_n profiles. The actual domain, integer conductor, profile laws
and return congruences remain explicit inputs. Atomicity or an atom-order
bound is not assumed in order to prove the count.
-/

namespace UnconditionalCounterexample

universe u v
variable {R : Type u} [CommRing R]

/-- Actual conductor splitting excludes atoms of order greater than one.
Both factors lie in the subring and have positive order, so neither is a unit. -/
theorem order_le_one_of_irreducible_conductor_splitting
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m * z ∈ T)
    (ord : R → ℕ) (hunit : ∀ z : R, IsUnit z → ord z = 0)
    (hmul : ∀ a b : R, a ≠ 0 → b ≠ 0 → ord (a * b) = ord a + ord b)
    (hsplit : ∀ x : R, x ∈ T → x ≠ 0 → 2 ≤ ord x →
      ∃ a b : R, x = a * b ∧ ord a = 1 ∧ m ∣ a - 1)
    {x : T} (hx : Irreducible x) : ord (x : R) ≤ 1 := by
  by_contra hhigh
  have hxzero : (x : R) ≠ 0 := fun h => hx.ne_zero (Subtype.ext h)
  obtain ⟨a, b, hxab, haord, hacong⟩ := hsplit x x.property hxzero (by omega)
  have habzero : a * b ≠ 0 := by rwa [← hxab]
  have ha0 := left_ne_zero_of_mul habzero
  have hb0 := right_ne_zero_of_mul habzero
  have haT : a ∈ T := mem_subring_of_conductor_dvd_sub_one T m hconductor hacong
  have hbT : b ∈ T := cofactor_mem_subring_of_conductor T m hconductor
    (hxab ▸ x.property) hacong
  let aT : T := ⟨a, haT⟩
  let bT : T := ⟨b, hbT⟩
  have heq : x = aT * bT := Subtype.ext hxab
  have hsum : ord (x : R) = 1 + ord b := by rw [hxab, hmul a b ha0 hb0, haord]
  rcases hx.isUnit_or_isUnit heq with h | h
  · have hz := hunit a (h.map T.subtype)
    omega
  · have hz := hunit b (h.map T.subtype)
    omega

/-- Construction-facing atom-order bound from one late divisor sequence and
its congruences modulo the same ambient conductor. -/
theorem order_le_one_of_irreducible_conductor_and_late_divisors
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m * z ∈ T)
    (ord : R → ℕ) (hunit : ∀ z : R, IsUnit z → ord z = 0)
    (hmul : ∀ a b : R, a ≠ 0 → b ≠ 0 → ord (a * b) = ord a + ord b)
    (a : ℕ → R) (haord : ∀ n, ord (a n) = 1)
    (hdiv : ∀ x : R, x ≠ 0 → 2 ≤ ord x → ∃ N : ℕ, ∀ n ≥ N, a n ∣ x)
    (hcongr : ∀ N : ℕ, ∃ n ≥ N, m ∣ a n - 1)
    {x : T} (hx : Irreducible x) : ord (x : R) ≤ 1 := by
  apply order_le_one_of_irreducible_conductor_splitting T m hconductor ord hunit hmul ?_ hx
  intro y _ hy hhigh
  obtain ⟨N, hN⟩ := hdiv y hy hhigh
  obtain ⟨n, hn, hcong⟩ := hcongr N
  obtain ⟨b, hb⟩ := hN n hn
  exact ⟨a n, b, hb, haord n, hcong⟩

/-- For values in {0,1}, the sum counts the occurrences with value one,
including multiplicities. -/
theorem filter_card_eq_sum_of_le_one {M : Type*} (ord : M → ℕ)
    (factors : Multiset M) (hsmall : ∀ a ∈ factors, ord a ≤ 1) :
    (factors.filter (fun a => ord a = 1)).card = (factors.map ord).sum := by
  induction factors using Multiset.induction_on with
  | empty => simp
  | @cons a factors ih =>
    have ha := hsmall a (Multiset.mem_cons_self a factors)
    have htail := ih (fun b hb => hsmall b (Multiset.mem_cons_of_mem hb))
    by_cases haone : ord a = 1
    · simp only [Multiset.filter_cons_of_pos (p := fun b => ord b = 1) _ haone, Multiset.card_cons,
        Multiset.map_cons, Multiset.sum_cons, haone]
      omega
    · have hazero : ord a = 0 := by omega
      simp only [Multiset.filter_cons_of_neg (p := fun b => ord b = 1) _ haone, Multiset.map_cons,
        Multiset.sum_cons, hazero, zero_add]
      exact htail

/-- Exact order-one atom count in a conductor-containing subring. This is a
statement about every factorization, so atomicity need not be assumed. -/
theorem factor_count_of_conductor_and_late_divisors
    (T : Subring R) (m : R) (hconductor : ∀ z : R, m * z ∈ T)
    (ord : R → ℕ) (hunit : ∀ z : R, IsUnit z → ord z = 0)
    (hmul : ∀ a b : R, a ≠ 0 → b ≠ 0 → ord (a * b) = ord a + ord b)
    (a : ℕ → R) (haord : ∀ n, ord (a n) = 1)
    (hdiv : ∀ x : R, x ≠ 0 → 2 ≤ ord x → ∃ N : ℕ, ∀ n ≥ N, a n ∣ x)
    (hcongr : ∀ N : ℕ, ∃ n ≥ N, m ∣ a n - 1)
    {x : T} (hx : x ≠ 0) (factors : Multiset T)
    (hatoms : ∀ z ∈ factors, Irreducible z) (hfac : Associated factors.prod x) :
    (factors.filter (fun z : T => ord (z : R) = 1)).card = ord (x : R) ∧
      ∀ z ∈ factors, ord (z : R) ≠ 1 → ord (z : R) = 0 := by
  have hsmall : ∀ z ∈ factors, ord (z : R) ≤ 1 := by
    intro z hz
    exact order_le_one_of_irreducible_conductor_and_late_divisors T m hconductor
      ord hunit hmul a haord hdiv hcongr (hatoms z hz)
  have hunitT : ∀ z : T, IsUnit z → ord (z : R) = 0 :=
    fun z hz => hunit z (hz.map T.subtype)
  have hmulT : ∀ z w : T, z ≠ 0 → w ≠ 0 →
      ord ((z * w : T) : R) = ord (z : R) + ord (w : R) := by
    intro z w hz hw
    exact hmul z w (fun h => hz (Subtype.ext h)) (fun h => hw (Subtype.ext h))
  constructor
  · rw [filter_card_eq_sum_of_le_one (fun z : T => ord (z : R)) factors hsmall]
    exact Factorization.sum_degree_eq_of_associated (fun z : T => ord (z : R))
      hunitT hmulT hx factors hfac
  · intro z hz hne
    have h := hsmall z hz
    omega

namespace ValuationProfiles

variable {ι : Type v} [IsDomain R]

/-- Paper §7.2 expressed in the actual valuation-profile interface. Late
divisibility is derived from the prescribed a_n profiles and coordinatewise
divisibility; it is not an additional factorization assumption. -/
theorem factor_count_of_integer_conductor (v : ValuationProfiles R ι)
    (hdivisibility : ∀ x y : R, x ≠ 0 → y ≠ 0 →
      (∀ p, v.value p x ≤ v.value p y) → x ∣ y)
    (a : ℕ → R) (ha : ∀ n, a n ≠ 0)
    (halimit : ∀ n, v.value .limit (a n) = 1)
    (haoutside : ∀ n i, v.value (.outside i) (a n) = 0)
    (haprimary : ∀ n j, (v.value (.primary j) (a n) : ℤ) = primaryAtomProfile n j)
    (T : Subring R) (m : ℕ) (hconductor : ∀ z : R, (m : R) * z ∈ T)
    (hcongr : ∀ N : ℕ, ∃ n ≥ N, (m : R) ∣ a n - 1)
    {x : T} (hx : x ≠ 0) (factors : Multiset T)
    (hatoms : ∀ z ∈ factors, Irreducible z) (hfac : Associated factors.prod x) :
    (factors.filter (fun z : T => v.value .limit (z : R) = 1)).card = v.value .limit (x : R) ∧
      ∀ z ∈ factors, v.value .limit (z : R) ≠ 1 → v.value .limit (z : R) = 0 := by
  apply factor_count_of_conductor_and_late_divisors T (m : R) hconductor
    (v.value .limit) (v.value_unit .limit) (v.value_mul .limit) a halimit
    ?_ hcongr hx factors hatoms hfac
  intro y hy hhigh
  exact v.eventually_dvd_of_primaryAtomProfiles hdivisibility a ha halimit haoutside haprimary
    hy hhigh

end ValuationProfiles

end UnconditionalCounterexample
