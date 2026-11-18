import UnconditionalCounterexample.ValuationProfiles
import UnconditionalCounterexample.NormalizedWords
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite divisors at horizontal order zero or one

Lemma 7.1 gives finitely many divisors up to associates at orders zero and one. The actual
domain's valuation laws, coordinate divisibility, and signed quotient-profile
representation remain explicit inputs. Divisors are first grouped by their
finite outside tuples; signed profile differences force uniform zero primary
tails. Finite profile codes then give finitely many associate classes, and
complementary factors cover order-one divisors.

The final lemmas also prove actual irreducibility of each element having the
prescribed a_n profile, including the initial profile for t. No atomicity,
bounded-factorization, or finite-divisor conclusion is assumed.
-/

namespace UnconditionalCounterexample.ValuationProfiles

universe u v
variable {R : Type u} {ι : Type v} [CommRing R] [IsDomain R]

/-- The additional signed-profile input furnished by a representation of
fractions with zero horizontal and outside profiles in the normalized generators.
No sign restriction is imposed on the primary difference. -/
def SignedDifferenceTriple (v : ValuationProfiles R ι) : Prop :=
  ∀ z u : R, z ≠ 0 → u ≠ 0 → v.value .limit z = 0 → v.value .limit u = 0 →
    (∀ i, v.value (.outside i) z = v.value (.outside i) u) →
    TripleCongruent (fun j => (v.value (.primary j) z : ℤ) - v.value (.primary j) u)

/-- Any signed normalized-word profile satisfies the overlapping triple
congruences, without effectiveness or support assumptions. -/
theorem tripleCongruent_of_represents {s u g : ℕ → ℤ}
    (h : NormalizedWords.Represents s u g) : TripleCongruent g := by
  constructor
  · have h0 := h.initial
    have h1 := h.odd 0
    norm_num at h1
    omega
  · intro n
    have h1 := h.odd n
    have h2 := h.even_succ n
    have h3 := h.odd (n + 1)
    have hi : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
    rw [hi] at h3
    omega

/-- The signed difference hypothesis follows from actual normalized-word
representations of quotient profiles. It does not assume finiteness of divisor
classes or eventual uniformity of their supports. -/
theorem signedDifferenceTriple_of_representations (v : ValuationProfiles R ι)
    (hrep : ∀ z u : R, z ≠ 0 → u ≠ 0 → v.value .limit z = 0 →
      v.value .limit u = 0 → (∀ i, v.value (.outside i) z = v.value (.outside i) u) →
      ∃ s q : ℕ → ℤ, NormalizedWords.Represents s q
        (fun j => (v.value (.primary j) z : ℤ) - v.value (.primary j) u)) :
    SignedDifferenceTriple v := by
  intro z u hz hu hzl hul hout
  obtain ⟨s, q, h⟩ := hrep z u hz hu hzl hul hout
  exact tripleCongruent_of_represents h

/-- In one fixed outside-profile class, a representative fixes a uniform
zero primary tail for all horizontal-order-zero divisors of a top of order ≤1. -/
theorem zero_tail_of_same_outside (v : ValuationProfiles R ι)
    (htriple : SignedDifferenceTriple v) {x u : R} (hx : x ≠ 0)
    (hxlimit : v.value .limit x ≤ 1) (hu : u ≠ 0) (hulimit : v.value .limit u = 0) :
    ∃ N : ℕ, ∀ z : R, z ∣ x → v.value .limit z = 0 →
      (∀ i, v.value (.outside i) z = v.value (.outside i) u) →
      ∀ j, N ≤ j → v.value (.primary j) z = 0 := by
  obtain ⟨Nx, hNx⟩ := v.eventually_primary x hx
  obtain ⟨Nu, hNu⟩ := v.eventually_primary u hu
  let k := max Nx Nu
  refine ⟨2 * k + 1, ?_⟩
  intro z hzx hzlimit houtside j hj
  have hz : z ≠ 0 := ne_zero_of_dvd_ne_zero hx hzx
  let g := fun l => (v.value (.primary l) z : ℤ) - v.value (.primary l) u
  have hgzero : EventuallyConstantProfile g 0 := by
    obtain ⟨Nz, hNz⟩ := v.eventually_primary z hz
    refine ⟨max Nz Nu, ?_⟩
    intro l hl
    dsimp [g]
    rw [hNz l (by omega), hNu l (by omega), hzlimit, hulimit]
    rfl
  have hsmall : ∀ l : ℕ, 2 * k + 1 ≤ l → 0 ≤ g l ∧ g l ≤ 1 := by
    intro l hl
    have hxu : Nx ≤ k := le_max_left _ _
    have huu : Nu ≤ k := le_max_right _ _
    have hle := v.value_le_of_dvd (.primary l) hx hzx
    rw [hNx l (by omega)] at hle
    dsimp [g]
    rw [hNu l (by omega), hulimit]
    simp only [Nat.cast_zero, sub_zero]
    exact ⟨Int.natCast_nonneg _, by omega⟩
  have hc := htriple z u hz hu hzlimit hulimit houtside
  have hgj := tail_eq_zero_of_triple_congruences g k hgzero hsmall
    (fun l _ => hc.2 l) j hj
  have huu : Nu ≤ k := le_max_right _ _
  dsimp [g] at hgj
  rw [hNu j (by omega), hulimit] at hgj
  omega

/-- Finitely many bounded outside tuples turn representative-dependent
primary cutoffs into one uniform cutoff for all order-zero divisors. -/
theorem uniform_zero_tail_for_zero_order_divisors (v : ValuationProfiles R ι)
    (htriple : SignedDifferenceTriple v) {x : R} (hx : x ≠ 0)
    (hxlimit : v.value .limit x ≤ 1) :
    ∃ N : ℕ, ∀ z : R, z ∣ x → v.value .limit z = 0 →
      ∀ j, N ≤ j → v.value (.primary j) z = 0 := by
  classical
  let I := {i : ι // v.value (.outside i) x ≠ 0}
  let : Fintype I := (v.finite_outside x hx).fintype
  let C := (i : I) → Fin (v.value (.outside i.val) x + 1)
  let Z := {z : R // z ∣ x ∧ v.value .limit z = 0}
  let code : Z → C := fun z i =>
    ⟨v.value (.outside i.val) z.val, by
      have hle := v.value_le_of_dvd (.outside i.val) hx z.property.1
      omega⟩
  have code_outside {z u : Z} (hcode : code z = code u) :
      ∀ i, v.value (.outside i) z.val = v.value (.outside i) u.val := by
    intro i
    by_cases hi : v.value (.outside i) x = 0
    · have hz := v.value_le_of_dvd (.outside i) hx z.property.1
      have hu := v.value_le_of_dvd (.outside i) hx u.property.1
      omega
    · exact congrArg Fin.val (congrFun hcode ⟨i, hi⟩)
  have hcutoff : ∀ c : C, ∃ N : ℕ,
      ∀ z : Z, code z = c → ∀ j, N ≤ j → v.value (.primary j) z.val = 0 := by
    intro c
    by_cases hc : ∃ u : Z, code u = c
    · obtain ⟨u, hu⟩ := hc
      have hunz : u.val ≠ 0 := ne_zero_of_dvd_ne_zero hx u.property.1
      obtain ⟨N, hN⟩ := v.zero_tail_of_same_outside htriple hx hxlimit hunz u.property.2
      refine ⟨N, ?_⟩
      intro z hz j hj
      exact hN z.val z.property.1 z.property.2 (code_outside (hz.trans hu.symm)) j hj
    · exact ⟨0, fun z hz => (hc ⟨z, hz⟩).elim⟩
  choose cutoff hcutoff using hcutoff
  let N := Finset.univ.sup cutoff
  refine ⟨N, ?_⟩
  intro z hzx hzlimit j hj
  let z' : Z := ⟨z, hzx, hzlimit⟩
  exact hcutoff (code z') z' rfl j
    ((Finset.le_sup (f := cutoff) (Finset.mem_univ (code z'))).trans hj)

/-- A finite code that determines an image gives a finite image even when
there can be infinitely many source representatives of one code. -/
theorem finite_range_of_finite_code {A B C : Type*} [Finite C]
    (f : A → B) (code : A → C)
    (hcode : ∀ a b, code a = code b → f a = f b) : (Set.range f).Finite := by
  have hfiber (c : C) : (f '' {a | code a = c}).Subsingleton := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hcode a b (ha.trans hb.symm)
  have hfinite : (⋃ c : C, f '' {a | code a = c}).Finite :=
    Set.finite_iUnion fun c => (hfiber c).finite
  apply hfinite.subset
  rintro _ ⟨a, rfl⟩
  exact Set.mem_iUnion.mpr ⟨code a, a, rfl, rfl⟩

/-- Order-zero divisors of a top of order at most one have finitely many
associate classes. Coordinate divisibility is a property of the actual domain;
the signed triple input is required also for nonintegral quotient profiles. -/
theorem finite_zero_order_divisor_classes (v : ValuationProfiles R ι)
    (htriple : SignedDifferenceTriple v)
    (hdivisibility : ∀ z u : R, z ≠ 0 → u ≠ 0 →
      (∀ p, v.value p z ≤ v.value p u) → z ∣ u)
    {x : R} (hx : x ≠ 0) (hxlimit : v.value .limit x ≤ 1) :
    (Associates.mk '' {z : R | z ∣ x ∧ v.value .limit z = 0}).Finite := by
  classical
  obtain ⟨N, hN⟩ := v.uniform_zero_tail_for_zero_order_divisors htriple hx hxlimit
  let outside : Finset ι := (v.finite_outside x hx).toFinset
  let indices : Finset (ProfilePlace ι) :=
    (Finset.range N).image ProfilePlace.primary ∪ outside.image ProfilePlace.outside
  let Z := {z : R // z ∣ x ∧ v.value .limit z = 0}
  let C := (p : indices) → Fin (v.value p.val x + 1)
  let code : Z → C := fun z p =>
    ⟨v.value p.val z.val, by
      have hle := v.value_le_of_dvd p.val hx z.property.1
      omega⟩
  have hcode : ∀ z u : Z, code z = code u → Associates.mk z.val = Associates.mk u.val := by
    intro z u heq
    have hcoordinate (p : ProfilePlace ι) (hp : p ∈ indices) :
        v.value p z.val = v.value p u.val :=
      congrArg Fin.val (congrFun heq ⟨p, hp⟩)
    have hall : ∀ p, v.value p z.val = v.value p u.val := by
      intro p
      cases p with
      | limit => exact z.property.2.trans u.property.2.symm
      | primary j =>
        by_cases hj : j < N
        · exact hcoordinate _ (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩))
        · rw [hN z.val z.property.1 z.property.2 j (by omega),
            hN u.val u.property.1 u.property.2 j (by omega)]
      | outside i =>
        by_cases hi : i ∈ outside
        · exact hcoordinate _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
        · have hix : v.value (.outside i) x = 0 := by
            simpa only [outside, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
          have hz := v.value_le_of_dvd (.outside i) hx z.property.1
          have hu := v.value_le_of_dvd (.outside i) hx u.property.1
          omega
    have hz := ne_zero_of_dvd_ne_zero hx z.property.1
    have hu := ne_zero_of_dvd_ne_zero hx u.property.1
    apply Associates.mk_eq_mk_iff_associated.mpr
    exact associated_of_dvd_dvd
      (hdivisibility z.val u.val hz hu (fun p => (hall p).le))
      (hdivisibility u.val z.val hu hz (fun p => (hall p).ge))
  have hfinite := finite_range_of_finite_code (fun z : Z => Associates.mk z.val) code hcode
  convert hfinite using 1
  ext a
  constructor
  · rintro ⟨z, hz, heq⟩
    exact ⟨⟨z, hz⟩, heq⟩
  · rintro ⟨z, heq⟩
    exact ⟨z.val, z.property, heq⟩

/-- Complementary factors exchange the remaining order-one divisor classes
with order-zero classes. Hence low-order tops have finitely many divisors up
to associates, rather than just bounded decomposition lengths. -/
theorem finite_divisor_classes_of_limit_le_one (v : ValuationProfiles R ι)
    (htriple : SignedDifferenceTriple v)
    (hdivisibility : ∀ z u : R, z ≠ 0 → u ≠ 0 →
      (∀ p, v.value p z ≤ v.value p u) → z ∣ u)
    {x : R} (hx : x ≠ 0) (hxlimit : v.value .limit x ≤ 1) :
    (Associates.mk '' {z : R | z ∣ x}).Finite := by
  classical
  let S := Associates.mk '' {z : R | z ∣ x ∧ v.value .limit z = 0}
  have hS : S.Finite := v.finite_zero_order_divisor_classes htriple hdivisibility hx hxlimit
  let : Fintype S := hS.fintype
  let P := {p : R × R // p.1 * p.2 = x ∧ v.value .limit p.1 = 0}
  let code : P → S := fun p =>
    ⟨Associates.mk p.val.1, p.val.1, ⟨⟨p.val.2, p.property.1.symm⟩, p.property.2⟩, rfl⟩
  have hcode : ∀ p q : P, code p = code q →
      Associates.mk p.val.2 = Associates.mk q.val.2 := by
    intro p q heq
    have hfirst : Associated p.val.1 q.val.1 :=
      Associates.mk_eq_mk_iff_associated.mp (congrArg Subtype.val heq)
    have hprod : Associated (p.val.1 * p.val.2) (q.val.1 * q.val.2) := by
      rw [p.property.1, q.property.1]
    have hp : p.val.1 ≠ 0 := by
      apply left_ne_zero_of_mul
      rwa [p.property.1]
    exact Associates.mk_eq_mk_iff_associated.mpr (hprod.of_mul_left hfirst hp)
  have hcomplement : (Set.range fun p : P => Associates.mk p.val.2).Finite :=
    finite_range_of_finite_code (fun p : P => Associates.mk p.val.2) code hcode
  apply (hS.union hcomplement).subset
  rintro _ ⟨z, hzx, rfl⟩
  by_cases hzlimit : v.value .limit z = 0
  · exact Set.mem_union_left _ ⟨z, ⟨hzx, hzlimit⟩, rfl⟩
  · obtain ⟨u, hxu⟩ := hzx
    have hzu : z * u ≠ 0 := by rwa [← hxu]
    have hvalue := v.value_mul .limit z u (left_ne_zero_of_mul hzu) (right_ne_zero_of_mul hzu)
    rw [← hxu] at hvalue
    have hulimit : v.value .limit u = 0 := by omega
    have hux : u * z = x := (mul_comm u z).trans hxu.symm
    exact Set.mem_union_right _ ⟨⟨(u, z), hux, hulimit⟩, rfl⟩

/-- The same conclusion as a finite divisor set in the usual associates
monoid, independent of any choice of element representatives. -/
theorem finite_associates_divisors_of_limit_le_one (v : ValuationProfiles R ι)
    (htriple : SignedDifferenceTriple v)
    (hdivisibility : ∀ z u : R, z ≠ 0 → u ≠ 0 →
      (∀ p, v.value p z ≤ v.value p u) → z ∣ u)
    {x : R} (hx : x ≠ 0) (hxlimit : v.value .limit x ≤ 1) :
    {a : Associates R | a ∣ Associates.mk x}.Finite := by
  convert v.finite_divisor_classes_of_limit_le_one htriple hdivisibility hx hxlimit using 1
  ext a
  obtain ⟨z, rfl⟩ := Associates.mk_surjective a
  constructor
  · intro hz
    exact ⟨z, Associates.mk_dvd_mk.mp hz, rfl⟩
  · rintro ⟨u, hux, heq⟩
    rw [← heq]
    exact Associates.mk_dvd_mk.mpr hux

/-- The actual profile of a_n has no nonunit divisor of horizontal order zero. -/
theorem isUnit_of_zero_order_divisor_primaryAtomProfile (v : ValuationProfiles R ι)
    {x : R} (hx : x ≠ 0) (n : ℕ)
    (houtside : ∀ i, v.value (.outside i) x = 0)
    (hprimary : ∀ j, (v.value (.primary j) x : ℤ) = primaryAtomProfile n j)
    {z : R} (hzx : z ∣ x) (hzlimit : v.value .limit z = 0) : IsUnit z := by
  have hz : z ≠ 0 := ne_zero_of_dvd_ne_zero hx hzx
  have hzoutside : ∀ i, v.value (.outside i) z = 0 := by
    intro i
    have hle := v.value_le_of_dvd (.outside i) hx hzx
    rw [houtside] at hle
    exact Nat.eq_zero_of_le_zero hle
  have hzero : EventuallyConstantProfile (fun j => (v.value (.primary j) z : ℤ)) 0 := by
    obtain ⟨N, hN⟩ := v.eventually_primary z hz
    refine ⟨N, ?_⟩
    intro j hj
    change (v.value (.primary j) z : ℤ) = 0
    rw [hN j hj, hzlimit]
    rfl
  have hprimaryzero := eq_zero_of_le_primaryAtomProfile
    (fun j => (v.value (.primary j) z : ℤ)) n hzero
    (v.pure_triple z hz hzlimit hzoutside) (fun j => Int.natCast_nonneg _) (by
      intro j
      rw [← hprimary]
      exact_mod_cast v.value_le_of_dvd (.primary j) hx hzx)
  apply v.unit_of_zero z hz
  intro p
  cases p with
  | limit => exact hzlimit
  | outside i => exact hzoutside i
  | primary j =>
    have h := congrFun hprimaryzero j
    change (v.value (.primary j) z : ℤ) = 0 at h
    exact_mod_cast h

/-- Actual nonzero elements with the a_n profile are atoms of the domain. -/
theorem irreducible_of_primaryAtomProfile (v : ValuationProfiles R ι)
    {x : R} (hx : x ≠ 0) (n : ℕ) (hlimit : v.value .limit x = 1)
    (houtside : ∀ i, v.value (.outside i) x = 0)
    (hprimary : ∀ j, (v.value (.primary j) x : ℤ) = primaryAtomProfile n j) :
    Irreducible x := by
  constructor
  · intro hunit
    have hzero := v.value_unit .limit x hunit
    omega
  · intro a b hab
    have habnz : a * b ≠ 0 := by rwa [← hab]
    have hv := v.value_mul .limit a b (left_ne_zero_of_mul habnz) (right_ne_zero_of_mul habnz)
    rw [← hab, hlimit] at hv
    by_cases ha : v.value .limit a = 0
    · exact Or.inl (v.isUnit_of_zero_order_divisor_primaryAtomProfile hx n houtside hprimary
        ⟨b, hab⟩ ha)
    · have hb : v.value .limit b = 0 := by omega
      exact Or.inr (v.isUnit_of_zero_order_divisor_primaryAtomProfile hx n houtside hprimary
        ⟨a, hab.trans (mul_comm a b)⟩ hb)

end UnconditionalCounterexample.ValuationProfiles
