import HereditaryAtomicity.UnitValues
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Simultaneous valuation values of Jacobson units

A nonzero Jacobson element and finitely many outside rank-one valuations let
one realize the values of any fixed nonzero fraction by a single ambient unit.
-/

namespace HereditaryAtomicity

universe u v w w'

private theorem exists_lt_pow_zero {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [MulArchimedean Γ₀]
    {a : Γ₀} (ha : 1 < a) (b : Γ₀) : ∃ n : ℕ, b < a ^ n := by
  obtain ⟨n, hn⟩ := MulArchimedean.arch b ha
  exact ⟨n + 1, hn.trans_lt (pow_lt_pow_right₀ ha (Nat.lt_succ_self n))⟩

section FinitePoles

variable {R : Type u} {K : Type v} {ι : Type w} {Γ : ι → Type w'}
  [CommRing R] [Field K]
  [∀ i, LinearOrderedCommGroupWithZero (Γ i)] [∀ i, MulArchimedean (Γ i)]

/-- One sufficiently large power exceeds all specified finite thresholds. -/
theorem exists_common_power (s : Finset ι) (a b : ∀ i, Γ i)
    (ha : ∀ i ∈ s, 1 < a i) : ∃ n : ℕ, ∀ i ∈ s, b i < (a i) ^ n := by
  classical
  have hex : ∀ i ∈ s, ∃ n : ℕ, b i < (a i) ^ n :=
    fun i hi => exists_lt_pow_zero (ha i hi) (b i)
  choose n hn using hex
  let N := s.attach.sup (fun i => n i i.property)
  refine ⟨N, ?_⟩
  intro i hi
  exact (hn i hi).trans_le (pow_le_pow_right₀ (ha i hi).le
    (Finset.le_sup (f := fun j : {j // j ∈ s} => n j j.property) (by simp :
      (⟨i, hi⟩ : {j // j ∈ s}) ∈ s.attach)))

/-- Finitely many outside valuations have a common pole in the source ring.
No inequivalence hypothesis on the valuations is needed. -/
theorem exists_common_pole (f : R →+* K) (v : ∀ i, Valuation K (Γ i))
    (s : Finset ι) (hout : ∀ i ∈ s, ∃ d : R, 1 < v i (f d)) :
    ∃ d : R, ∀ i ∈ s, 1 < v i (f d) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert k s hk ih =>
    obtain ⟨d, hd⟩ := ih (fun i hi => hout i (Finset.mem_insert_of_mem hi))
    by_cases hkd : 1 < v k (f d)
    · exact ⟨d, by simpa only [Finset.mem_insert, forall_eq_or_imp] using And.intro hkd hd⟩
    have hkd' : v k (f d) ≤ 1 := le_of_not_gt hkd
    obtain ⟨y, hy⟩ := hout k (Finset.mem_insert_self k s)
    obtain ⟨n, hn⟩ := exists_common_power s (fun i => v i (f d))
      (fun i => max 1 (v i (f y))) hd
    refine ⟨d ^ n + y, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with hik | hi
    · subst i
      have hsmall : v k (f (d ^ n)) < v k (f y) := by
        rw [map_pow, map_pow]
        exact (pow_le_one₀ zero_le hkd').trans_lt hy
      rw [map_add, (v k).map_add_eq_of_lt_right hsmall]
      exact hy
    · have hlarge : v i (f y) < v i (f (d ^ n)) := by
        rw [map_pow, map_pow]
        exact (le_max_right _ _).trans_lt (hn i hi)
      rw [map_add, (v i).map_add_eq_of_lt_left hlarge, map_pow, map_pow]
      exact (le_max_left _ _).trans_lt (hn i hi)

end FinitePoles

section Jacobson

variable {R : Type u} {K : Type v} {ι : Type w} {Γ : ι → Type w'}
  [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Fintype ι] [∀ i, LinearOrderedCommGroupWithZero (Γ i)]
  [∀ i, MulArchimedean (Γ i)]

/-- A single Jacobson unit realizes the values of a nonzero fraction at every
member of a finite outside family with Archimedean valuation codomains. -/
theorem exists_unit_same_values_of_archimedean
    (v : ∀ i, Valuation K (Γ i)) {j : R}
    (hj : j ∈ Ideal.jacobson (⊥ : Ideal R)) (hj0 : j ≠ 0)
    (hout : ∀ i, ∃ d : R, 1 < v i (algebraMap R K d))
    (x : K) (hx : x ≠ 0) :
    ∃ u : Rˣ, ∀ i, v i (algebraMap R K u) = v i x := by
  classical
  let f := algebraMap R K
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R x
  have hbK : f b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haK : f a ≠ 0 := by
    intro ha
    apply hx
    rw [← hab]
    change f a / f b = 0
    rw [ha, zero_div]
  have hjK : f j ≠ 0 := by
    intro h
    exact hj0 ((IsFractionRing.injective R K) (h.trans (map_zero f).symm))
  obtain ⟨d, hd⟩ := exists_common_pole f v Finset.univ (by simpa using hout)
  have hd' : ∀ i, 1 < v i (f d) := by simpa using hd
  have hja (i : ι) : v i (f (j * a)) ≠ 0 :=
    (v i).ne_zero_iff.mpr (by rw [map_mul]; exact mul_ne_zero hjK haK)
  have hjb (i : ι) : v i (f (j * b)) ≠ 0 :=
    (v i).ne_zero_iff.mpr (by rw [map_mul]; exact mul_ne_zero hjK hbK)
  obtain ⟨n, hn⟩ := exists_common_power Finset.univ (fun i => v i (f d))
    (fun i => max (v i (f (j * a)))⁻¹ (v i (f (j * b)))⁻¹)
    (by simpa using hd')
  let A := j * (d ^ n * a) + 1
  let B := j * (d ^ n * b) + 1
  have hA : IsUnit A := (Ideal.mem_jacobson_bot.mp hj) (d ^ n * a)
  have hB : IsUnit B := (Ideal.mem_jacobson_bot.mp hj) (d ^ n * b)
  refine ⟨hA.unit * hB.unit⁻¹, ?_⟩
  intro i
  have hda : 1 < v i (f (j * (d ^ n * a))) := by
    have hh : (v i (f (j * a)))⁻¹ < (v i (f d)) ^ n :=
      (le_max_left _ _).trans_lt (hn i (Finset.mem_univ i))
    have hh' := (inv_lt_iff_one_lt_mul₀' (pos_iff_ne_zero.mpr (hja i))).mp hh
    simpa only [map_mul, map_pow, mul_assoc, mul_left_comm, mul_comm] using hh'
  have hdb : 1 < v i (f (j * (d ^ n * b))) := by
    have hh : (v i (f (j * b)))⁻¹ < (v i (f d)) ^ n :=
      (le_max_right _ _).trans_lt (hn i (Finset.mem_univ i))
    have hh' := (inv_lt_iff_one_lt_mul₀' (pos_iff_ne_zero.mpr (hjb i))).mp hh
    simpa only [map_mul, map_pow, mul_assoc, mul_left_comm, mul_comm] using hh'
  have hvA : v i (f A) = v i (f (j * (d ^ n * a))) := by
    dsimp [A]
    rw [map_add, map_one]
    apply (v i).map_add_eq_of_lt_left
    simpa only [map_one] using hda
  have hvB : v i (f B) = v i (f (j * (d ^ n * b))) := by
    dsimp [B]
    rw [map_add, map_one]
    apply (v i).map_add_eq_of_lt_left
    simpa only [map_one] using hdb
  have hdK : f d ≠ 0 := by
    intro h
    have := hd' i
    rw [h, map_zero] at this
    exact (not_lt_of_ge zero_le) this
  have hc : v i (f j) * (v i (f d)) ^ n ≠ 0 :=
    mul_ne_zero ((v i).ne_zero_iff.mpr hjK)
      (pow_ne_zero n ((v i).ne_zero_iff.mpr hdK))
  change v i (f (↑(hA.unit * hB.unit⁻¹))) = v i x
  simp only [Units.val_mul, map_mul, map_units_inv, IsUnit.unit_spec, map_inv₀]
  rw [hvA, hvB, ← hab]
  simp only [map_mul, map_pow, map_div₀, ← mul_assoc]
  rw [← div_eq_mul_inv, mul_div_mul_left _ _ hc]

end Jacobson

section RankOne

variable {R : Type u} {K : Type v} {ι : Type w} {Γ : ι → Type w'}
  [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Fintype ι] [∀ i, LinearOrderedCommGroupWithZero (Γ i)]

/-- Finite simultaneous Jacobson-unit realization for arbitrary rank-one
valuations; only their actual value groups must be Archimedean. -/
theorem exists_unit_same_values
    (v : ∀ i, Valuation K (Γ i)) [∀ i, (v i).RankOne] {j : R}
    (hj : j ∈ Ideal.jacobson (⊥ : Ideal R)) (hj0 : j ≠ 0)
    (hout : ∀ i, ∃ d : R, 1 < v i (algebraMap R K d))
    (x : K) (hx : x ≠ 0) :
    ∃ u : Rˣ, ∀ i, v i (algebraMap R K u) = v i x := by
  let (i : ι) : MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (.ofClass (v i))) :=
    (Valuation.nonempty_rankOne_iff_mulArchimedean (v := v i)).mp ⟨inferInstance⟩
  have hout' : ∀ i, ∃ d : R, 1 < (v i).restrict (algebraMap R K d) := by
    intro i
    obtain ⟨d, hd⟩ := hout i
    refine ⟨d, ?_⟩
    exact lt_of_not_ge (fun h => not_le_of_gt hd ((v i).restrict_le_one_iff.mp h))
  obtain ⟨u, hu⟩ := exists_unit_same_values_of_archimedean
    (fun i => (v i).restrict) hj hj0 hout' x hx
  refine ⟨u, fun i => ?_⟩
  have h := congrArg MonoidWithZeroHom.ValueGroup₀.embedding (hu i)
  simpa only [Valuation.embedding_restrict] using h

/-- At one outside rank-one valuation, every nonzero fraction has the value of
an actual source-ring unit. -/
theorem exists_unit_same_valuation {Γ₀ : Type w'} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [v.RankOne] {j : R}
    (hj : j ∈ Ideal.jacobson (⊥ : Ideal R)) (hj0 : j ≠ 0)
    (hout : ∃ d : R, 1 < v (algebraMap R K d))
    (x : K) (hx : x ≠ 0) : ∃ u : Rˣ, v (algebraMap R K u) = v x := by
  obtain ⟨u, hu⟩ := exists_unit_same_values (fun _ : Unit => v)
    hj hj0 (fun _ => hout) x hx
  exact ⟨u, hu ()⟩

end RankOne

end HereditaryAtomicity
