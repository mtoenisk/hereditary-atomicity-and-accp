import UnconditionalCounterexample.PrimaryWordProfiles
import UnconditionalCounterexample.PairedIsolators

/-!
# Primary and paired isolators from the actual generator columns

The even isolator is b_n. The odd isolator is the literal rational expression
q_n³/(b_n² b_(n+1)²), whose adjacent even values cancel. Both lie in the actual
vertical intersection and are units in its pole algebra. The paired guard
isolator is then constructed as p³/f, including its exact product identity.

The b/q valuation columns, guard-unit values, and pole-algebra membership are
explicit construction inputs. No singleton or prime classification is assumed.
-/

noncomputable section
namespace UnconditionalCounterexample.PrimaryIsolators
open WithZero NormalizedWords PrimaryWordProfiles IntersectionDomain
variable {K ι : Type*} [Field K]

/-- Triangular normalization preserves actual membership and inverse membership. -/
theorem normalizedFactor_mem (B : Subring K) (P : ℕ → K) (E : ℕ → ℕ)
    (hP : ∀ i, P i ∈ B) (hPi : ∀ i, (P i)⁻¹ ∈ B) (i : ℕ) :
    RawWords.normalizedFactor P E i ∈ B := by
  rw [RawWords.normalizedFactor, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  apply B.mul_mem (hP i)
  apply B.prod_mem
  intro j _
  rw [← inv_pow]
  exact B.pow_mem (hPi j) _

theorem normalizedFactor_inv_mem (B : Subring K) (P : ℕ → K) (E : ℕ → ℕ)
    (hP : ∀ i, P i ∈ B) (hPi : ∀ i, (P i)⁻¹ ∈ B) (i : ℕ) :
    (RawWords.normalizedFactor P E i)⁻¹ ∈ B := by
  rw [RawWords.normalizedFactor, inv_div, div_eq_mul_inv]
  apply B.mul_mem _ (hPi i)
  exact B.prod_mem (fun j _ => B.pow_mem (hP j) _)

/-- For the actual pole algebra of the raw list, both membership premises
are discharged directly from the specified generators. -/
theorem normalizedFactor_pole_mem {k : Type*} [Field k]
    (F : ℕ → Polynomial k) (E : ℕ → ℕ) (i : ℕ) :
    RawWords.normalizedFactor (fun j => algebraMap (Polynomial k) (RatFunc k) (F j)) E i
      ∈ PoleAlgebra.generated (Set.range F) ∧
    (RawWords.normalizedFactor (fun j => algebraMap (Polynomial k) (RatFunc k) (F j)) E i)⁻¹
      ∈ PoleAlgebra.generated (Set.range F) := by
  have hP (j : ℕ) := PoleAlgebra.polynomial_mem (Set.range F) (F j)
  have hPi (j : ℕ) := PoleAlgebra.inverse_mem (Set.mem_range_self j : F j ∈ Set.range F)
  exact ⟨normalizedFactor_mem (PoleAlgebra.generated (Set.range F)).toSubring _ E hP hPi i,
    normalizedFactor_inv_mem (PoleAlgebra.generated (Set.range F)).toSubring _ E hP hPi i⟩

/-- Raw guard units remain guard units after triangular normalization. -/
theorem normalizedFactor_guard (w : Valuation K ℤᵐ⁰) (P : ℕ → K) (E : ℕ → ℕ)
    (hP : ∀ i, w (P i) = 1) (i : ℕ) :
    w (RawWords.normalizedFactor P E i) = 1 := by
  simp [RawWords.normalizedFactor, map_div₀, hP]

/-- The literal quotient cancelling both adjacent even primary values. -/
def oddIsolator (W : ℕ → K) (n : ℕ) : K :=
  W (Generator.q n).stage ^ 3 /
    (W (Generator.b n).stage ^ 2 * W (Generator.b (n + 1)).stage ^ 2)

theorem oddIsolator_primary (v : ℕ → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hb : ∀ n j, v j (W (Generator.b n).stage) = exp (-(bWeight n j)))
    (hq : ∀ n j, v j (W (Generator.q n).stage) = exp (-(qWeight n j)))
    (n j : ℕ) : v j (oddIsolator W n) = exp (-(if j = 2*n+1 then (3 : ℤ) else 0)) := by
  rw [oddIsolator, map_div₀, map_mul, map_pow, map_pow, map_pow, hq, hb, hb,
    ← exp_nsmul, ← exp_nsmul, ← exp_nsmul, ← exp_add, ← exp_sub]
  apply congrArg exp
  simp only [nsmul_eq_mul, Nat.cast_ofNat, bWeight, qWeight]
  split_ifs <;> omega

theorem oddIsolator_guard (w : Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hw : ∀ i, w (W i) = 1) (n : ℕ) : w (oddIsolator W n) = 1 := by
  simp [oddIsolator, map_div₀, hw]

theorem oddIsolator_mem (B : Subring K) (W : ℕ → K)
    (hW : ∀ i, W i ∈ B) (hWi : ∀ i, (W i)⁻¹ ∈ B) (n : ℕ) :
    oddIsolator W n ∈ B := by
  rw [oddIsolator, div_eq_mul_inv, mul_inv_rev, ← inv_pow, ← inv_pow]
  exact B.mul_mem (B.pow_mem (hW _) 3)
    (B.mul_mem (B.pow_mem (hWi _) 2) (B.pow_mem (hWi _) 2))

theorem oddIsolator_inv_mem (B : Subring K) (W : ℕ → K)
    (hW : ∀ i, W i ∈ B) (hWi : ∀ i, (W i)⁻¹ ∈ B) (n : ℕ) :
    (oddIsolator W n)⁻¹ ∈ B := by
  rw [oddIsolator, inv_div, div_eq_mul_inv, ← inv_pow]
  exact B.mul_mem (B.mul_mem (B.pow_mem (hW _) 2) (B.pow_mem (hW _) 2))
    (B.pow_mem (hWi _) 3)

/-- The explicit singleton profile puts an element into the actual intersection. -/
theorem singleton_mem (B : Subring K) (v : ι → Valuation K ℤᵐ⁰)
    (i : ι) (z : K) (hzB : z ∈ B) (hzi : v i z = exp (-3))
    (hzother : ∀ j, j ≠ i → v j z = 1) : z ∈ intersection B v := by
  apply (mem_intersection B v z).mpr
  refine ⟨hzB, fun j => ?_⟩
  by_cases hj : j = i
  · rw [hj, hzi, exp_le_one_iff]
    norm_num
  · rw [hzother j hj]

/-- The even primary singleton is the actual b generator. -/
theorem exists_even_primary_isolator (B : Subring K)
    (v : ℕ → Valuation K ℤᵐ⁰) (w : ι → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hb : ∀ n j, v j (W (Generator.b n).stage) = exp (-(bWeight n j)))
    (hW : ∀ i, W i ∈ B) (hWi : ∀ i, (W i)⁻¹ ∈ B)
    (hw : ∀ p i, w p (W i) = 1) (n : ℕ) :
    ∃ f : intersection B (Sum.elim v w), (f : K)⁻¹ ∈ B ∧
      (Sum.elim v w) (.inl (2*n)) f = exp (-3) ∧
      (∀ l, l ≠ .inl (2*n) → (Sum.elim v w) l f = 1) := by
  have hmain : (Sum.elim v w) (.inl (2*n)) (W (Generator.b n).stage) = exp (-3) := by
    simpa [bWeight] using hb n (2*n)
  have hother : ∀ l, l ≠ .inl (2*n) → (Sum.elim v w) l (W (Generator.b n).stage) = 1 := by
    intro l hl
    cases l with
    | inl j =>
      have hj : j ≠ 2*n := fun h => hl (congrArg Sum.inl h)
      simp [hb, bWeight, hj]
    | inr p => exact hw p _
  exact ⟨⟨_, singleton_mem B (Sum.elim v w) _ _ (hW _) hmain hother⟩,
    hWi _, hmain, hother⟩

/-- The odd primary singleton is the literal q-cube divided by its two b-squares. -/
theorem exists_odd_primary_isolator (B : Subring K)
    (v : ℕ → Valuation K ℤᵐ⁰) (w : ι → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hb : ∀ n j, v j (W (Generator.b n).stage) = exp (-(bWeight n j)))
    (hq : ∀ n j, v j (W (Generator.q n).stage) = exp (-(qWeight n j)))
    (hW : ∀ i, W i ∈ B) (hWi : ∀ i, (W i)⁻¹ ∈ B)
    (hw : ∀ p i, w p (W i) = 1) (n : ℕ) :
    ∃ f : intersection B (Sum.elim v w), (f : K)⁻¹ ∈ B ∧
      (Sum.elim v w) (.inl (2*n+1)) f = exp (-3) ∧
      (∀ l, l ≠ .inl (2*n+1) → (Sum.elim v w) l f = 1) := by
  have hmain : (Sum.elim v w) (.inl (2*n+1)) (oddIsolator W n) = exp (-3) := by
    simpa using oddIsolator_primary v W hb hq n (2*n+1)
  have hother : ∀ l, l ≠ .inl (2*n+1) → (Sum.elim v w) l (oddIsolator W n) = 1 := by
    intro l hl
    cases l with
    | inl j =>
      have hj : j ≠ 2*n+1 := fun h => hl (congrArg Sum.inl h)
      simpa [hj] using
        oddIsolator_primary v W hb hq n j
    | inr p => exact oddIsolator_guard (w p) W (hw p) n
  exact ⟨⟨_, singleton_mem B (Sum.elim v w) _ _ (oddIsolator_mem B W hW hWi n) hmain hother⟩,
    oddIsolator_inv_mem B W hW hWi n, hmain, hother⟩

/-- Every primary index has a constructed B-unit singleton of positive order three. -/
theorem exists_primary_isolator (B : Subring K)
    (v : ℕ → Valuation K ℤᵐ⁰) (w : ι → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hb : ∀ n j, v j (W (Generator.b n).stage) = exp (-(bWeight n j)))
    (hq : ∀ n j, v j (W (Generator.q n).stage) = exp (-(qWeight n j)))
    (hW : ∀ i, W i ∈ B) (hWi : ∀ i, (W i)⁻¹ ∈ B)
    (hw : ∀ p i, w p (W i) = 1) (j : ℕ) :
    ∃ f : intersection B (Sum.elim v w), (f : K)⁻¹ ∈ B ∧
      (Sum.elim v w) (.inl j) f = exp (-3) ∧
      (∀ l, l ≠ .inl j → (Sum.elim v w) l f = 1) := by
  have hj : j = 2*(j/2) ∨ j = 2*(j/2)+1 := by omega
  rcases hj with hj | hj
  · rw [hj]
    exact exists_even_primary_isolator B v w W hb hW hWi hw _
  · rw [hj]
    exact exists_odd_primary_isolator B v w W hb hq hW hWi hw _

/-- Construct the actual primary/guard pair, including its product p³. -/
theorem exists_paired_isolators (B : Subring K)
    (v : ℕ → Valuation K ℤᵐ⁰) (w : ι → Valuation K ℤᵐ⁰) (W : ℕ → K)
    (hb : ∀ n j, v j (W (Generator.b n).stage) = exp (-(bWeight n j)))
    (hq : ∀ n j, v j (W (Generator.q n).stage) = exp (-(qWeight n j)))
    (hW : ∀ i, W i ∈ B) (hWi : ∀ i, (W i)⁻¹ ∈ B)
    (hw : ∀ p i, w p (W i) = 1) (i : ℕ) (j : ι) (p : ℕ)
    (hpinv : (p : K)⁻¹ ∈ B) (hpi : v i (p : K) = exp (-1))
    (hpj : w j (p : K) = exp (-1))
    (hpother : ∀ l, l ≠ .inl i → l ≠ .inr j → (Sum.elim v w) l (p : K) = 1) :
    ∃ f g : intersection B (Sum.elim v w),
      (f : K)⁻¹ ∈ B ∧ (g : K)⁻¹ ∈ B ∧
      (Sum.elim v w) (.inl i) f = exp (-3) ∧
      (∀ l, l ≠ .inl i → (Sum.elim v w) l f = 1) ∧
      (Sum.elim v w) (.inr j) g = exp (-3) ∧
      (∀ l, l ≠ .inr j → (Sum.elim v w) l g = 1) ∧
      f * g = (p : intersection B (Sum.elim v w)) ^ 3 := by
  obtain ⟨f, hfinv, hfi, hfother⟩ := exists_primary_isolator B v w W hb hq hW hWi hw i
  obtain ⟨g, hginv, hgj, hgother, hprod⟩ :=
    PairedIsolators.exists_guard_isolator B (Sum.elim v w) (.inl i) (.inr j)
      (by simp) p hpinv hpi hpj hpother f 3 (by decide) hfinv hfi hfother
  exact ⟨f, g, hfinv, hginv, hfi, hfother, hgj, hgother, hprod⟩

end UnconditionalCounterexample.PrimaryIsolators
