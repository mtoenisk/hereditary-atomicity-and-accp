import HereditaryAtomicity.DVRBase.SourceSupport
import HereditaryAtomicity.DVRBase.BlockNumerics

/-!
# Initial-segment support through actual block selection

Prescribed lower bounds on return exponents ensure that a selected block has
the required power return at every place supporting its first original ratio.
The initial-segment support assumption then supplies the whole finite prefix
at every nonunit endpoint.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
variable {K : Type*} [Field K]

/-- A known power quotient remains in a subring at every larger exponent. -/
theorem power_quotient_mem_of_le (A : Subring K) {x d : K} (hx : x ∈ A)
    {m n : ℕ} (hmn : m ≤ n) (hreturn : x ^ m / d ∈ A) : x ^ n / d ∈ A := by
  have heq : x ^ n / d = (x ^ m / d) * x ^ (n - m) := by
    conv_lhs => rw [← Nat.add_sub_of_le hmn, pow_add]
    ring
  rw [heq]
  exact A.mul_mem hreturn (A.pow_mem hx _)

/-- A source multiple inherits a power-return quotient, and its exponent may
be increased to the prescribed floor selected by the block recursion. -/
theorem multiple_power_quotient_mem_of_le (D A : Subring K) (hDA : D ≤ A)
    {x y : D} (hxy : x ∣ y) {d : K} {m n : ℕ} (hmn : m ≤ n)
    (hreturn : (x : K) ^ m / d ∈ A) : (y : K) ^ n / d ∈ A := by
  obtain ⟨q, hq⟩ := hxy
  have hx := power_quotient_mem_of_le A (hDA x.property) hmn hreturn
  have heq : (y : K) ^ n / d = ((x : K) ^ n / d) * (q : K) ^ n := by
    rw [hq]
    simp only [Subring.coe_mul, mul_pow]
    ring
  rw [heq]
  exact A.mul_mem hx (A.pow_mem (hDA q.property) _)

namespace SourceBlockData
variable {R : Subring K} (B : SourceBlockData R)

/-- The support and floor conditions on the original chain prove the prefix
return condition for the selected block data. -/
theorem selected_prefix_power_return
    (D : Subring K) [IsFractionRing D K] (places : Set (MaximalSpectrum D))
    (c t : ℕ → D) (a l floor : ℕ → ℕ) (ha : StrictMono a)
    (_hendpoint : ∀ n, (B.endpoint n : K) = (c (a n) : K))
    (hratio : ∀ n, (B.ratio n : K) = ((sourceBlock t (a n) (l n) : D) : K))
    (hfloor : ∀ n, floor (a n) ≤ B.returnExponent n)
    (hsupport : ∀ M ∈ places, ∀ n, c n ∈ M.asIdeal → ∀ i < n, t i ∈ M.asIdeal)
    (hreturn : ∀ M ∈ places, ∀ i, t i ∈ M.asIdeal →
      (t i : K) ^ floor i / (B.uniformizer : K) ^ B.exponent ∈ sourceMaximalStalk D M) :
    ∀ M ∈ places, ∀ n, c (a n) ∈ M.asIdeal → ∀ i < n,
      (B.ratio i : K) ^ B.returnExponent i / (B.uniformizer : K) ^ B.exponent ∈
        sourceMaximalStalk D M := by
  intro M hM n hcn i hi
  rw [hratio i]
  exact multiple_power_quotient_mem_of_le D (sourceMaximalStalk D M)
    (le_sourceMaximalStalk D M) (sourceBlock_first_dvd t (a i) (l i)) (hfloor i)
    (hreturn M hM (a i) (hsupport M hM (a n) hcn (a i) (ha hi)))

/-- Every selected block remains a unit outside the support set, because it
is literally a finite product of the original source ratios. -/
theorem selected_ratio_unit_elsewhere
    (D : Subring K) [IsFractionRing D K] (places : Set (MaximalSpectrum D))
    (t : ℕ → D) (a l : ℕ → ℕ)
    (hsupport : ∀ n (M : MaximalSpectrum D), t n ∈ M.asIdeal → M ∈ places) :
    ∀ n (M : MaximalSpectrum D), M ∉ places →
      IsUnit (sourceMaximalMap D M (sourceBlock t (a n) (l n))) := by
  intro n M hM
  unfold sourceBlock
  rw [map_prod]
  apply IsUnit.prod_iff.mpr
  intro i _
  exact (isUnit_sourceMaximalMap_iff D M _).mpr (fun hi => hM (hsupport _ M hi))

end SourceBlockData
end HereditaryAtomicity.DVRBase
