import UnconditionalCounterexample.PrincipalProfiles

/-! # Triangular inversion with auxiliary factors

Normalize each main factor by the product of *both* kinds of predecessors.
Auxiliary factors themselves stay unnormalized. Every finite signed word in
the original factors has a representation using these main generators and
the auxiliary factors, keeping their two exponent lists separate.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards

open PrincipalProfiles

/-- Main factor at stage n divided by the specified power of every earlier
main and auxiliary factor. -/
def normalizedMain {L : Type*} [CommGroupWithZero L] (F G : ℕ → L) (E : ℕ → ℕ) (n : ℕ) : L :=
  F n / ∏ j ∈ Finset.range n, (F j * G j) ^ E n

private def groupNormalized {L : Type*} [CommGroup L] (F G : ℕ → L) (E : ℕ → ℕ) (n : ℕ) : L :=
  F n / ∏ j ∈ Finset.range n, (F j * G j) ^ E n

private theorem normalize_group {L : Type*} [CommGroup L] (F G : ℕ → L) (E : ℕ → ℕ)
    (e : ℕ ⊕ ℕ →₀ ℤ) : ∃ a b : ℕ →₀ ℤ,
    e.prod (fun i z => Sum.elim F G i ^ z) =
      a.prod (fun n z => groupNormalized F G E n ^ z) * b.prod (fun n z => G n ^ z) := by
  classical
  let W := groupNormalized F G E
  let M := Subgroup.closure (Set.range W)
  let T := Subgroup.closure (Set.range G)
  let S := M ⊔ T
  have hW (n : ℕ) : W n ∈ S := (le_sup_left : M ≤ S) (Subgroup.subset_closure (Set.mem_range_self _))
  have hG (n : ℕ) : G n ∈ S := (le_sup_right : T ≤ S) (Subgroup.subset_closure (Set.mem_range_self _))
  have hF (n : ℕ) : F n ∈ S := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hprod : (∏ j ∈ Finset.range n, (F j * G j) ^ E n) ∈ S := by
        exact Submonoid.prod_mem _ fun j hj =>
          S.pow_mem (S.mul_mem (ih j (Finset.mem_range.mp hj)) (hG j)) _
      simpa only [W, groupNormalized, div_mul_cancel] using S.mul_mem (hW n) hprod
  have hraw (i : ℕ ⊕ ℕ) : Sum.elim F G i ∈ S := by cases i <;> first | apply hF | apply hG
  have hw : e.prod (fun i z => Sum.elim F G i ^ z) ∈ S :=
    Submonoid.prod_mem _ fun i _ => S.zpow_mem (hraw i) _
  obtain ⟨w, hw, g, hg, he⟩ := Subgroup.mem_sup.mp hw
  obtain ⟨a, ha⟩ := Subgroup.exists_finsupp_of_mem_closure_range W w hw
  obtain ⟨b, hb⟩ := Subgroup.exists_finsupp_of_mem_closure_range G g hg
  exact ⟨a,b, by rw [← ha, ← hb]; exact he.symm⟩

/-- The denominator includes all preceding raw factors even when an auxiliary
factor has nonzero value at its own private place. -/
theorem normalize_mixed_word {L : Type*} [Field L] (F G : ℕ → L)
    (hf : ∀ n, F n ≠ 0) (hg : ∀ n, G n ≠ 0) (E : ℕ → ℕ) (e : ℕ ⊕ ℕ →₀ ℤ) :
    ∃ a b : ℕ →₀ ℤ, word (Sum.elim F G) e = word (normalizedMain F G E) a * word G b := by
  let f (n : ℕ) := Units.mk0 _ (hf n)
  let g (n : ℕ) := Units.mk0 _ (hg n)
  obtain ⟨a, b, h⟩ := normalize_group f g E e
  have he := congrArg (fun u : Lˣ => (u : L)) h
  have hsum (i : ℕ ⊕ ℕ) : ((Sum.elim f g i : Lˣ) : L) = Sum.elim F G i := by cases i <;> rfl
  refine ⟨a,b,?_⟩
  simpa only [Finsupp.prod, word, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    hsum, groupNormalized, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_mk0,
    normalizedMain, f,g] using he

end UnconditionalCounterexample.Variations.PrivateGuards
