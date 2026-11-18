import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The direct arbitrary-ideal SP argument

For a nonzero principal element, take the indicator ideals of its positive valuation
levels. For a nonzero ideal I, sum these level ideals over the nonzero elements of I.
Locally the sum at each level is the indicator of the minimum order of I, so each sum
is radical. A bound from one nonzero member of I gives a finite factorization.

This module proves the arbitrary-ideal step, without finite generation of I
or an external SP criterion. Its inputs are explicit local principal orders,
a uniform bound on each principal profile, and the threshold ideal realization
supplied separately by the construction. No SP property is assumed.
-/

noncomputable section
namespace UnconditionalCounterexample.RadicalIdealProducts
open scoped BigOperators
variable {R : Type*} [CommRing R]

abbrev Maximal (R : Type*) [CommRing R] := {M : Ideal R // M.IsMaximal}
local instance maximal_instance (M : Maximal R) : M.val.IsMaximal := M.property

abbrev localIdeal (M : Maximal R) (I : Ideal R) : Ideal (Localization.AtPrime M.val) :=
  I.map (algebraMap R (Localization.AtPrime M.val))

abbrev localMaximal (M : Maximal R) : Ideal (Localization.AtPrime M.val) :=
  IsLocalRing.maximalIdeal (Localization.AtPrime M.val)

abbrev NonzeroMember (I : Ideal R) := {x : R // x ∈ I ∧ x ≠ 0}

theorem nonempty_members (I : Ideal R) (hI : I ≠ ⊥) : Nonempty (NonzeroMember I) := by
  obtain ⟨x, hx, hx0⟩ := I.ne_bot_iff.mp hI
  exact ⟨⟨x, hx, hx0⟩⟩

/-- The actual minimum over nonzero members, not a minimum over a finite generating set. -/
def minimum (ν : Maximal R → R → ℕ) (I : Ideal R) (M : Maximal R) : ℕ :=
  sInf (Set.range (fun x : NonzeroMember I => ν M x))

theorem minimum_le (ν : Maximal R → R → ℕ) (I : Ideal R) (M : Maximal R)
    (x : NonzeroMember I) : minimum ν I M ≤ ν M x :=
  csInf_le' (Set.mem_range_self x)

theorem minimum_attained (ν : Maximal R → R → ℕ) (I : Ideal R) (hI : I ≠ ⊥)
    (M : Maximal R) : ∃ x : NonzeroMember I, ν M x = minimum ν I M := by
  have := nonempty_members I hI
  exact csInf_mem (Set.range_nonempty (fun x : NonzeroMember I => ν M x))

/-- Principal local exponents determine the exponent of every nonzero ideal by
its attained minimum, without any finite-generation assumption. -/
theorem localIdeal_eq_pow_minimum (ν : Maximal R → R → ℕ)
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ ν M x)
    (I : Ideal R) (hI : I ≠ ⊥) (M : Maximal R) :
    localIdeal M I = localMaximal M ^ minimum ν I M := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hmem : algebraMap R (Localization.AtPrime M.val) x ∈ localMaximal M ^ ν M x := by
      rw [← hprincipal M x hx0]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton x))
    exact Ideal.pow_le_pow_right (minimum_le ν I M ⟨x, hx, hx0⟩) hmem
  · obtain ⟨x, hx⟩ := minimum_attained ν I hI M
    rw [← hx, ← hprincipal M x x.property.2]
    exact Ideal.map_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr x.property.1))

/-- The source's ideal sum over all nonzero elements of I. -/
def thresholdSum (J : ∀ x : R, x ≠ 0 → ℕ → Ideal R) (I : Ideal R) (k : ℕ) : Ideal R :=
  ⨆ x : NonzeroMember I, J x x.property.2 k

/-- The arbitrary sum has the exact indicator profile at each maximal ideal. -/
theorem local_thresholdSum (ν : Maximal R → R → ℕ)
    (J : ∀ x : R, x ≠ 0 → ℕ → Ideal R)
    (hJ : ∀ (M : Maximal R) (x : R) (hx : x ≠ 0) (k : ℕ), 0 < k →
      localIdeal M (J x hx k) = if k ≤ ν M x then localMaximal M else ⊤)
    (I : Ideal R) (hI : I ≠ ⊥) (M : Maximal R) (k : ℕ) (hk : 0 < k) :
    localIdeal M (thresholdSum J I k) =
      if k ≤ minimum ν I M then localMaximal M else ⊤ := by
  change (⨆ x : NonzeroMember I, J x x.property.2 k).map _ = _
  rw [Ideal.map_iSup]
  split_ifs with hkm
  · have hxk (x : NonzeroMember I) : k ≤ ν M x := hkm.trans (minimum_le ν I M x)
    apply le_antisymm
    · apply iSup_le
      intro x
      change localIdeal M (J x x.property.2 k) ≤ localMaximal M
      rw [hJ M x x.property.2 k hk]
      simp [hxk x]
    · obtain ⟨x⟩ := nonempty_members I hI
      apply le_iSup_of_le x
      change localMaximal M ≤ localIdeal M (J x x.property.2 k)
      rw [hJ M x x.property.2 k hk]
      simp [hxk x]
  · apply top_unique
    obtain ⟨x, hx⟩ := minimum_attained ν I hI M
    apply le_iSup_of_le x
    change ⊤ ≤ localIdeal M (J x x.property.2 k)
    rw [hJ M x x.property.2 k hk, hx]
    simp [hkm]

/-- Each arbitrary threshold sum is radical, verified at all actual maximal
localizations. No radicality of an infinite sum is assumed. -/
theorem thresholdSum_isRadical (ν : Maximal R → R → ℕ)
    (J : ∀ x : R, x ≠ 0 → ℕ → Ideal R)
    (hJ : ∀ (M : Maximal R) (x : R) (hx : x ≠ 0) (k : ℕ), 0 < k →
      localIdeal M (J x hx k) = if k ≤ ν M x then localMaximal M else ⊤)
    (I : Ideal R) (hI : I ≠ ⊥) (k : ℕ) (hk : 0 < k) :
    (thresholdSum J I k).IsRadical := by
  apply Ideal.radical_eq_iff.mp
  apply Ideal.eq_of_localization_maximal
  intro M hM
  let m : Maximal R := ⟨M, hM⟩
  rw [IsLocalization.map_radical M.primeCompl]
  change (localIdeal m (thresholdSum J I k)).radical = localIdeal m (thresholdSum J I k)
  rw [local_thresholdSum ν J hJ I hI m k hk]
  split_ifs
  · exact (inferInstance : (localMaximal m).IsPrime).radical
  · exact Ideal.radical_top _

/-- A bounded natural exponent is the sum of its positive level indicators. -/
theorem prod_levels {G : Type*} [CommMonoid G] (a : G) (m N : ℕ) (hm : m ≤ N) :
    (∏ k ∈ Finset.range N, if k + 1 ≤ m then a else 1) = a ^ m := by
  classical
  induction N generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    simp [hm0]
  | succ N ih =>
    by_cases hmN : m ≤ N
    · rw [Finset.prod_range_succ, ih m hmN]
      simp [show ¬ N + 1 ≤ m by omega]
    · have hm' : m = N + 1 := by omega
      subst m
      calc
        _ = ∏ _k ∈ Finset.range (N + 1), a := by
          apply Finset.prod_congr rfl
          intro k hk
          simp [show k + 1 ≤ N + 1 from Nat.succ_le_of_lt (Finset.mem_range.mp hk)]
        _ = _ := by simp

/-- Direct arbitrary-ideal factorization from realized principal level profiles.
The bound comes from one nonzero member of I; I itself need not be finitely generated. -/
theorem eq_product_thresholdSums (ν : Maximal R → R → ℕ)
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ ν M x)
    (J : ∀ x : R, x ≠ 0 → ℕ → Ideal R)
    (hJ : ∀ (M : Maximal R) (x : R) (hx : x ≠ 0) (k : ℕ), 0 < k →
      localIdeal M (J x hx k) = if k ≤ ν M x then localMaximal M else ⊤)
    (I : Ideal R) (hI : I ≠ ⊥) (x : NonzeroMember I) (N : ℕ)
    (hN : ∀ M, ν M x ≤ N) :
    I = ∏ k ∈ Finset.range N, thresholdSum J I (k + 1) := by
  apply Ideal.eq_of_localization_maximal
  intro M hM
  let m : Maximal R := ⟨M, hM⟩
  change localIdeal m I = localIdeal m (∏ k ∈ Finset.range N, thresholdSum J I (k + 1))
  rw [localIdeal_eq_pow_minimum ν hprincipal I hI m]
  change _ = (Ideal.mapHom (algebraMap R (Localization.AtPrime M))) _
  rw [map_prod]
  have hmN : minimum ν I m ≤ N := (minimum_le ν I m x).trans (hN m)
  calc
    _ = ∏ k ∈ Finset.range N,
        if k + 1 ≤ minimum ν I m then localMaximal m else 1 :=
      (prod_levels (localMaximal m) (minimum ν I m) N hmN).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k _
      change (if k + 1 ≤ minimum ν I m then localMaximal m else 1) =
        localIdeal m (thresholdSum J I (k+1))
      simpa only [Ideal.one_eq_top] using
        (local_thresholdSum ν J hJ I hI m (k+1) (Nat.succ_pos k)).symm

/-- Every nonzero ideal is a finite product of radical ideals once all
principal level profiles are realized and principal orders are uniformly bounded. -/
theorem exists_radical_product (ν : Maximal R → R → ℕ)
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ ν M x)
    (hbounded : ∀ x : R, x ≠ 0 → ∃ N : ℕ, ∀ M, ν M x ≤ N)
    (J : ∀ x : R, x ≠ 0 → ℕ → Ideal R)
    (hJ : ∀ (M : Maximal R) (x : R) (hx : x ≠ 0) (k : ℕ), 0 < k →
      localIdeal M (J x hx k) = if k ≤ ν M x then localMaximal M else ⊤)
    (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ N : ℕ, ∃ K : ℕ → Ideal R, (∀ k, (K k).IsRadical) ∧
      I = ∏ k ∈ Finset.range N, K k := by
  obtain ⟨x⟩ := nonempty_members I hI
  obtain ⟨N, hN⟩ := hbounded x x.property.2
  exact ⟨N, fun k => thresholdSum J I (k+1),
    fun k => thresholdSum_isRadical ν J hJ I hI (k+1) (Nat.succ_pos k),
    eq_product_thresholdSums ν hprincipal J hJ I hI x N hN⟩

/-- The concrete producer may supply each positive threshold ideal separately;
choice assembles those actual ideals into the family needed by the sum argument. -/
theorem exists_radical_product_of_thresholds (ν : Maximal R → R → ℕ)
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ ν M x)
    (hbounded : ∀ x : R, x ≠ 0 → ∃ N : ℕ, ∀ M, ν M x ≤ N)
    (hrealize : ∀ (x : R) (_hx : x ≠ 0) (k : ℕ), 0 < k →
      ∃ J : Ideal R, ∀ M : Maximal R,
        localIdeal M J = if k ≤ ν M x then localMaximal M else ⊤)
    (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ N : ℕ, ∃ K : ℕ → Ideal R, (∀ k, (K k).IsRadical) ∧
      I = ∏ k ∈ Finset.range N, K k := by
  classical
  choose J hJ using hrealize
  let J' (x : R) (hx : x ≠ 0) (k : ℕ) : Ideal R :=
    if hk : 0 < k then J x hx k hk else ⊤
  apply exists_radical_product ν hprincipal hbounded J' _ I hI
  intro M x hx k hk
  dsimp only [J']
  simpa only [hk, dite_true] using hJ x hx k hk M

/-- In a reduced ring the zero ideal is radical as well, so the same direct
argument factors every ideal, including zero and the whole ring. -/
theorem every_ideal_radical_product [IsReduced R] (ν : Maximal R → R → ℕ)
    (hprincipal : ∀ (M : Maximal R) (x : R), x ≠ 0 →
      localIdeal M (Ideal.span {x}) = localMaximal M ^ ν M x)
    (hbounded : ∀ x : R, x ≠ 0 → ∃ N : ℕ, ∀ M, ν M x ≤ N)
    (hrealize : ∀ (x : R) (_hx : x ≠ 0) (k : ℕ), 0 < k →
      ∃ J : Ideal R, ∀ M : Maximal R,
        localIdeal M J = if k ≤ ν M x then localMaximal M else ⊤)
    (I : Ideal R) :
    ∃ N : ℕ, ∃ K : ℕ → Ideal R, (∀ k, (K k).IsRadical) ∧
      I = ∏ k ∈ Finset.range N, K k := by
  by_cases hI : I = ⊥
  · refine ⟨1, fun _ => ⊥, fun _ => Ideal.radical_eq_iff.mp (Ideal.radical_bot_of_isReduced), ?_⟩
    simp [hI]
  · exact exists_radical_product_of_thresholds ν hprincipal hbounded hrealize I hI

end UnconditionalCounterexample.RadicalIdealProducts
