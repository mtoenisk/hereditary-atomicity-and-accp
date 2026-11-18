import UnconditionalCounterexample.ResidueUnits
import UnconditionalCounterexample.ConductorChains
import UnconditionalCounterexample.PaperSquareChain
import UnconditionalCounterexample.CompleteProfiles

namespace UnconditionalCounterexample.TailRatioChains
noncomputable section
open Polynomial WithZero PaperSquareChain PairedDomain PairedResidues
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

theorem qProfile_even_shift_zero {N j i : ℕ} (hi : i < N) : qProfile (2*(N+j)) i = 0 := by
  by_contra h
  have hb := qProfile_ne_zero_bounds h
  omega

theorem sum_qProfile_even_shift_le_two (N : ℕ) (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s, qProfile (2*(N+j)) i) ≤ 2 := by
  have h := sum_qProfile_even_le_two (s.image (fun j => N+j)) i
  rw [Finset.sum_image] at h
  · exact h
  · intro a _ b _ hab
    exact Nat.add_left_cancel hab

variable {S : Set ℚ[X]} (d : Places) (q : ℕ → PoleAlgebra.generated S)
  (hunit : ∀ n, IsUnit (q n))
  (hp : ∀ n i, vertical d (.inl i) (q n : RatFunc ℚ) = exp (-qProfile n i))
  (hg : ∀ n p, vertical d (.inr p) (q n : RatFunc ℚ) = 1)

include hunit in
theorem finite_product_dvd_of_late_primary
    (x : domain S d) (N : ℕ)
    (hlate : ∀ i, N ≤ i → vertical d (.inl i) (x : RatFunc ℚ) ≤ exp (-2))
    (s : Finset ℕ) : (∏ j ∈ s, domainRatio d q hp hg (2*(N+j))) ∣ x := by
  let P : RatFunc ℚ := ∏ j ∈ s, (q (2*(N+j)) : RatFunc ℚ)
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => q_ne_zero q hunit _)
  have hPcoe : ((∏ j ∈ s, domainRatio d q hp hg (2*(N+j)) : domain S d) : RatFunc ℚ) = P := by
    change (domain S d).subtype (∏ j ∈ s, domainRatio d q hp hg (2*(N+j))) = P
    rw [map_prod]
    rfl
  apply (IntersectionDomain.subring_dvd_iff_div_mem _ _ _ (fun h =>
    hP0 (hPcoe.symm.trans (congrArg Subtype.val h)))).mpr
  rw [hPcoe]
  apply (IntersectionDomain.div_mem_iff _ _ hP0).mpr
  have hxD := (IntersectionDomain.mem_intersection _ _ _).mp x.property
  constructor
  · rw [div_eq_mul_inv]
    apply (PoleAlgebra.generated S).mul_mem hxD.1
    dsimp [P]
    rw [← Finset.prod_inv_distrib]
    exact (PoleAlgebra.generated S).prod_mem (fun j _ => q_inv_mem q hunit _)
  · rintro (i | p)
    · have hP : vertical d (.inl i) P = exp (-(∑ j ∈ s, qProfile (2*(N+j)) i)) := by
        dsimp [P]
        clear hP0 hPcoe P
        induction s using Finset.induction_on with
        | empty => simp
        | @insert j s hnot ih =>
          simp only [Finset.prod_insert hnot, map_mul, hp, ih,
            Finset.sum_insert hnot, neg_add, exp_add]
      rw [hP]
      by_cases hi : i < N
      · simp only [qProfile_even_shift_zero hi, Finset.sum_const_zero, neg_zero, exp_zero]
        exact hxD.2 (.inl i)
      · exact (hlate i (by omega)).trans (exp_le_exp.mpr (by
          have h := sum_qProfile_even_shift_le_two N s i
          omega))
    · have hP : vertical d (.inr p) P = 1 := by
        simp only [P, map_prod, hg, Finset.prod_const_one]
      rw [hP]
      exact hxD.2 (.inr p)

include hunit in
theorem exists_tail_finite_product_dvd
    (x : domain S d) (hx : x ≠ 0)
    (horder : 2 ≤ PrimaryStabilization.tOrder (x : RatFunc ℚ)) :
    ∃ N : ℕ, ∀ M, N ≤ M → ∀ s : Finset ℕ,
      (∏ j ∈ s, domainRatio d q hp hg (2*(M+j))) ∣ x := by
  have hx0 : (x : RatFunc ℚ) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨N,hN⟩ := CompleteProfiles.eventually_primary S d x hx0
  refine ⟨N,?_⟩
  intro M hM s
  apply finite_product_dvd_of_late_primary d q hunit hp hg x M ?_ s
  intro i hi
  rw [DiscreteOrders.value_eq_exp_neg_order _ hx0]
  change exp (-DiscreteOrders.order (CompleteProfiles.valuations S d (.primary i)) x) ≤ exp (-2)
  rw [hN i (hM.trans hi), CompleteProfiles.limit_order S d x hx0]
  exact exp_le_exp.mpr (by omega)

theorem exists_tail_unit_residues (n : ℕ) (hn : n ≠ 0) :
    ∃ N : ℕ, ∀ M, N ≤ M → ∀ j,
      IsUnit (globalResidue S d n hn (domainRatio d q hp hg (2*(M+j)))) := by
  classical
  let indices : Finset ℕ := n.primeFactors.attach.image
    (fun p : n.primeFactors => d.primes.symm ⟨p, Nat.prime_of_mem_primeFactors p.property⟩)
  refine ⟨indices.sup id + 1,?_⟩
  intro M hM j
  apply globalResidue_isUnit S d n hn
  intro p
  apply primePairResidue_isUnit
  · change vertical d (.inl _) (q (2*(M+j)) : RatFunc ℚ) = 1
    rw [hp]
    have hi : d.primes.symm ⟨p, Nat.prime_of_mem_primeFactors p.property⟩ < M := by
      have hmem : d.primes.symm ⟨p, Nat.prime_of_mem_primeFactors p.property⟩ ∈ indices :=
        Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩
      have hb := Finset.le_sup (f := id) hmem
      dsimp only [id] at hb
      omega
    rw [qProfile_even_shift_zero hi, neg_zero, exp_zero]
  · exact hg _ _

include hunit hp hg in
theorem high_order_chain_of_integer_conductor
    (n : ℕ) (hn : n ≠ 0) (T : Subring (domain S d))
    (hconductor : ∀ z : domain S d, (n : domain S d)*z ∈ T)
    (x : T) (hx : x ≠ 0)
    (horder : 2 ≤ PrimaryStabilization.tOrder ((x : domain S d) : RatFunc ℚ)) :
    HasStrictChainAt x := by
  let : NeZero n := ⟨hn⟩
  have hxD : (x : domain S d) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨Nx,hxTail⟩ := exists_tail_finite_product_dvd d q hunit hp hg x hxD horder
  obtain ⟨Nr,hrTail⟩ := exists_tail_unit_residues d q hp hg n hn
  let N := max Nx Nr
  apply ConductorChains.hasStrictChainAt_of_finite_residues T (n : domain S d) hconductor
    (globalResidue S d n hn) (globalResidue_ker S d n hn) x hx
    (fun j => domainRatio d q hp hg (2*(N+j)))
  · intro j
    exact q_not_isUnit d q hp _
  · exact hrTail N (le_max_right _ _)
  · exact hxTail N (le_max_left _ _)

include hunit hp hg in
theorem high_order_chain_of_finite_index
    (T : Subring (domain S d)) (hfinite : Finite (domain S d ⧸ T.toAddSubgroup))
    (x : T) (hx : x ≠ 0)
    (horder : 2 ≤ PrimaryStabilization.tOrder ((x : domain S d) : RatFunc ℚ)) :
    HasStrictChainAt x := by
  have hn := T.toAddSubgroup.index_ne_zero_iff_finite.mpr hfinite
  apply high_order_chain_of_integer_conductor d q hunit hp hg T.toAddSubgroup.index hn T ?_ x hx horder
  intro z
  change (T.toAddSubgroup.index : domain S d)*z ∈ T.toAddSubgroup
  simpa only [nsmul_eq_mul] using T.toAddSubgroup.nsmul_index_mem z

end
end UnconditionalCounterexample.TailRatioChains
