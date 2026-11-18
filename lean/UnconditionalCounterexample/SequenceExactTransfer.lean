import UnconditionalCounterexample.PaperConductorScale
import UnconditionalCounterexample.SequenceLocalTransfer
import UnconditionalCounterexample.ConstructionRecovery

/-!
# Exact polynomial transfer at the prescribed integer scale

This is the manuscript Lemma 6.1 argument for the actual recursive sequence.
An extracted sequence of listed words recovers the rational hull. For the same
prescribed positive integer n with nt in T, the proof fixes s=nu_p(n), obtains
p^s t in the actual integral tensor image, and uses the actual simultaneous
stage transfer identities at that fixed s. The bounded latest exponents then
put the full L^bound ideal inside the integral image.

The only subring-specific inputs are the actual listed words, their eventual
latest-exponent bound, and the prescribed nt membership. Neither transfer
identities nor a conductor power are assumed. The generic rational-hull
clearing is used for arbitrary multipliers, without selecting another scale.
-/

noncomputable section
namespace UnconditionalCounterexample.SequenceExactTransfer

open Polynomial Filter TensorProduct StageRecursion ConstructionWords PrimaryChoices
open LocalAlgebra PoleTensorConductor

variable {Req : Requirements} (seq : Sequence Req)

theorem raw_nonzero : ∀ f ∈ Set.range seq.chain.raw, f ≠ 0 := by
  rintro f ⟨i, rfl⟩
  exact (seq.chain.raw_monic i).ne_zero

/-- Exact Lemma 6.1 for the actual sequence, using s=nu_p(n) from the same
prescribed integer n with nt∈T. Rational-hull recovery supplies only clearing
of arbitrary multipliers; it does not choose or enlarge this scale. -/
theorem power_ideal_subset_at_prescribed_scale
    (T : Subring (PoleAlgebra.generated (Set.range seq.chain.raw)))
    (y : ℕ → T) (stage : ℕ → ℕ) (hstage : Tendsto stage atTop atTop)
    (w : ∀ i, Word (stage i)) (bound : ℕ)
    (hbound : ∀ᶠ i in atTop, (w i).latestExponent ≤ bound)
    (hword : ∀ i, ((y i : PoleAlgebra.generated (Set.range seq.chain.raw)) : RatFunc ℚ) =
      ScheduledRecovery.generators seq.chain.raw seq.chain.exponent (stage i) ^ (w i).latestExponent *
        (∏ j ∈ Finset.range (stage i),
          ScheduledRecovery.generators seq.chain.raw seq.chain.exponent j ^ (w i).oldExponent j))
    (n : ℕ) (hn : 0 < n)
    (hnt : (n : PoleAlgebra.generated (Set.range seq.chain.raw)) *
      algebraMap ℚ[X] (PoleAlgebra.generated (Set.range seq.chain.raw)) X ∈ T)
    (j : ℕ) :
    ∀ z ∈ Ideal.span {algebraMap ℚ_[(primes j).val][X]
        (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[(primes j).val]
          (Set.range seq.chain.raw)))
        (((X - C (SequenceLocalTransfer.branch seq j false)) *
          (X - C (SequenceLocalTransfer.branch seq j true))) ^ bound)},
      z ∈ PoleTensorConductor.image (primes j).val (Set.range seq.chain.raw) (raw_nonzero seq) T := by
  let p := (primes j).val
  let s := padicValNat p n
  have hfrac (i : ℕ) : ((y i : PoleAlgebra.generated (Set.range seq.chain.raw)) : RatFunc ℚ) =
      algebraMap ℚ[X] (RatFunc ℚ) (seq.chain.raw (stage i)) ^ (w i).latestExponent /
        algebraMap ℚ[X] (RatFunc ℚ) ((GlobalPlans.globalPlan seq (stage i)).wordDen (w i)) := by
    rw [hword]
    have h := ConstructionRecovery.global_word_eq_fraction seq.chain.raw seq.chain.exponent
      (stage i) (GlobalPlans.globalPlan seq (stage i)) (GlobalPlans.globalPlan_E seq (stage i)) (w i)
    rwa [ConstructionRecovery.oldDenominator_eq_wordDen] at h
  have hclock : Tendsto (fun i => stage i + 1) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_succ (stage i)) hstage
  have hhull := ConstructionRecovery.hull_eq_top_of_sequence seq T y stage hstage w hword
  have hclear := power_clearing_ambientImage p (Set.range seq.chain.raw) (raw_nonzero seq) T hhull
  have hs : RatFunc.C (p : ℚ_[p]) ^ s * RatFunc.X ∈
      ambientImage p (Set.range seq.chain.raw) (raw_nonzero seq) T :=
    PaperConductorScale.prescribed_scale_mem p (Set.range seq.chain.raw) (raw_nonzero seq) T n hn hnt
  have hinv : (RatFunc.C (p : ℚ_[p]))⁻¹ ∈
      (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] (Set.range seq.chain.raw))).toSubring := by
    change (RatFunc.C (p : ℚ_[p]))⁻¹ ∈
      PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] (Set.range seq.chain.raw))
    rw [← map_inv₀]
    exact (PoleAlgebra.generated _).algebraMap_mem ((p : ℚ_[p])⁻¹)
  apply power_ideal_subset_of_ambient_multiples p (Set.range seq.chain.raw) (raw_nonzero seq) T
    (SequenceLocalTransfer.branch seq j false) (SequenceLocalTransfer.branch seq j true) bound
  apply padic_pair_conductor_power_of_eventual_word_transfers p s bound
    (SequenceLocalTransfer.branch seq j false) (SequenceLocalTransfer.branch seq j true)
    (SequenceLocalTransfer.branch_integral seq j false) (SequenceLocalTransfer.branch_integral seq j true)
    (ambientImage p (Set.range seq.chain.raw) (raw_nonzero seq) T)
    (PoleAlgebra.generated (ScalarExtension.extendedSet ℚ ℚ_[p] (Set.range seq.chain.raw))).toSubring
    (scalar_mem_ambientImage p (Set.range seq.chain.raw) (raw_nonzero seq) T) hs hinv hclear
    (fun i => stage i + 1) (fun i => (w i).latestExponent)
    (fun i => (seq.chain.raw (stage i)).map (algebraMap ℚ ℚ_[p]))
    (fun i => ((GlobalPlans.globalPlan seq (stage i)).wordDen (w i)).map (algebraMap ℚ ℚ_[p])) hclock
  filter_upwards [hbound, hstage.eventually
    (SequenceLocalTransfer.eventually_all_word_estimates seq j s)] with i hbi hlocal
  refine ⟨hbi, ?_, (hlocal (w i)).2⟩
  have hmem := (coe_mem_ambientImage_iff p (Set.range seq.chain.raw) (raw_nonzero seq) T _).mpr
    (TransportedIntegralImage.original_mem p _ _
      (ScalarExtension.tensorEquiv ℚ ℚ_[p] (Set.range seq.chain.raw) (raw_nonzero seq)) T (y i))
  have hH0 : (GlobalPlans.globalPlan seq (stage i)).wordDen (w i) ≠ 0 := by
    intro he
    have hne := SequenceLocalTransfer.global_wordDen_eval_ne_zero seq (stage i) (w i) j false
    simp only [he, eval₂_zero, ne_eq, not_true_eq_false] at hne
  have heq := ScalarExtension.embedding_one_tmul_fraction ℚ ℚ_[p] (Set.range seq.chain.raw)
    (raw_nonzero seq) (y i) ((seq.chain.raw (stage i)) ^ (w i).latestExponent)
    ((GlobalPlans.globalPlan seq (stage i)).wordDen (w i)) hH0
    (by simpa only [map_pow] using hfrac i)
  change ScalarExtension.embedding ℚ ℚ_[p] (Set.range seq.chain.raw) (raw_nonzero seq)
    (1 ⊗ₜ[ℚ] (y i : PoleAlgebra.generated (Set.range seq.chain.raw))) ∈
      ambientImage p (Set.range seq.chain.raw) (raw_nonzero seq) T at hmem
  rw [heq] at hmem
  simpa only [Polynomial.map_pow, map_pow, RatFunc.coePolynomial_eq_algebraMap] using hmem

end UnconditionalCounterexample.SequenceExactTransfer
