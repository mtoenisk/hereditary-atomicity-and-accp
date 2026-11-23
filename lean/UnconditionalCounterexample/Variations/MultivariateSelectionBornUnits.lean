import UnconditionalCounterexample.Variations.MultivariateSelectionGuards
import UnconditionalCounterexample.Variations.MultivariateSelectionFrozen

/-!
# Earlier polynomials remain units at new places

All primary and guard coordinates are assigned once. A polynomial that
predates an assignment is a unit there, by the concrete birth screens and
the coefficient models at every then-unprocessed prime.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain

variable {r : ℕ} {q : PrimeIndex} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable (L : LocalPrescription r q) (G : Geometry r K)

theorem inputs_processed (n : ℕ) : (localInput (requirements L G) n).primes = (permanentBatch L G n).processed :=
  (congrArg Batch.processed (actual_batch L G n)).symm

theorem inputs_aux (n : ℕ) : (localInput (requirements L G) n).aux = (permanentBatch L G n).aux :=
  (congrArg Batch.aux (actual_batch L G n)).symm

theorem guard_unit_of_earlier (p : PrimeIndex) (i : ℕ) (hi : i < firstAppearance L G p) :
    ((places L G).guard p).valuation (algebraMap _ (FunctionField (r+1)) (siteRaw L G i)) = 1 := by
  have hp : p ∉ (localInput (requirements L G) i).primes := by
    rw [inputs_processed]
    intro hm
    exact hi.not_ge (first_le L G (processed_covered L G i hm))
  obtain ⟨Q,hQ,_,hne⟩ := raw_good_reduction (requirements L G) i p hp
  apply (permanentFibre L G p).guard.unit_of_model _ Q hQ
  apply earlier_guard_avoids L G hi
  rwa [reduction_of_model hQ]

theorem primary_unit_of_earlier (hz : (0 : Fin (r+1) → K) ∈ G.fixed) (j i : ℕ) (hi : i < j/2) :
    ((places L G).primary j).valuation (algebraMap _ (FunctionField (r+1)) (siteRaw L G i)) = 1 := by
  classical
  apply (primaryBirth L G j).old_units
  rw [(valid_batch L G (j/2)).previous_eq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(⟨i,hi⟩ : Fin (j/2)),Finset.mem_univ _,rfl⟩,
    first_variable_not_dvd (requirements L G) hz i⟩

private def residueLeading (n : ℕ) (p : PrimeIndex) : ResiduePolys r p :=
  ∑ i : Fin (r+1), C ((n : ZMod p.val) ^ i.val) * X i

private theorem residueLeading_ne_zero (n : ℕ) (p : PrimeIndex) : residueLeading (r := r) n p ≠ 0 := by
  intro h
  have hh := congrArg (eval (Fin.cons (1 : ZMod p.val) (fun _ : Fin r => 0))) h
  simp [residueLeading,Fin.sum_univ_succ] at hh

theorem aux_guard_unit (n : ℕ) :
    let p := (permanentBatch L G n).aux
    ((places L G).guard p).valuation (algebraMap _ (FunctionField (r+1)) (siteRaw L G n)) = 1 := by
  classical
  let p := (localInput (requirements L G) n).aux
  have he : p = (permanentBatch L G n).aux := inputs_aux L G n
  rw [← he]
  have hh : p ∈ (table L G n).covered := by rw [(permanentBatch L G n).covered_eq,he]; exact Finset.mem_insert_self _ _
  have hnew : p ∉ (priorTable n (fun i : Fin n => siteChain L G i.val)).covered := fun hp =>
    (valid_batch L G n).aux_fresh (he ▸ (valid_batch L G n).copied hp)
  have hl : (permanentFibre L G p).guard.avoids (residueLeading n p) := by
    rw [← frozen L G hh]
    apply (valid_batch L G n).guards p hh hnew _ _ (residueLeading_ne_zero _ _)
    apply Finset.mem_union_right
    simp [he,residueLeading]
  obtain ⟨Q,hQ,hred⟩ := raw_auxiliary_model (requirements L G) n
  apply (permanentFibre L G p).guard.unit_of_model _ Q hQ
  rw [reduction_of_model hQ]
  have hmap := congrArg (MvPolynomial.map (modOne p) (σ := Fin (r+1))) hred
  change MvPolynomial.map (modOne p) (MvPolynomial.map (PadicInt.toZModPow 1) Q) = _ at hmap
  rw [map_map,modOne_comp] at hmap
  have hshape : MvPolynomial.map PadicInt.toZMod Q = residueLeading n p ^ (chain (requirements L G) n).degree := by
    simpa only [map_sum,map_mul,map_C,map_pow,map_natCast,map_X,residueLeading] using hmap
  rw [hshape]
  change aeval _ (_ ^ _) ≠ 0
  rw [map_pow]
  exact pow_ne_zero _ hl

theorem not_processed_raw_unit {p : PrimeIndex} {n : ℕ} (hp : p ∉ (permanentBatch L G n).processed) :
    ((places L G).guard p).valuation (algebraMap _ (FunctionField (r+1)) (siteRaw L G n)) = 1 := by
  rcases not_processed_cases L G hp with h | ⟨_,h⟩
  · exact guard_unit_of_earlier L G p n h
  · rw [h]
    exact aux_guard_unit L G n

theorem not_processed_guard_unit {p : PrimeIndex} {n : ℕ} (hp : p ∉ (permanentBatch L G n).processed) :
    ((places L G).guard p).valuation (RawWords.normalizedFactor
      (fun i => algebraMap _ (FunctionField (r+1)) (siteRaw L G i)) normalizationPower n) = 1 := by
  rw [RawWords.normalizedFactor,map_div₀,map_prod,not_processed_raw_unit L G hp]
  have hu (i : ℕ) (hi : i ∈ Finset.range n) :
      ((places L G).guard p).valuation ((algebraMap _ (FunctionField (r+1)) (siteRaw L G i)) ^ normalizationPower n) = 1 := by
    rw [map_pow,not_processed_raw_unit L G (fun h => hp (processed_mono L G (Finset.mem_range.mp hi).le h)),one_pow]
  rw [Finset.prod_eq_one hu, div_one]

end UnconditionalCounterexample.MultivariateSelection
