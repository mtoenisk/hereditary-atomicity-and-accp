import UnconditionalCounterexample.Variations.PrivateGuardsTablePermanence

/-! # Unit values of mixed generators before the birth of a public site -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection MultiDomain WithZero

variable {r d : ℕ} {K : Type*} [Field K] [CharZero K]
  (P : TablePolicy r K) (q : PrimeIndex) (c : Fin (r+1) → ℚ) (C : Config r d)

local notation "liveRule" => tableRule P q c
local notation "T" => publicPath P q c C
local notation "B" => family C liveRule
private abbrev mapF {r : ℕ} : Poly r →+* Variations.FunctionField (r+1) := algebraMap _ _

theorem raw_main_model (n : ℕ) (p : PrimeIndex) (hp : p ∉ ((T).batch n).processed) :
    ∃ Q : MvPolynomial (Fin (r+1)) ℤ_[p.val],
      MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (main C liveRule n) ∧
      MvPolynomial.map PadicInt.toZMod Q ≠ 0 := by
  obtain ⟨hi,H⟩ := (accepted C liveRule n).main_ok
  change p ∉ (event C liveRule n).entry.memory.processed at hp
  rw [H.2.1] at hp
  exact (event C liveRule n).entry.good_model n p _ H.2.2.2.2.2.2.2 hp

theorem guard_old_main {p : PrimeIndex} {n : ℕ} (hn : n < (T).firstAppearance p) :
    ((T).places.guard p).valuation (mapF (main C liveRule n)) = 1 := by
  obtain ⟨Q,hQ,hred⟩ := raw_main_model P q c C n p
    (fun hm => hn.not_ge ((T).first_le ((T).processed_covered n hm)))
  apply ((T).permanentFibre p).guard.unit_of_model _ Q hQ
  apply (T).earlier_guard_avoids (main_mem_old P q c C hn)
  rwa [reduction_of_model hQ]

theorem guard_old_puncture {p : PrimeIndex} {j n : ℕ} (hp : p ∉ ((T).batch n).processed) (hj : j < n) :
    ((T).places.guard p).valuation (mapF (puncture C liveRule j)) = 1 := by
  have hbad : p ∉ badPrimes (puncture C liveRule j) := fun h =>
    hp ((path_extra P q c C n).1 (extra_bad (before C liveRule n) ⟨j,hj⟩ h))
  obtain ⟨Q,hQ,hred⟩ := good_model_of_not_mem_badPrimes _ (event C liveRule j).irreducible_puncture.ne_zero p hbad
  apply ((T).permanentFibre p).guard.unit_of_model _ Q hQ
  apply (T).earlier_guard_avoids (puncture_mem_old P q c C (hj.trans_le
    (Nat.le_of_not_lt fun h => hp ((T).eventual_processed p h))))
  rwa [reduction_of_model hQ]

private def residueLeading (n : ℕ) (p : PrimeIndex) : ResiduePolys r p :=
  ∑ i : Fin (r+1), MvPolynomial.C ((n : ZMod p.val) ^ i.val) * X i

private theorem residueLeading_ne (n : ℕ) (p : PrimeIndex) : residueLeading (r := r) n p ≠ 0 := by
  intro h
  have hv := congrArg (eval (Fin.cons (1 : ZMod p.val) (fun _ : Fin r => 0))) h
  simp [residueLeading,Fin.sum_univ_succ] at hv

theorem guard_aux_main (n : ℕ) :
    ((T).places.guard ((T).batch n).aux).valuation (mapF (main C liveRule n)) = 1 := by
  classical
  let p := ((T).batch n).aux
  have hp : p ∈ ((T).table n).covered := by rw [((T).batch n).covered_eq]; exact Finset.mem_insert_self ..
  have hnew : p ∉ (previousTable (T).batch n).covered := fun h => ((T).valid n).aux_fresh (((T).valid n).copied h)
  have hl : ((T).permanentFibre p).guard.avoids (residueLeading n p) := by
    rw [← (T).frozen hp]
    apply ((T).valid n).guards p hp hnew _ _ (residueLeading_ne _ _)
    apply Finset.mem_union_right
    simp [p,residueLeading]
  obtain ⟨hi,H⟩ := (accepted C liveRule n).main_ok
  let u := (event C liveRule n).entry
  have he : p = (tablePrescription P q c (before C liveRule n) hi).aux := congrArg Batch.aux H.2.1
  obtain ⟨Q,hQ,hred⟩ := u.aux_model n p (by rw [he]; exact H.2.2.2.2.2.2.1)
  apply ((T).permanentFibre p).guard.unit_of_model _ Q hQ
  rw [reduction_of_model hQ]
  have hmap := congrArg (MvPolynomial.map (modOne p) (σ := Fin (r+1))) hred
  change MvPolynomial.map (modOne p) (MvPolynomial.map (PadicInt.toZModPow 1) Q) = _ at hmap
  rw [map_map,modOne_comp] at hmap
  have hshape : MvPolynomial.map PadicInt.toZMod Q = residueLeading n p ^ u.degree := by
    simpa only [map_sum,map_mul,map_C,map_pow,map_natCast,map_X,residueLeading] using hmap
  rw [hshape]
  change aeval _ (_ ^ _) ≠ 0
  rw [map_pow]
  exact pow_ne_zero _ hl

theorem guard_unprocessed_main {p : PrimeIndex} {n : ℕ} (hp : p ∉ ((T).batch n).processed) :
    ((T).places.guard p).valuation (mapF (main C liveRule n)) = 1 := by
  rcases (T).not_processed_cases hp with h | ⟨_,he⟩
  · exact guard_old_main P q c C h
  · rw [he]
    exact guard_aux_main P q c C n

private theorem normalized_unit (v : Valuation (FunctionField (r+1)) ℤᵐ⁰) (n : ℕ)
    (hF : ∀ i ≤ n, v (mapF (main C liveRule i)) = 1) (hG : ∀ i < n, v (mapF (puncture C liveRule i)) = 1) :
    v ((B).generator mixedPower n) = 1 := by
  change v (normalizedMain (fun i => mapF (main C liveRule i)) (fun i => mapF (puncture C liveRule i)) mixedPower n) = 1
  rw [normalizedMain,map_div₀,hF n le_rfl,map_prod]
  have hu (j : ℕ) (hj : j ∈ Finset.range n) :
      v ((mapF (main C liveRule j) * mapF (puncture C liveRule j))^mixedPower n) = 1 := by
    rw [map_pow,map_mul,hF j (Finset.mem_range.mp hj).le,hG j (Finset.mem_range.mp hj),mul_one,one_pow]
  rw [Finset.prod_eq_one hu,div_one]

theorem primary_unborn_generator (j n : ℕ) (hn : n < j/2) :
    ((T).places.primary j).valuation ((B).generator mixedPower n) = 1 :=
  normalized_unit P q c C _ _ (fun i hi => primary_old_main P q c C j i (hi.trans_lt hn))
    (fun i hi => primary_old_puncture P q c C j i (hi.trans hn))

theorem guard_unprocessed_generator {p : PrimeIndex} {n : ℕ} (hp : p ∉ ((T).batch n).processed) :
    ((T).places.guard p).valuation ((B).generator mixedPower n) = 1 :=
  normalized_unit P q c C _ _ (fun _ hi => guard_unprocessed_main P q c C (fun hm => hp ((T).processed_mono hi hm)))
    (fun _ hi => guard_old_puncture P q c C hp hi)

end UnconditionalCounterexample.Variations.PrivateGuards.Live
