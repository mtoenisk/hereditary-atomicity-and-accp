import UnconditionalCounterexample.Variations.CalibrationSites
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Fresh correction primes and disjoint marked balls
Schur's theorem and Hensel lifting assign the signed order of the next
irreducible while keeping all frozen polynomials units on both balls. -/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Weighted
open Polynomial GuardSupport Filter Topology

def correctionOrder (k : ℤ) (b : Bool) : ℤ := if b then max (-k) 0 else max k 0

structure CorrectionBalls (f : ℚ[X]) (frozen : Finset ℚ[X]) (k : ℤ) where
  prime : PrimeIndex
  center : Bool → ℤ_[prime.val]
  radius : Bool → ℝ
  radius_pos : ∀ b, 0 < radius b
  disjoint : Disjoint (Metric.ball (center false) (radius false)) (Metric.ball (center true) (radius true))
  on_ball : ∀ b z, z ∈ Metric.ball (center b) (radius b) →
    aeval (z : ℚ_[prime.val]) f ≠ 0 ∧
    (aeval (z : ℚ_[prime.val]) f).valuation = correctionOrder k b ∧
    ∀ g ∈ frozen, ‖aeval (z : ℚ_[prime.val]) g‖ = 1

private theorem norm_of_clearing {p : ℕ} [Fact p.Prime] (x : ℤ_[p])
    {V : ℤ[X]} {d : ℤ} {q : ℚ[X]} (he : V.map (algebraMap ℤ ℚ) = C (d : ℚ) * q)
    (hd : IsUnit (d : ℤ_[p])) : ‖aeval x.val q‖ = ‖aeval x.val V‖ := by
  have h := congrArg (aeval x.val) he
  rw [aeval_map_algebraMap, map_mul, aeval_C, map_intCast] at h
  have hdn : ‖(d : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hd
  simpa only [norm_mul, hdn, one_mul] using (congrArg norm h).symm

private theorem norm_of_int_unit {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} {V : ℤ[X]}
    (h : IsUnit (aeval x V)) : ‖aeval x.val V‖ = 1 := by
  have he : aeval x.val V = ((aeval x V : ℤ_[p]) : ℚ_[p]) := aeval_algebraMap_apply ℚ_[p] x V
  rw [he]
  exact PadicInt.isUnit_iff.mp h

private theorem eval_unit_of_residue {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} {a : ℤ}
    {V : ℤ[X]} (hx : PadicInt.toZMod x = a) (ha : ¬ (p : ℤ) ∣ V.eval a) :
    IsUnit (aeval x V) := by
  apply intPolynomial_eval_unit_of_residue_nonzero
  rw [hx]
  exact (eval₂_at_apply (p := V) (Int.castRingHom (ZMod p)) a).trans_ne
    (fun hz => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))

private theorem eventually_norm_eval_eq {p : ℕ} [Fact p.Prime] (f : ℚ[X]) (x : ℤ_[p])
    (hf : aeval x.val f ≠ 0) :
    ∀ᶠ z : ℤ_[p] in 𝓝 x, ‖aeval z.val f‖ = ‖aeval x.val f‖ := by
  have hc : Continuous (fun z : ℤ_[p] => aeval z.val f) :=
    f.continuous_aeval.comp continuous_subtype_val
  have he : ∀ᶠ z : ℤ_[p] in 𝓝 x, aeval z.val f ∈ Metric.ball (aeval x.val f) ‖aeval x.val f‖ :=
    (hc.continuousAt (x := x)).eventually (Metric.ball_mem_nhds _ (norm_pos_iff.mpr hf))
  exact he.mono fun z hz => Padic.norm_eq_of_norm_sub_lt_right
    (by simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hz)

private theorem balls_of_centers {p : PrimeIndex} {f : ℚ[X]} {frozen : Finset ℚ[X]} {k : ℤ}
    (c : Bool → ℤ_[p.val]) (hsep : c false ≠ c true)
    (hc : ∀ b, aeval (c b).val f ≠ 0 ∧ (aeval (c b).val f).valuation = correctionOrder k b ∧
      ∀ g ∈ frozen, ‖aeval (c b).val g‖ = 1) :
    ∃ s : CorrectionBalls f frozen k, s.prime = p := by
  have hball (b : Bool) : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball (c b) r,
      ‖aeval z.val f‖ = ‖aeval (c b).val f‖ ∧ ∀ g ∈ frozen, ‖aeval z.val g‖ = 1 := by
    have hall : ∀ᶠ z : ℤ_[p.val] in 𝓝 (c b), ∀ g ∈ frozen, ‖aeval z.val g‖ = 1 := by
      apply (Filter.eventually_all_finset frozen).mpr
      intro g hg
      have hnorm := (hc b).2.2 g hg
      exact (eventually_norm_eval_eq g _ (norm_ne_zero_iff.mp (hnorm.trans_ne one_ne_zero))).mono
        fun _ he => he.trans hnorm
    exact Metric.mem_nhds_iff.mp ((eventually_norm_eval_eq _ _ (hc b).1).and hall)
  choose r hr h using hball
  let δ := dist (c false) (c true) / 2
  have hδ : 0 < δ := half_pos (dist_pos.mpr hsep)
  refine ⟨⟨p, c, fun b => min (r b) δ, fun b => lt_min (hr b) hδ, ?_, ?_⟩, rfl⟩
  · apply Set.disjoint_left.mpr
    intro z hz hw
    have hz' := lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right ..)
    have hw' := lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_right ..)
    rw [dist_comm z (c false)] at hz'
    have htri := dist_triangle (c false) z (c true)
    dsimp [δ] at hz' hw'
    linarith
  · intro b z hz
    obtain ⟨hn, hg⟩ := h b z (Metric.ball_subset_ball (min_le_left ..) hz)
    have hne := norm_ne_zero_iff.mp (hn.trans_ne (norm_ne_zero_iff.mpr (hc b).1))
    exact ⟨hne, (EvaluationChoices.valuation_eq_of_norm_eq _ hne (hc b).1 hn).trans (hc b).2.1, hg⟩

/-- A fresh prime realizes the requested signed difference throughout two balls
and makes every previously recorded polynomial a unit there. -/
theorem exists_correctionBalls (f : ℚ[X]) (hirr : Irreducible f) (frozen : Finset ℚ[X])
    (hn : ∀ g ∈ frozen, g ≠ 0) (hcop : ∀ g ∈ frozen, IsCoprime f g)
    (k : ℤ) (cutoff : ℕ) : ∃ s : CorrectionBalls f frozen k, cutoff < s.prime.val := by
  classical
  obtain ⟨d, F, hd, hF, he⟩ := exists_integer_multiple f hirr.ne_zero
  choose e V he0 hV heq using fun g : frozen => exists_integer_multiple g.val (hn _ g.property)
  let A (g : frozen) := C (e g) * V g
  let G := C d * ∏ g, A g
  have hG : G ≠ 0 := mul_ne_zero (C_ne_zero.mpr hd)
    (Finset.prod_ne_zero_iff.mpr fun g _ => mul_ne_zero (C_ne_zero.mpr (he0 g)) (hV g))
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hdu : IsUnit (C (d : ℚ) : ℚ[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hdq)
  have hdegree : F.natDegree ≠ 0 := by
    have he' := congrArg natDegree he
    rw [natDegree_map_eq_of_injective (f := algebraMap ℤ ℚ) Int.cast_injective, natDegree_C_mul hdq] at he'
    exact he' ▸ hirr.natDegree_pos.ne'
  have hcG : IsCoprime (F.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)) := by
    rw [he, isCoprime_mul_unit_left_left hdu]
    simp only [G, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
    change IsCoprime f (C (d : ℚ) * ∏ g, (A g).map (algebraMap ℤ ℚ))
    rw [isCoprime_mul_unit_left_right hdu]
    apply IsCoprime.prod_right
    intro g _
    have hu : IsUnit (C (e g : ℚ) : ℚ[X]) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast he0 g))
    change IsCoprime f ((C (e g) * V g).map _)
    rw [Polynomial.map_mul, Polynomial.map_C, heq g]
    change IsCoprime f (C (e g : ℚ) * (C (e g : ℚ) * g.val))
    rw [isCoprime_mul_unit_left_right hu, isCoprime_mul_unit_left_right hu]
    exact hcop _ g.property
  have hc : IsCoprime (F.map (Int.castRingHom ℚ)) ((F.derivative * G).map (Int.castRingHom ℚ)) := by
    rw [Polynomial.map_mul, ← derivative_map]
    apply IsCoprime.mul_right _ hcG
    change IsCoprime (F.map (algebraMap ℤ ℚ)) (F.map (algebraMap ℤ ℚ)).derivative
    rw [he, derivative_C_mul, isCoprime_mul_units_left hdu hdu]
    exact hirr.separable
  let H := F * G
  obtain ⟨b, hb⟩ := (eventually_eval_ne_zero_cofinite (mul_ne_zero hF hG)).exists
  obtain ⟨q, a, hq, hbig, hroot, hav⟩ := Calibration.exists_prime_root_avoiding F _ hdegree hc
    (max cutoff (H.eval b).natAbs)
  let p : PrimeIndex := ⟨q, hq⟩
  let : Fact q.Prime := ⟨hq⟩
  have hsafe : ¬ (q : ℤ) ∣ H.eval b := fun hh =>
    Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hb) ((le_max_right ..).trans_lt hbig) (Int.natCast_dvd.mp hh)
  rw [eval_mul] at hav
  have hsimple : ¬ (q : ℤ) ∣ F.derivative.eval a := fun hh => hav (dvd_mul_of_dvd_left hh _)
  have hGa : ¬ (q : ℤ) ∣ G.eval a := fun hh => hav (dvd_mul_of_dvd_right hh _)
  have hgunit (x : ℤ_[q]) (hgu : IsUnit (aeval x G)) :
      IsUnit (d : ℤ_[q]) ∧ ∀ g ∈ frozen, ‖aeval x.val g‖ = 1 := by
    have hparts : IsUnit (d : ℤ_[q]) ∧ IsUnit (aeval x (∏ g, A g)) := by
      simpa [G, -map_prod] using hgu
    refine ⟨hparts.1, ?_⟩
    intro g hg
    let i : frozen := ⟨g, hg⟩
    have hfactor := isUnit_of_dvd_unit ((aeval x).toRingHom.map_dvd
      (Finset.dvd_prod_of_mem A (Finset.mem_univ i))) hparts.2
    have hpair : IsUnit (e i : ℤ_[q]) ∧ IsUnit (aeval x (V i)) := by simpa [A] using hfactor
    exact (norm_of_clearing x (heq i) hpair.1).trans (norm_of_int_unit hpair.2)
  have safe (x : ℤ_[q]) (hx : PadicInt.toZMod x = b) :
      aeval x.val f ≠ 0 ∧ (aeval x.val f).valuation = 0 ∧ ∀ g ∈ frozen, ‖aeval x.val g‖ = 1 := by
    have h : IsUnit (aeval x F) ∧ IsUnit (aeval x G) := by
      simpa [H] using eval_unit_of_residue hx hsafe
    obtain ⟨hdx, hgs⟩ := hgunit _ h.2
    have hnrm := (norm_of_clearing x he hdx).trans (norm_of_int_unit h.1)
    have hne := norm_ne_zero_iff.mp (hnrm.trans_ne one_ne_zero)
    refine ⟨hne, ?_, hgs⟩
    simpa using EvaluationChoices.valuation_eq_of_norm_eq q hne
      (one_ne_zero : (1 : ℚ_[q]) ≠ 0) (hnrm.trans norm_one.symm)
  have hsb := safe (b : ℤ_[q]) (by simp)
  have hcents : ∃ c : Bool → ℤ_[q], c false ≠ c true ∧
      ∀ i, aeval (c i).val f ≠ 0 ∧ (aeval (c i).val f).valuation = correctionOrder k i ∧
        ∀ g ∈ frozen, ‖aeval (c i).val g‖ = 1 := by
    by_cases hk : k = 0
    · subst k
      have hs' := safe ((b + q : ℤ) : ℤ_[q]) (by simp)
      refine ⟨fun i => if i then ((b + q : ℤ) : ℤ_[q]) else (b : ℤ_[q]), ?_, ?_⟩
      · simp only [Bool.false_eq_true, ite_false, ite_true, Int.cast_add, Int.cast_natCast]
        exact fun hh => (Nat.cast_ne_zero.mpr hq.ne_zero : (q : ℤ_[q]) ≠ 0) (by simpa using hh.symm)
      · intro i
        cases i
        · simpa [correctionOrder] using hsb
        · simpa [correctionOrder] using hs'
    · obtain ⟨x, _, hx, hxn, hxo⟩ := Calibration.exists_transcendental_lift q F a k.natAbs
        (Int.natAbs_pos.mpr hk) hroot hsimple
      obtain ⟨hdx, hxg⟩ := hgunit _ (eval_unit_of_residue hx hGa)
      have hnm := norm_of_clearing x he hdx
      have hxne := norm_ne_zero_iff.mp (hnm.trans_ne (norm_ne_zero_iff.mpr hxn))
      have hyo := (EvaluationChoices.valuation_eq_of_norm_eq q hxne hxn hnm).trans hxo
      have hdiff : x ≠ (b : ℤ_[q]) := by
        intro heq'
        subst x
        rw [hsb.2.1] at hyo
        exact hk (by omega)
      by_cases hpos : 0 < k
      · refine ⟨fun i => if i then (b : ℤ_[q]) else x, by simpa using hdiff, ?_⟩
        intro i
        cases i
        · exact ⟨hxne, hyo.trans (by simp only [Int.natCast_natAbs, abs_of_pos hpos, correctionOrder, Bool.false_eq_true, ite_false, max_eq_left hpos.le]), hxg⟩
        · simpa [correctionOrder, max_eq_right (by omega : -k ≤ 0)] using hsb
      · refine ⟨fun i => if i then x else (b : ℤ_[q]), by simpa using hdiff.symm, ?_⟩
        intro i
        cases i
        · simpa [correctionOrder, max_eq_right (by omega : k ≤ 0)] using hsb
        · exact ⟨hxne, hyo.trans (by simp only [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hpos), correctionOrder, ite_true, max_eq_left (neg_nonneg.mpr (le_of_not_gt hpos))]), hxg⟩
  obtain ⟨c, hdiff, hvals⟩ := hcents
  obtain ⟨s, hs⟩ := balls_of_centers (p := p) c hdiff hvals
  exact ⟨s, hs ▸ (le_max_left ..).trans_lt hbig⟩

/-- The coprimality conditions in a correction stage follow from the
enumeration's use of distinct monic irreducibles. -/
theorem exists_correctionBalls_of_monic (f : ℚ[X]) (hm : f.Monic) (hi : Irreducible f)
    (frozen : Finset ℚ[X]) (hnew : f ∉ frozen)
    (hfrozen : ∀ g ∈ frozen, g.Monic ∧ Irreducible g) (k : ℤ) (cutoff : ℕ) :
    ∃ s : CorrectionBalls f frozen k, cutoff < s.prime.val := by
  apply exists_correctionBalls f hi frozen (fun g hg => (hfrozen g hg).2.ne_zero) _ k cutoff
  intro g hg
  apply (hi.isCoprime_or_dvd g).resolve_right
  intro hd
  have he := eq_of_monic_of_associated hm (hfrozen g hg).1 (hi.associated_of_dvd (hfrozen g hg).2 hd)
  exact hnew (he ▸ hg)

/-- When the next polynomial has already been processed, both marked balls
can keep it and all of the other frozen polynomials units. -/
theorem exists_unitBalls (f : ℚ[X]) (hf : f ≠ 0) (frozen : Finset ℚ[X])
    (hn : ∀ g ∈ frozen, g ≠ 0) (cutoff : ℕ) :
    ∃ s : CorrectionBalls f frozen 0, cutoff < s.prime.val := by
  classical
  let S := insert f frozen
  have hS : ∀ g ∈ S, g ≠ 0 := by simpa [S] using And.intro hf hn
  obtain ⟨a, ha⟩ := (eventually_eval_ne_zero_cofinite
    (Finset.prod_ne_zero_iff.mpr hS : (∏ g ∈ S, g) ≠ 0)).exists
  rw [eval_prod, Finset.prod_ne_zero_iff] at ha
  have hcop (g : ℚ[X]) (hg : g ∈ S) : IsCoprime (X - C a) g :=
    ((irreducible_X_sub_C a).isCoprime_or_dvd g).resolve_right
      fun h => ha g hg (dvd_iff_isRoot.mp h)
  obtain ⟨s, hs⟩ := exists_correctionBalls (X - C a) (irreducible_X_sub_C a) S hS hcop 0 cutoff
  refine ⟨⟨s.prime, s.center, s.radius, s.radius_pos, s.disjoint, ?_⟩, hs⟩
  intro b z hz
  have h := (s.on_ball b z hz).2.2
  have hnorm := h f (Finset.mem_insert_self ..)
  have hne := norm_ne_zero_iff.mp (hnorm.trans_ne one_ne_zero)
  refine ⟨hne, ?_, fun g hg => h g (Finset.mem_insert_of_mem hg)⟩
  have hv := EvaluationChoices.valuation_eq_of_norm_eq s.prime.val hne
    (one_ne_zero : (1 : ℚ_[s.prime.val]) ≠ 0) (hnorm.trans norm_one.symm)
  cases b <;> simpa [correctionOrder] using hv

end UnconditionalCounterexample.Hierarchy.Weighted
