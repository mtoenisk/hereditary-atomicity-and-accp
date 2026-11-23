import UnconditionalCounterexample.Variations.CalibrationSites
import UnconditionalCounterexample.Variations.DyadicDeviations
import UnconditionalCounterexample.Variations.UnivariateBirths

/-!
# Allocating calibration fibres on the recursive prefix

Besides the frozen integer factors, a fresh site must see every preceding
rational numerator as a unit on both branches. Clearing their coefficients
before choosing the prime puts these constraints into the same polynomial
avoidance test as the retained factors.
-/

noncomputable section
namespace UnconditionalCounterexample.Calibration

open Polynomial GuardSupport RecursivePrefix Variations.Univariate

/-- A requested auxiliary fibre ready for insertion into the next batch. -/
structure AtPrefix {n : ℕ} (P : Prefix n) (f G : ℤ[X]) (l : ℕ)
    extends AuxiliarySite f G l n where
  fresh : prime ∉ P.state.assignment.primes
  old_primary : ∀ j : Fin n, ‖aeval primary.val.val (P.raw j)‖ = 1
  old_guard : ∀ j : Fin n, ‖aeval guard.value.val (P.raw j)‖ = 1

def AtPrefix.births {n : ℕ} {P : Prefix n} {f G : ℤ[X]} {l : ℕ}
    (a : AtPrefix P f G l) : Births P :=
  Births.singleton P a.prime a.fresh a.guard a.birth a.old_guard (some a.primary)

private theorem norm_eq_one_of_clearing {p : ℕ} [Fact p.Prime] (x : ℤ_[p])
    {V : ℤ[X]} {d : ℤ} {q : ℚ[X]} (h : V.map (algebraMap ℤ ℚ) = C (d : ℚ) * q)
    (hu : IsUnit (aeval x (C d * V))) : ‖aeval x.val q‖ = 1 := by
  have hsplit : IsUnit (d : ℤ_[p]) ∧ IsUnit (aeval x V) := by simpa using hu
  have hv : ‖V.eval₂ (Int.castRingHom ℚ_[p]) x.val‖ = 1 := by
    rw [← coe_intPolynomial_eval]
    exact PadicInt.isUnit_iff.mp hsplit.2
  have hd : ‖(d : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hsplit.1
  have heval := congrArg (Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) x.val) h
  have hc : (algebraMap ℚ ℚ_[p]).comp (algebraMap ℤ ℚ) =
      Int.castRingHom ℚ_[p] := Subsingleton.elim _ _
  rw [eval₂_map, eval₂_mul, eval₂_C, hc, map_intCast] at heval
  have hnorm := congrArg norm heval
  rw [norm_mul, hd, one_mul, hv] at hnorm
  exact hnorm.symm

/-- The prime is fresh for the actual preceding sequence; both evaluations
preserve all its raw numerator units and the units of the frozen product. -/
theorem exists_atPrefix {n : ℕ} (P : Prefix n) (f G : ℤ[X]) (hd : f.natDegree ≠ 0)
    (hprim : f.IsPrimitive) (hirr : Irreducible f) (hG : G ≠ 0)
    (hc : IsCoprime (f.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)))
    (hraw : ∀ j : Fin n, IsCoprime (f.map (algebraMap ℤ ℚ)) (P.raw j))
    (cutoff l : ℕ) (hl : 0 < l) :
    ∃ s : AtPrefix P f G l, cutoff < s.prime.val := by
  classical
  choose d V hdV hV he using fun j => exists_integer_multiple (P.raw j) (P.monic j).ne_zero
  let A (j : Fin n) := C (d j) * V j
  let frozen := G * ∏ j, A j
  have hn (j : Fin n) : A j ≠ 0 := mul_ne_zero (C_ne_zero.mpr (hdV j)) (hV j)
  have hfrozen : frozen ≠ 0 := mul_ne_zero hG (Finset.prod_ne_zero_iff.mpr (fun j _ => hn j))
  have hcop : IsCoprime (f.map (algebraMap ℤ ℚ)) (frozen.map (algebraMap ℤ ℚ)) := by
    simp only [frozen, Polynomial.map_mul, Polynomial.map_prod]
    apply hc.mul_right
    apply IsCoprime.prod_right
    intro j _
    have hu : IsUnit (C (d j : ℚ)) :=
      isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hdV j))
    change IsCoprime _ ((C (d j) * V j).map _)
    rw [Polynomial.map_mul, Polynomial.map_C, he j]
    change IsCoprime _ (C (d j : ℚ) * (C (d j : ℚ) * P.raw j))
    rw [isCoprime_mul_unit_left_right hu, isCoprime_mul_unit_left_right hu]
    exact hraw j
  let bound := P.state.assignment.primes.sup Subtype.val
  obtain ⟨s, hs⟩ := exists_auxiliary_site f frozen hd hprim hirr hfrozen hcop (max cutoff bound) n l hl
  have hprev : s.prime ∉ P.state.assignment.primes := by
    intro hmem
    exact (not_le_of_gt hs) ((Finset.le_sup (f := Subtype.val) hmem).trans (le_max_right _ _))
  have hfactor {x : ℤ_[s.prime.val]} (hx : IsUnit (aeval x frozen)) :
      IsUnit (aeval x G) ∧ ∀ j : Fin n, ‖aeval x.val (P.raw j)‖ = 1 := by
    have hpart : IsUnit (aeval x G) ∧ IsUnit (aeval x (∏ j, A j)) := by
      simpa [frozen, -map_prod] using hx
    refine ⟨hpart.1, fun j => norm_eq_one_of_clearing x (he j) ?_⟩
    exact isUnit_of_dvd_unit ((aeval x).toRingHom.map_dvd
      (Finset.dvd_prod_of_mem A (Finset.mem_univ j))) hpart.2
  obtain ⟨hαG, hα⟩ := hfactor s.frozen_primary
  obtain ⟨hβG, hβ⟩ := hfactor s.frozen_guard
  exact ⟨⟨⟨s.prime, s.guard, s.birth, s.primary, s.value_ne_zero, s.value_order,
    s.guard_unit, hαG, hβG⟩, hprev, hα, hβ⟩, (le_max_left ..).trans_lt hs⟩

/-- One signed, nonzero dyadic discrepancy is removed by one actual auxiliary
fibre on the prefix. The weight index and the new rational prime can both be
taken above their independently specified lower bounds. -/
theorem exists_correction {n : ℕ} (P : Prefix n) (f G : ℤ[X]) (hd : f.natDegree ≠ 0)
    (hprim : f.IsPrimitive) (hirr : Irreducible f) (hG : G ≠ 0)
    (hc : IsCoprime (f.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)))
    (hraw : ∀ j : Fin n, IsCoprime (f.map (algebraMap ℤ ℚ)) (P.raw j))
    {J : Bool → Type*} {Gd H : Type*} (profile : DyadicDeviations.Profile J Gd H)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (k : Bool) (target : ℤ) (cutoff L : ℕ)
    (hne : (target : ℚ) - profile.signedMass index sign k ≠ 0) :
    ∃ i ≥ L, ∃ l : ℕ, ∃ s : AtPrefix P f G l, cutoff < s.prime.val ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        profile.signedMass index sign k + ε * ((aeval s.primary.val.val f).valuation : ℚ) *
          DyadicProfiles.weight i = target := by
  obtain ⟨i, hi, l, hl, hweight⟩ := profile.exists_calibration index sign k target L hne
  obtain ⟨s, hs⟩ := exists_atPrefix P f G hd hprim hirr hG hc hraw cutoff l hl
  refine ⟨i, hi, l, s, hs, ?_⟩
  rcases hweight with hpos | hneg
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [s.value_order]
    push_cast
    linarith
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [s.value_order]
    push_cast
    linarith

end UnconditionalCounterexample.Calibration
