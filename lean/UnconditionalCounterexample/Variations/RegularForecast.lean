import UnconditionalCounterexample.Variations.RegularReservations
import UnconditionalCounterexample.Variations.FreezingCalendar

/-!
# Forecast orders at new regular dyadic primes

At a regular site over centre c the only monic irreducible contributing
positive primary order is X − c itself. Its order is exactly one. Every
frozen monic irreducible, including X − c, is a unit at the guard.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.RegularForecast

open Polynomial GuardSupport PaperGuardStages RecursivePrefix RegularReservations

def centreFactor (c : ℕ) : ℚ[X] := X - C (c : ℚ)

/-- The erased factor is the only possible obstruction to screening the
primary by its residue at the centre. -/
theorem away {f : ℚ[X]} (hf : f.Monic) (hirr : Irreducible f) (c : ℕ)
    (hne : f ≠ centreFactor c) : f.eval (c : ℚ) ≠ 0 := by
  intro hz
  have hd : centreFactor c ∣ f := dvd_iff_isRoot.mpr hz
  exact hne (eq_of_monic_of_associated (monic_X_sub_C _) hf
    ((irreducible_X_sub_C _).associated_of_dvd hirr hd)).symm

/-- Arbitrarily many regular labels can be placed simultaneously even when
the frozen set contains both endpoints. -/
theorem exists_family {I : Type*} {n : ℕ} (P : Prefix n) (labels : Finset I)
    (c : I → ℕ) (hc : ∀ i, c i = 0 ∨ c i = 1)
    (frozen : Finset ℚ[X]) (hhor : ∀ f ∈ frozen, f.Monic ∧ Irreducible f)
    (avoid : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ e : (i : labels) → Entry P (c i.val) (frozen.erase (centreFactor (c i.val))),
      Function.Injective (fun i => (e i).prime) ∧
        ∀ i, cutoff < (e i).prime.val ∧ (e i).prime ∉ avoid := by
  refine RegularReservations.exists_family P labels c hc (fun i => frozen.erase (centreFactor (c i))) ?_ ?_ avoid cutoff
  · intro i f h
    exact (hhor f (Finset.mem_of_mem_erase h)).1
  · intro i f h
    obtain ⟨hm,hr⟩ := hhor f (Finset.mem_of_mem_erase h)
    exact away hm hr _ (Finset.ne_of_mem_erase h)

private theorem zero_order {p : ℕ} [Fact p.Prime] {z : ℚ_[p]} (hn : ‖z‖ = 1) : z.valuation = 0 := by
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (hn ▸ one_ne_zero)
  simpa using EvaluationChoices.valuation_eq_of_norm_eq p hz (one_ne_zero : (1 : ℚ_[p]) ≠ 0)
    (hn.trans norm_one.symm)

/-- The actual two branch orders on each member of the entire frozen set. -/
theorem entry_orders {n c : ℕ} {P : Prefix n} {frozen : Finset ℚ[X]}
    (e : Entry P c (frozen.erase (centreFactor c))) (hc : c = 0 ∨ c = 1)
    {f : ℚ[X]} (hf : f ∈ frozen) :
    (aeval e.primary.val.val f).valuation = (if f = centreFactor c then 1 else 0) ∧
      (aeval e.guard.value.val f).valuation = 0 := by
  by_cases he : f = centreFactor c
  · simp only [he, ite_true]
    subst f
    have hguard : ‖e.guard.value.val - (c : ℚ_[e.prime.val])‖ = 1 := by
      rcases hc with rfl | rfl
      · simpa using PadicInt.isUnit_iff.mp e.guard.unit
      · have h := UnivariateCentres.difference_unit (α := (1 : ℤ_[e.prime.val])) (β := e.guard.value)
          (by simpa using e.guard_residue_ne_one)
        simpa only [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, Nat.cast_one] using
          PadicInt.isUnit_iff.mp h
    simpa [centreFactor] using And.intro e.order (zero_order hguard)
  · simp only [he, ite_false]
    have h := e.frozen_units f (Finset.mem_erase.mpr ⟨he,hf⟩)
    exact ⟨zero_order h.1, zero_order h.2⟩

/-- Passing to a chosen primitive integral model leaves both orders intact
at every prime where the scalar multiple is a unit. -/
theorem model_orders {n c : ℕ} {P : Prefix n} {frozen : Finset ℚ[X]}
    (e : Entry P c (frozen.erase (centreFactor c))) (hc : c = 0 ∨ c = 1)
    {f : ℚ[X]} (hf : f ∈ frozen) (F : ℤ[X]) (q : ℚ)
    (hm : F.map (Int.castRingHom ℚ) = C q * f) (hq : ‖(q : ℚ_[e.prime.val])‖ = 1) :
    (aeval e.primary.val.val F).valuation = (if f = centreFactor c then 1 else 0) ∧
      (aeval e.guard.value.val F).valuation = 0 := by
  have same (a : ℚ_[e.prime.val]) (ha : Transcendental ℚ a) :
      (aeval a F).valuation = (aeval a f).valuation := by
    have eq := congrArg (Polynomial.aeval a) hm
    have comp : (algebraMap ℚ ℚ_[e.prime.val]).comp (Int.castRingHom ℚ) =
        algebraMap ℤ ℚ_[e.prime.val] := Subsingleton.elim _ _
    simp only [map_mul, aeval_C] at eq
    rw [aeval_def, eval₂_map, comp, ← aeval_def] at eq
    have hne : aeval a f ≠ 0 := by
      intro hv
      have hz := transcendental_iff.mp ha f hv
      by_cases h : f = centreFactor c
      · exact (monic_X_sub_C _).ne_zero (h.symm.trans hz)
      · have h1 := (e.frozen_units f (Finset.mem_erase.mpr ⟨h,hf⟩)).2
        simp [hz] at h1
    have hq' : (q : ℚ_[e.prime.val]) ≠ 0 := norm_ne_zero_iff.mp (hq ▸ one_ne_zero)
    change aeval a F = (q : ℚ_[e.prime.val]) * aeval a f at eq
    rw [eq, Padic.valuation_mul hq' hne, zero_order hq, zero_add]
  rw [same _ e.primary.property.1, same _ e.guard.transcendental]
  exact entry_orders e hc hf

end UnconditionalCounterexample.Variations.RegularForecast
