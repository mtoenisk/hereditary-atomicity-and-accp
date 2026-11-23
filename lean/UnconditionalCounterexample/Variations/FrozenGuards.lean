import UnconditionalCounterexample.Variations.UnivariateGuards
import UnconditionalCounterexample.Variations.UnivariateExtraction
import UnconditionalCounterexample.Variations.UnivariateValues
import UnconditionalCounterexample.ConstructionReturns

/-!
# Uniform guard screening for a freezing round

The cutoff for a finite family of rational polynomials depends only on that
family. Once the batch covers it, every later guard, including a guard chosen
for a calibration, evaluates the frozen family in units. The same cutoff can
be requested even at the initial stage.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.FrozenGuards

open Polynomial Filter GuardSupport PaperGuardStages RecursivePrefix Univariate CombinedGuardStep

private theorem uniform_integer (F : ℤ[X]) (hF : F ≠ 0) :
    ∃ N : ℕ, ∀ (p : PrimeIndex), N ≤ p.val → ∀ g : Guard p, 0 < g.birth →
      ‖F.eval₂ (Int.castRingHom ℚ_[p.val]) g.value.val‖ = 1 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (LogarithmicGuards.eventually_natAbs_eval_bounds_on_log_interval F hF)
  refine ⟨N, fun p hp g hb => ?_⟩
  obtain ⟨lo,hi⟩ := g.logarithmic hb
  obtain ⟨hpos,hlt⟩ := hN _ hp g.representative lo hi
  rw [← coe_intPolynomial_eval]
  apply PadicInt.isUnit_iff.mp
  apply intPolynomial_eval_unit_of_residue_nonzero
  rw [g.residue]
  have he : F.eval₂ (Int.castRingHom (ZMod p.val)) (g.representative : ZMod p.val) =
      ((F.eval (g.representative : ℤ) : ℤ) : ZMod p.val) := by
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using
      Polynomial.eval₂_at_apply (p := F) (Int.castRingHom (ZMod p.val)) (g.representative : ℤ)
  rw [he]
  intro hz
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hle := Int.natAbs_le_of_dvd_ne_zero hd (Int.natAbs_pos.mp hpos)
  exact (not_le_of_gt hlt) (by simpa using hle)

private theorem uniform_polynomial (f : ℚ[X]) (hf : f ≠ 0) :
    ∃ N : ℕ, ∀ (p : PrimeIndex), N ≤ p.val → ∀ g : Guard p, 0 < g.birth →
      ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) g.value.val‖ = 1 := by
  obtain ⟨d,F,hd,hF,hm⟩ := exists_integer_multiple f hf
  obtain ⟨N,hN⟩ := uniform_integer F hF
  obtain ⟨K,hK⟩ := uniform_integer (C d) (by simpa using hd)
  refine ⟨max N K, fun p hp g hb => ?_⟩
  have hV := hN p ((le_max_left _ _).trans hp) g hb
  have hd' := hK p ((le_max_right _ _).trans hp) g hb
  simp only [eval₂_C] at hd'
  change ‖(d : ℚ_[p.val])‖ = 1 at hd'
  have he := congrArg (Polynomial.eval₂ (algebraMap ℚ ℚ_[p.val]) g.value.val) hm
  have hc : (algebraMap ℚ ℚ_[p.val]).comp (algebraMap ℤ ℚ) = Int.castRingHom ℚ_[p.val] :=
    Subsingleton.elim _ _
  rw [eval₂_map, eval₂_mul, eval₂_C, hc] at he
  simp only [map_intCast] at he
  have hn := congrArg norm he
  rw [norm_mul, hd', one_mul, hV] at hn
  exact hn.symm

/-- A cutoff, calculated before the guard or future prime has been chosen.
Zero polynomials are ignored so this function takes an arbitrary finite list. -/
def cutoff (frozen : Finset ℚ[X]) : ℕ :=
  frozen.sup fun f => if h : f = 0 then 0 else (uniform_polynomial f h).choose

theorem uniform_units (frozen : Finset ℚ[X]) (p : PrimeIndex) (hp : cutoff frozen ≤ p.val)
    (g : Guard p) (hb : 0 < g.birth) (f : ℚ[X]) (hf : f ∈ frozen) (hne : f ≠ 0) :
    ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) g.value.val‖ = 1 := by
  apply (uniform_polynomial f hne).choose_spec p _ g hb
  apply le_trans _ hp
  have h := Finset.le_sup (f := fun f : ℚ[X] => if h : f = 0 then 0 else (uniform_polynomial f h).choose) hf
  unfold cutoff
  exact (show (if h : f = 0 then 0 else (uniform_polynomial f h).choose) = _ from by simp [hne]).symm.le.trans h

/-- A two-centre batch also covering the uniform guard cutoff. It preserves
the precise requested-prime field used by the adaptive recursion. -/
def base {n : ℕ} (frozen : Finset ℚ[X]) (P : Prefix n) (start : n = 0 → P.state = zeroState)
    (degree : ℕ) (needed : Finset PrimeIndex) :
    {B : Batch // StageRecursion.BatchProgress P degree needed B} := by
  let B := UnivariateGuards.base P start (max degree (cutoff frozen)) needed
  refine ⟨B.val, ⟨B.property.stage, B.property.processed, B.property.old_guard,
    B.property.new_guard, B.property.cutoff_gt, ?_⟩⟩
  apply le_trans _ B.property.degree_budget
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (le_max_left _ _) _)

theorem base_covers {n : ℕ} (frozen : Finset ℚ[X]) (P : Prefix n) (start : n = 0 → P.state = zeroState)
    (degree : ℕ) (needed : Finset PrimeIndex) : cutoff frozen ≤ (base frozen P start degree needed).val.cutoff := by
  let d := max degree (cutoff frozen)
  have b := (UnivariateGuards.base P start d needed).property.degree_budget
  have h : cutoff frozen ≤ 4 + (∑ j, (P.raw j).natDegree) + d := (le_max_right _ _).trans (Nat.le_add_left _ _)
  exact (h.trans Nat.lt_two_pow_self.le).trans b

theorem base_good {n : ℕ} (frozen : Finset ℚ[X]) (P : Prefix n) (start : n = 0 → P.state = zeroState)
    (degree : ℕ) (needed : Finset PrimeIndex) (p : PrimeIndex)
    (hp : p ∈ (base frozen P start degree needed).val.assigned.primes)
    (hf : p ∉ P.state.assignment.primes) :
    UnivariateGuards.Good ((base frozen P start degree needed).val.assigned.guard p hp) :=
  UnivariateGuards.base_good P start _ needed p hp hf

/-- After the freezing batch, all later actual guards give units on the
frozen polynomials. This also applies to all future auxiliary calibrations. -/
theorem after_freezing (R : Requirements) (n : ℕ) (frozen : Finset ℚ[X])
    (covered : cutoff frozen ≤ (selection R n).batch.cutoff) (p : PrimeIndex)
    (later : n < (chain R).guardChain.birth p) (f : ℚ[X]) (hf : f ∈ frozen) (hne : f ≠ 0) :
    ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) (permanentSite R p).guard.val‖ = 1 := by
  let C := (chain R).guardChain
  have outside : p ∉ (selection R n).batch.assigned.primes := C.not_mem_before_birth p later
  have large : (selection R n).batch.cutoff < p.val := by
    by_contra! h
    exact outside ((selection R n).batch.processed_subset_assigned
      ((selection R n).batch.covered ((GuardStages.mem_primesThrough _ _).mpr h)))
  rw [permanent_guard_eq]
  apply uniform_units frozen p (covered.trans large.le) (C.guard p) _ f hf hne
  rw [C.guard_birth]
  exact (Nat.zero_le n).trans_lt later

/-- The norm support at the actual guard branch is finite without any
assumption about the chosen targets or requested primary sites. -/
theorem finite_guard_support (R : Requirements) (x : RatFunc ℚ) (hx : x ≠ 0) :
    {p : PrimeIndex | ‖(permanentSite R p).evaluate true (Or.inl rfl) x‖ ≠ 1}.Finite := by
  apply (UnivariateExtraction.guard_support R x hx).subset
  intro p hne he
  apply hne
  change ‖LocalEvaluation.evalAt (permanentSite R p).guard.val (permanentSite R p).guard_trans x‖ = 1
  rw [UnivariateExtraction.eval_permanent_guard]
  exact ConstructionReturns.norm_eq_one_of_mulValuation_eq_one _ he

end UnconditionalCounterexample.Variations.FrozenGuards
