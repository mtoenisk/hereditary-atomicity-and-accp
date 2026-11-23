import UnconditionalCounterexample.Variations.UnivariateBirths
import UnconditionalCounterexample.Variations.UnivariateCentres

/-!
# Permanent finite reservations for the dyadic construction

Finite disjoint lists of requested sites may be assigned in one raw stage.
At a new regular site, every previously frozen noncentral monic polynomial
can simultaneously be a unit on both arguments. The coordinate centred there
has its prescribed displacement order.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.Univariate

open Polynomial GuardSupport CombinedGuardStep RecursivePrefix PaperGuardStages

namespace Births
variable {n : ℕ} {P : Prefix n} (a b : Births P)

private def chooseData (p : PrimeIndex) (hp : p ∈ a.primes ∪ b.primes) :
    Σ g : Guard p, Option (Primary p g.value) := by
  classical
  exact if h : p ∈ a.primes then ⟨a.guard p h, a.primary p h⟩
    else
      let h' := (Finset.mem_union.mp hp).resolve_left h
      ⟨b.guard p h', b.primary p h'⟩

private def siteOfData {p : PrimeIndex} (d : Σ g : Guard p, Option (Primary p g.value)) : Site p :=
  ⟨d.1.value, d.1.transcendental, d.2⟩

/-- Glue finite lists of distinct prescribed fibres. -/
def union (_h : Disjoint a.primes b.primes) : Births P := by
  classical
  let data := a.chooseData b
  refine { primes := a.primes ∪ b.primes
           fresh := fun p hp => (Finset.mem_union.mp hp).elim (a.fresh p) (b.fresh p)
           guard := fun p hp => (data p hp).1
           primary := fun p hp => (data p hp).2
           birth_eq := ?_
           old_units := ?_ }
  · intro p hp
    by_cases h : p ∈ a.primes
    · simpa only [data, chooseData, h, ↓reduceDIte] using a.birth_eq p h
    · simpa only [data, chooseData, h, ↓reduceDIte] using b.birth_eq p ((Finset.mem_union.mp hp).resolve_left h)
  · intro p hp j
    by_cases h : p ∈ a.primes
    · simpa only [data, chooseData, h, ↓reduceDIte] using a.old_units p h j
    · simpa only [data, chooseData, h, ↓reduceDIte] using b.old_units p ((Finset.mem_union.mp hp).resolve_left h) j

theorem union_site_left (hd : Disjoint a.primes b.primes) (p : PrimeIndex) (h : p ∈ a.primes) :
    (a.union b hd).site p (Finset.mem_union_left _ h) = a.site p h := by
  classical
  apply congrArg siteOfData (a₁ := a.chooseData b p (Finset.mem_union_left _ h))
    (a₂ := ⟨a.guard p h, a.primary p h⟩)
  exact dite_eq_left h

theorem union_site_right (hd : Disjoint a.primes b.primes) (p : PrimeIndex) (h : p ∈ b.primes) :
    (a.union b hd).site p (Finset.mem_union_right _ h) = b.site p h := by
  classical
  have ha : p ∉ a.primes := fun hm => Finset.disjoint_left.mp hd hm h
  apply congrArg siteOfData (a₁ := a.chooseData b p (Finset.mem_union_right _ h))
    (a₂ := ⟨b.guard p h, b.primary p h⟩)
  exact dite_eq_right ha

end Births

/-- The degree floor at one stage permanently reserves a finite list of
polynomials which did not occur in the prefix. -/
theorem retains_finite_list (R : Requirements) (n : ℕ) (frozen : Finset ℚ[X])
    (hprefix : ∀ f ∈ frozen, ∀ j : Fin n, ((chain R).approx n).raw j ≠ f)
    (hfloor : frozen.sup Polynomial.natDegree ≤ R.degreeFloor ((chain R).approx n) (table R n)) :
    ∀ f ∈ frozen, f ∉ Set.range (chain R).raw := fun f hf =>
  retained_after_freezing R n f (hprefix f hf) ((Finset.le_sup hf).trans hfloor)

/-- One fresh regular site simultaneously screens every earlier raw and every
member of a finite list of frozen monic rational polynomials away from the
chosen endpoint. Their coefficients may have arbitrary denominators. -/
theorem exists_regular_site_avoiding {n : ℕ} (P : Prefix n) (frozen : Finset ℚ[X])
    (hmonic : ∀ f ∈ frozen, f.Monic) (c : ℕ) (hc : c = 0 ∨ c = 1)
    (haway : ∀ f ∈ frozen, f.eval (c : ℚ) ≠ 0) (avoid : Finset PrimeIndex) (cutoff : ℕ) :
    ∃ (p : PrimeIndex) (g : Guard p) (α : Primary p g.value),
      p ∉ P.state.assignment.primes ∧ p ∉ avoid ∧ cutoff < p.val ∧ 2 < p.val ∧
      g.birth = n ∧ PadicInt.toZMod g.value ≠ 1 ∧
      PadicInt.toZMod α.val = c ∧ (α.val.val - c).valuation = 1 ∧
      (∀ j : Fin n, ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[p.val]) α.val.val‖ = 1 ∧
        ‖(P.raw j).eval₂ (algebraMap ℚ ℚ_[p.val]) g.value.val‖ = 1) ∧
      ∀ f ∈ frozen, ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) α.val.val‖ = 1 ∧
        ‖f.eval₂ (algebraMap ℚ ℚ_[p.val]) g.value.val‖ = 1 := by
  classical
  let J := Fin n ⊕ ↥frozen
  let Q : J → ℚ[X] := Sum.elim P.raw Subtype.val
  have hm : ∀ j, (Q j).Monic
    | .inl j => P.monic j
    | .inr f => hmonic f.val f.property
  have hv : ∀ j, (Q j).eval (c : ℚ) ≠ 0
    | .inl j => (P.irreducible j).not_isRoot_of_natDegree_ne_one (by have := P.degree_five j; omega)
    | .inr f => haway f.val f.property
  let bound := (Finset.univ : Finset J).sup fun j => (Q j).support.sup fun i => ((Q j).coeff i).den
  let excluded := P.state.assignment.primes ∪ GuardStages.primesThrough bound
  obtain ⟨A, hA, _⟩ := PaperGuardStages.exists_initial_assignment excluded
  have hs (j : J) (i : ℕ) (p : PrimeIndex) (hd : p.val ∣ ((Q j).coeff i).den) : p ∈ A.primes := by
    have hi : i ∈ (Q j).support := by
      by_contra h
      have hz := Polynomial.notMem_support_iff.mp h
      rw [hz, Rat.den_zero] at hd
      exact p.property.not_dvd_one hd
    rw [hA]
    apply Finset.mem_union_right
    exact (GuardStages.mem_primesThrough p bound).mpr (((Nat.le_of_dvd (Rat.den_pos _) hd).trans
      (Finset.le_sup (f := fun i => ((Q j).coeff i).den) hi)).trans
        (Finset.le_sup (f := fun j : J => (Q j).support.sup fun i => ((Q j).coeff i).den)
          (Finset.mem_univ j)))
  obtain ⟨p, hb, h2, hA', havoid, α, g, ht, hr, horder, hbirth, hguard, hdiff, hold⟩ :=
    UnivariateCentres.exists_fresh_pair A avoid Q hm hs c 1 n cutoff hc (by decide) hv
  have hneq : PadicInt.toZMod α ≠ PadicInt.toZMod g.value := by
    have hh := (padicInt_isUnit_iff_toZMod_ne_zero _).mp hdiff
    rw [map_sub, sub_ne_zero] at hh
    exact hh.symm
  refine ⟨p, g, ⟨α, ht, hneq⟩, ?_, havoid, hb, h2, hbirth, hguard, hr, ?_,
    fun j => hold (.inl j), fun f hf => hold (.inr ⟨f,hf⟩)⟩
  · rw [hA] at hA'
    exact fun hp => hA' (Finset.mem_union_left _ hp)
  · simpa using horder

end UnconditionalCounterexample.Variations.Univariate
