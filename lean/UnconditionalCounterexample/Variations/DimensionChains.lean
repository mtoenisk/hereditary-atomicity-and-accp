import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.FiniteType

/-!
# Prime chains and finitely generated subalgebras

To bound the dimension of a subring of a rational function field, pass
to a finite type ℤ-algebra inside it. For each strict step choose an element of
the larger prime outside the smaller one. Adjoining just these elements preserves
every step upon contraction. The same proof works over any base ring.
-/

namespace UnconditionalCounterexample.Variations

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite prime chain contracts strictly to a single finitely generated subalgebra. -/
theorem exists_fg_subalgebra_preserving_prime_chain (p : LTSeries (PrimeSpectrum A)) :
    ∃ B : Subalgebra R A, B.FG ∧
      StrictMono (fun i ↦ PrimeSpectrum.comap B.val.toRingHom (p i)) := by
  classical
  have hex (i : Fin p.length) : ∃ x : A,
      x ∈ (p i.succ).asIdeal ∧ x ∉ (p i.castSucc).asIdeal := by
    exact Set.not_subset.mp (not_le_of_gt ((PrimeSpectrum.asIdeal_lt_asIdeal ..).2 (p.step i)))
  choose x hmem hnot using hex
  let B := Algebra.adjoin R (Set.range x)
  refine ⟨B, Subalgebra.fg_def.2 ⟨_, Set.finite_range x, rfl⟩, ?_⟩
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  apply (PrimeSpectrum.asIdeal_lt_asIdeal ..).1
  refine lt_iff_le_not_ge.mpr ⟨(Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal ..).2
    (le_of_lt (p.step i)))), ?_⟩
  intro h
  let w : B := ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  exact hnot i (h (show w ∈ (PrimeSpectrum.comap B.val.toRingHom (p i.succ)).asIdeal from hmem i))

/-- A uniform bound on the dimensions of finitely generated subalgebras bounds the whole ring. -/
theorem ringKrullDim_le_of_fg_subalgebras (d : WithBot ℕ∞)
    (h : ∀ B : Subalgebra R A, B.FG → ringKrullDim B ≤ d) :
    ringKrullDim A ≤ d := by
  change (⨆ p : LTSeries (PrimeSpectrum A), (p.length : WithBot ℕ∞)) ≤ d
  refine iSup_le fun p ↦ ?_
  obtain ⟨B, hB, hm⟩ := exists_fg_subalgebra_preserving_prime_chain (R := R) p
  let q : LTSeries (PrimeSpectrum B) :=
    ⟨p.length, fun i ↦ PrimeSpectrum.comap B.val.toRingHom (p i),
      fun _ ↦ hm Fin.castSucc_lt_succ⟩
  exact (Order.LTSeries.length_le_krullDim q).trans (h B hB)

end UnconditionalCounterexample.Variations
