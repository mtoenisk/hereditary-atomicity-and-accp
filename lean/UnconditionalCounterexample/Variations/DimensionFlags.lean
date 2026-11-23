import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.Ideal

/-!
# Coordinate flags for prescribed dimension

The full coordinate flag ends at the retained rational point. It
lifts to the generic localization and contracts strictly to the constructed ring.
The extra prime over the reserved integer adds a further strict step. The
truncated flag gives the lower bound in the examples of smaller dimension.
-/

namespace UnconditionalCounterexample.Variations

noncomputable section

open MvPolynomial

variable {k : Type*} [CommRing k] {r : ℕ}

/-- Specialize precisely the coordinates with index less than `j` at the point `c`. -/
def specializeCoordinates (c : Fin r → k) (j : ℕ) :
    MvPolynomial (Fin r) k →+* MvPolynomial (Fin r) k :=
  eval₂Hom C (fun i ↦ if (i : ℕ) < j then C (c i) else X i)

private theorem specializeCoordinates_comp (c : Fin r → k) {j n : ℕ} (hjn : j ≤ n) :
    (specializeCoordinates c n).comp (specializeCoordinates c j) = specializeCoordinates c n := by
  ext a
  · simp [specializeCoordinates]
  · by_cases h : (a : ℕ) < j
    · simp [specializeCoordinates, h, h.trans_le hjn]
    · simp [specializeCoordinates, h]

variable [IsDomain k]

/-- The prime of the coordinate subspace through `c` fixing its first `j` coordinates. -/
def coordinatePrime (c : Fin r → k) (j : ℕ) : PrimeSpectrum (MvPolynomial (Fin r) k) :=
  ⟨RingHom.ker (specializeCoordinates c j), RingHom.ker_isPrime _⟩

theorem coordinatePrime_lt_succ (c : Fin r → k) (j : Fin r) :
    coordinatePrime c j < coordinatePrime c (j + 1 : ℕ) := by
  apply (PrimeSpectrum.asIdeal_lt_asIdeal ..).1
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · intro f hf
    change specializeCoordinates c (j + 1 : ℕ) f = 0
    change specializeCoordinates c (j : ℕ) f = 0 at hf
    have heq := DFunLike.congr_fun (specializeCoordinates_comp c (Nat.le_succ (j : ℕ))) f
    rw [← heq, RingHom.comp_apply, hf, map_zero]
  · intro h
    let f : MvPolynomial (Fin r) k := X j - C (c j)
    have hx : f ∈ (coordinatePrime c (j + 1 : ℕ)).asIdeal := by
      change specializeCoordinates c (j + 1 : ℕ) f = 0
      simp [specializeCoordinates, f]
    have hy := h hx
    change specializeCoordinates c (j : ℕ) f = 0 at hy
    simp [specializeCoordinates, f] at hy
    have hval := congrArg (eval (fun _ : Fin r ↦ c j + 1)) hy
    simp at hval

/-- The first `d` coordinate primes give a strict flag of length `d`, including `d = r`. -/
def coordinateFlag (c : Fin r → k) (d : ℕ) (hd : d ≤ r) :
    LTSeries (PrimeSpectrum (MvPolynomial (Fin r) k)) where
  length := d
  toFun i := coordinatePrime c i
  step i := coordinatePrime_lt_succ c ⟨i, i.isLt.trans_le hd⟩

theorem coordinatePrime_full (c : Fin r → k) :
    (coordinatePrime c r).asIdeal = RingHom.ker (eval c) := by
  have heq : specializeCoordinates c r = C.comp (eval c) := by
    ext a <;> simp [specializeCoordinates]
  ext f
  change specializeCoordinates c r f = 0 ↔ eval c f = 0
  simp [heq]

section Localization

variable {D : Type*} [CommRing D] (B : Type*) [CommRing B] [Algebra D B]
variable (M : Submonoid D) [IsLocalization M B]

/-- A flag survives localization as soon as the multiplicative set misses its last prime. -/
def liftPrimeFlag (p : LTSeries (PrimeSpectrum D)) (htop : Disjoint (M : Set D) p.last.asIdeal) :
    LTSeries (PrimeSpectrum B) :=
  let e := IsLocalization.primeSpectrumOrderIso M B
  let point (i : Fin (p.length + 1)) : {q : PrimeSpectrum D // Disjoint (M : Set D) q.asIdeal} :=
    ⟨p i, htop.mono_right (p.monotone (Fin.le_last i) : p i ≤ p.last)⟩
  LTSeries.mk p.length (fun i ↦ e.symm (point i)) (fun _ _ hij ↦ e.symm.strictMono (p.strictMono hij))

/-- Each member of the lifted chain contracts to the specified member of the original chain. -/
theorem liftPrimeFlag_comap (p : LTSeries (PrimeSpectrum D))
    (htop : Disjoint (M : Set D) p.last.asIdeal) (i : Fin (p.length + 1)) :
    PrimeSpectrum.comap (algebraMap D B) ((liftPrimeFlag B M p htop) i) = p i :=
  congrArg Subtype.val ((IsLocalization.primeSpectrumOrderIso M B).apply_symm_apply _)

/-- A strict chain in a localization contracts strictly in the original ring. -/
def contractPrimeFlag (p : LTSeries (PrimeSpectrum B)) : LTSeries (PrimeSpectrum D) :=
  p.map (PrimeSpectrum.comap (algebraMap D B)) (fun _ _ h ↦
    (IsLocalization.orderEmbedding M B).strictMono h)

/-- A prime above the contracted top that contains an inverted element extends the flag
by one strict step. In the prescribed-dimension construction the witness is the reserved prime. -/
theorem succ_length_le_of_vertical_prime (p : LTSeries (PrimeSpectrum B)) (q : PrimeSpectrum D)
    (hle : (PrimeSpectrum.comap (algebraMap D B) p.last) ≤ q)
    (hmeet : ∃ m : M, (m : D) ∈ q.asIdeal) :
    ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim D := by
  obtain ⟨m, hm⟩ := hmeet
  have hlt : (contractPrimeFlag B M p).last < q := by
    refine lt_iff_le_not_ge.mpr ⟨hle, fun h ↦ ?_⟩
    have hp : algebraMap D B m ∈ p.last.asIdeal := h hm
    exact p.last.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp (IsLocalization.map_units B m))
  exact Order.LTSeries.length_le_krullDim ((contractPrimeFlag B M p).snoc q hlt)

/-- Separate chains in the generic localization from chains ending in a vertical prime. -/
theorem ringKrullDim_le_of_vertical_heights (d : ℕ) (hB : ringKrullDim B ≤ d)
    (hv : ∀ q : PrimeSpectrum D, ¬ Disjoint (M : Set D) q.asIdeal → Order.height q ≤ d) :
    ringKrullDim D ≤ d := by
  change (⨆ p : LTSeries (PrimeSpectrum D), (p.length : WithBot ℕ∞)) ≤ d
  refine iSup_le fun p ↦ ?_
  by_cases hd : Disjoint (M : Set D) p.last.asIdeal
  · exact (Order.LTSeries.length_le_krullDim (liftPrimeFlag B M p hd)).trans hB
  · exact_mod_cast (Order.length_le_height_last (p := p)).trans (hv _ hd)

end Localization

/-- Localizing the polynomial ring at denominators nonvanishing at a rational point
preserves its full dimension. -/
theorem ringKrullDim_localization_at_retained_point {F : Type*} [Field F] {n : ℕ}
    (c : Fin n → F) (M : Submonoid (MvPolynomial (Fin n) F)) (B : Type*) [CommRing B]
    [Algebra (MvPolynomial (Fin n) F) B] [IsLocalization M B]
    (hM : ∀ f : M, eval c f ≠ 0) : ringKrullDim B = n := by
  let p := coordinateFlag c n le_rfl
  have htop : Disjoint (M : Set (MvPolynomial (Fin n) F)) p.last.asIdeal := by
    change Disjoint _ ((coordinatePrime c n).asIdeal : Set (MvPolynomial (Fin n) F))
    rw [coordinatePrime_full]
    exact Set.disjoint_left.mpr fun f hf hzero ↦ hM ⟨f, hf⟩ hzero
  apply le_antisymm
  · change (⨆ q : LTSeries (PrimeSpectrum B), (q.length : WithBot ℕ∞)) ≤ n
    refine iSup_le fun q ↦ ?_
    have h := Order.LTSeries.length_le_krullDim (contractPrimeFlag B M q)
    change (q.length : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F) at h
    simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field] using h
  · exact Order.LTSeries.length_le_krullDim (liftPrimeFlag B M p htop)


end

end UnconditionalCounterexample.Variations
