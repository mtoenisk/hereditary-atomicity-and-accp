import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.RankOne

/-!
# Krull dimension and rank-one valuations

A valuation subring of dimension at most one has an archimedean value group.
If it is proper, its canonical valuation therefore has rank one in mathlib's
sense, including an order embedding of its value group into the nonnegative
reals. No discreteness or Noetherian hypothesis is imposed.
-/

namespace HereditaryAtomicity

private theorem exists_pow_dvd_of_krullDimLE_one
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] (a b : R) (ha : ¬ IsUnit a) (hb : b ≠ 0) :
    ∃ n : ℕ, b ∣ a ^ n := by
  have hrad : IsLocalRing.maximalIdeal R ≤ (Ideal.span ({b} : Set R)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP ↦ ?_
    have hPb : b ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hP.1
    have hPbot : P ≠ ⊥ := by
      intro heq
      exact hb (by simpa [heq] using hPb)
    have hmax := hP.2.isMaximal_of_ne_bot hPbot
    exact le_of_eq (IsLocalRing.eq_maximalIdeal hmax).symm
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hrad ha)
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

variable {K : Type*} [Field K]

/-- In a valuation subring of dimension at most one, any two positive values
are comparable by a natural power. -/
theorem valuationSubring_valueGroup_mulArchimedean (V : ValuationSubring K)
    [Ring.KrullDimLE 1 V] : MulArchimedean V.ValueGroup := by
  constructor
  intro x y hy
  by_cases hx : x ≤ 1
  · exact ⟨0, by simpa using hx⟩
  have hx' : 1 < x := lt_of_not_ge hx
  obtain ⟨a, ha⟩ := V.valuation_surjective y⁻¹
  obtain ⟨b, hb⟩ := V.valuation_surjective x⁻¹
  have hav : V.valuation a < 1 := by rw [ha]; exact inv_lt_one₀ (lt_trans zero_lt_one hy) |>.mpr hy
  have hbv : V.valuation b < 1 := by rw [hb]; exact inv_lt_one₀ (lt_trans zero_lt_one hx') |>.mpr hx'
  let aV : V := ⟨a, V.mem_of_valuation_le_one a hav.le⟩
  let bV : V := ⟨b, V.mem_of_valuation_le_one b hbv.le⟩
  have haV : ¬ IsUnit aV := by
    intro hu
    exact hav.ne ((V.valuation_eq_one_iff aV).mp hu)
  have hbV : bV ≠ 0 := by
    intro hzero
    have hbzero : b = 0 := congrArg Subtype.val hzero
    have : x⁻¹ = 0 := by simpa [hbzero] using hb.symm
    exact (ne_of_gt (lt_trans zero_lt_one hx')) (inv_eq_zero.mp this)
  obtain ⟨n, c, hc⟩ := exists_pow_dvd_of_krullDimLE_one aV bV haV hbV
  refine ⟨n, ?_⟩
  have hval : V.valuation (a ^ n) ≤ V.valuation b := by
    apply (V.valuation_le_iff _ _).mpr
    refine ⟨c, ?_⟩
    have heq : a ^ n = b * (c : K) := congrArg Subtype.val hc
    simpa [mul_comm] using heq.symm
  rw [map_pow, ha, hb, inv_pow] at hval
  exact (inv_le_inv₀ (pow_pos (lt_trans zero_lt_one hy) n) (lt_trans zero_lt_one hx')).mp hval

/-- A proper valuation subring of dimension at most one has a rank-one
canonical valuation. The result supplies the real-valued rank-one structure,
rather than assuming it from the Krull-dimension assertion. -/
theorem valuationSubring_nonempty_rankOne (V : ValuationSubring K)
    [Ring.KrullDimLE 1 V] (hV : V ≠ ⊤) : Nonempty V.valuation.RankOne := by
  let : V.valuation.IsNontrivial := by
    by_contra hn
    exact hV (V.eq_top_iff.mpr hn)
  let : MulArchimedean V.ValueGroup := valuationSubring_valueGroup_mulArchimedean V
  apply Valuation.nonempty_rankOne_iff_mulArchimedean.mpr
  exact MulArchimedean.comap
    MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono

end HereditaryAtomicity
