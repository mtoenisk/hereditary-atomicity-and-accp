import HereditaryAtomicity.PrueferBezout
import HereditaryAtomicity.SparseCutConductor
import Mathlib.RingTheory.Spectrum.Maximal.Topology
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Continuous normalized profiles on actual normalization branches

The topology is the Zariski topology on the actual maximal spectrum. Nonzero
Jacobson radical makes it a zero-dimensional quotient spectrum, with no finite
branch hypothesis. The profile is the order of the actual normalized valuation.
-/

noncomputable section
open Set TopologicalSpace
open scoped NNReal
namespace HereditaryAtomicity

private theorem maximalSpectrum_isEmbedding {A : Type*} [CommRing A] :
    Topology.IsEmbedding (@MaximalSpectrum.toPrimeSpectrum A _) :=
  MaximalSpectrum.toPrimeSpectrum_injective.isEmbedding_induced

/-- The maximal spectrum is the spectrum of any nonzero ideal contained in the
Jacobson radical, for a domain of dimension at most one. -/
def maximalSpectrumQuotientHomeomorph
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (J : Ideal A) (hJ0 : J ≠ ⊥) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal A)) :
    MaximalSpectrum A ≃ₜ PrimeSpectrum (A ⧸ J) := by
  let q := Ideal.Quotient.mk J
  have hJP (P : MaximalSpectrum A) : J ≤ P.asIdeal :=
    hJ.trans (sInf_le ⟨bot_le, P.isMaximal⟩)
  let f : MaximalSpectrum A → PrimeSpectrum (A ⧸ J) := fun P =>
    ⟨P.asIdeal.map q, Ideal.isPrime_map_quotientMk_of_isPrime (hJP P)⟩
  have hmax (Q : PrimeSpectrum (A ⧸ J)) : (Q.asIdeal.comap q).IsMaximal := by
    apply (Ideal.comap_isPrime q Q.asIdeal).isMaximal_of_ne_bot
    intro heq
    apply hJ0
    apply le_antisymm _ bot_le
    have hle := Ideal.ker_le_comap (K := Q.asIdeal) q
    simpa [q, heq] using hle
  let g : PrimeSpectrum (A ⧸ J) → MaximalSpectrum A := fun Q =>
    ⟨Q.asIdeal.comap q, hmax Q⟩
  have hgf : ∀ P, g (f P) = P := by
    intro P
    apply MaximalSpectrum.ext
    exact Ideal.comap_map_mk (hJP P)
  have hfg : ∀ Q, f (g Q) = Q := by
    intro Q
    apply PrimeSpectrum.ext
    exact Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective Q.asIdeal
  refine ⟨⟨f, g, hgf, hfg⟩, ?_, ?_⟩
  · apply (PrimeSpectrum.isEmbedding_comap_of_surjective (A ⧸ J) q
      Ideal.Quotient.mk_surjective).continuous_iff.mpr
    have heq : PrimeSpectrum.comap q ∘ f = MaximalSpectrum.toPrimeSpectrum := by
      funext P
      apply PrimeSpectrum.ext
      exact Ideal.comap_map_mk (hJP P)
    rw [heq]
    exact MaximalSpectrum.toPrimeSpectrum_continuous
  · apply maximalSpectrum_isEmbedding.continuous_iff.mpr
    exact PrimeSpectrum.continuous_comap q

/-- Compactness of the actual maximal spectrum; no finite maximal spectrum is assumed. -/
theorem compactSpace_maximalSpectrum_of_nonzero_jacobson
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (hJ : Ideal.jacobson (⊥ : Ideal A) ≠ ⊥) : CompactSpace (MaximalSpectrum A) :=
  (maximalSpectrumQuotientHomeomorph _ hJ le_rfl).symm.compactSpace

/-- The same maximal spectrum is Hausdorff and totally separated. -/
theorem totallySeparated_maximalSpectrum_of_nonzero_jacobson
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (hJ : Ideal.jacobson (⊥ : Ideal A) ≠ ⊥) :
    TotallySeparatedSpace (MaximalSpectrum A) := by
  let J := Ideal.jacobson (⊥ : Ideal A)
  let : Ring.KrullDimLE 0 (A ⧸ J) := dimension_zero_quotient_of_nonzero_ideal J hJ
  let : TotallySeparatedSpace (PrimeSpectrum (A ⧸ J)) :=
    totallySeparated_primeSpectrum_of_dimension_zero
  let e := maximalSpectrumQuotientHomeomorph J hJ le_rfl
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro P Q hPQ
  obtain ⟨U, hU, hP, hQ⟩ := totallySeparatedSpace_iff_exists_isClopen.mp
    (inferInstance : TotallySeparatedSpace (PrimeSpectrum (A ⧸ J)))
    (e.injective.ne hPQ)
  exact ⟨e ⁻¹' U, hU.preimage e.continuous, hP, hQ⟩

/-- Every basic open of this maximal spectrum is clopen. -/
theorem isClopen_maximal_basicOpen_of_nonzero_jacobson
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (hJ : Ideal.jacobson (⊥ : Ideal A) ≠ ⊥) (a : A) :
    IsClopen {P : MaximalSpectrum A | a ∉ P.asIdeal} := by
  let J := Ideal.jacobson (⊥ : Ideal A)
  let : Ring.KrullDimLE 0 (A ⧸ J) := dimension_zero_quotient_of_nonzero_ideal J hJ
  let e := maximalSpectrumQuotientHomeomorph J hJ le_rfl
  have heq : {P : MaximalSpectrum A | a ∉ P.asIdeal} =
      e ⁻¹' (PrimeSpectrum.basicOpen (Ideal.Quotient.mk J a) : Set _) := by
    ext P
    change a ∉ P.asIdeal ↔ Ideal.Quotient.mk J a ∉ P.asIdeal.map (Ideal.Quotient.mk J)
    rw [← Ideal.mem_comap, Ideal.comap_map_mk
      (show J ≤ P.asIdeal from sInf_le ⟨bot_le, P.isMaximal⟩)]
  rw [heq]
  exact (isClopen_basicOpen_of_dimension_zero _).preimage e.continuous

/-- The actual maximal spectrum is Hausdorff when the Jacobson radical is nonzero. -/
theorem t2Space_maximalSpectrum_of_nonzero_jacobson
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (hJ : Ideal.jacobson (⊥ : Ideal A) ≠ ⊥) : T2Space (MaximalSpectrum A) := by
  let : TotallySeparatedSpace (MaximalSpectrum A) :=
    totallySeparated_maximalSpectrum_of_nonzero_jacobson hJ
  infer_instance

/-- The vanishing locus of any finitely generated ideal is clopen on the actual
maximal spectrum, including when there are infinitely many maximal ideals. -/
theorem isClopen_maximal_zeroLocus_of_fg
    {A : Type*} [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (hJ : Ideal.jacobson (⊥ : Ideal A) ≠ ⊥)
    (I : Ideal A) (hI : I.FG) : IsClopen {P : MaximalSpectrum A | I ≤ P.asIdeal} := by
  obtain ⟨s, hs⟩ := hI
  have heq : {P : MaximalSpectrum A | I ≤ P.asIdeal} =
      ⋂ a ∈ s, {P : MaximalSpectrum A | a ∈ P.asIdeal} := by
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [← hs, Ideal.span_le]
    rfl
  rw [heq]
  apply isClopen_biInter_finset
  intro a _
  convert (isClopen_maximal_basicOpen_of_nonzero_jacobson hJ a).compl using 1
  ext P
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]

variable {K : Type*} [Field K]

/-- A fraction over a Bézout subring has a coprime numerator and denominator. -/
theorem exists_coprime_fraction (B : Subring K) [IsFractionRing B K] [IsBezout B]
    (x : K) : ∃ a b : B, b ≠ 0 ∧ IsCoprime a b ∧ (a : K) / (b : K) = x := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective B x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  let d := IsBezout.gcd a b
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hb0 (IsBezout.gcd_dvd_right a b)
  obtain ⟨a', ha⟩ := IsBezout.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := IsBezout.gcd_dvd_right a b
  obtain ⟨u, v, huv⟩ := IsBezout.gcd_eq_sum a b
  change a = d * a' at ha
  change b = d * b' at hb'
  change u * a + v * b = d at huv
  have hb'0 : b' ≠ 0 := by intro h; simp [h] at hb'; exact hb0 hb'
  have hcop : IsCoprime a' b' := by
    refine ⟨u, v, ?_⟩
    apply mul_left_cancel₀ hd0
    change d * (u * a' + v * b') = d * 1
    calc
      _ = u * a + v * b := by rw [ha, hb']; ring
      _ = _ := by simpa [d] using huv
  refine ⟨a', b', hb'0, hcop, ?_⟩
  have hdK : (d : K) ≠ 0 := Subtype.coe_ne_coe.mpr hd0
  change (a : K) / (b : K) = x at hab
  rw [ha, hb'] at hab
  simpa only [Subring.coe_mul, mul_div_mul_left _ _ hdK] using hab

/-- A coprime denominator tests membership in each actual maximal branch. -/
theorem coprime_fraction_mem_prueferMaximalValuation_iff
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    {a b : B} (hcop : IsCoprime a b) (hb : b ≠ 0) (P : MaximalSpectrum B) :
    (a : K) / (b : K) ∈ prueferMaximalValuation B hB P ↔ b ∉ P.asIdeal := by
  let v := prueferMaximalRealValuation B hB hfield P
  have hvB (z : B) : v z ≤ 1 :=
    (mem_pruefer_iff_realValuations_le_one B hB hfield z).mp z.property P
  have hmem : (a : K) / (b : K) ∈ prueferMaximalValuation B hB P ↔
      v ((a : K) / (b : K)) ≤ 1 := by
    rw [← prueferMaximalRealValuation_valuationSubring B hB hfield P]
    rfl
  rw [hmem]
  constructor
  · intro hx hbP
    have hbv : v (b : K) < 1 :=
      (prueferMaximalRealValuation_lt_one_iff B hB hfield P b).mpr hbP
    have haeq : (a : K) = ((a : K) / (b : K)) * (b : K) :=
      (div_mul_cancel₀ _ (Subtype.coe_ne_coe.mpr hb)).symm
    have hav : v (a : K) < 1 := by
      rw [haeq, map_mul]
      exact (mul_le_mul_of_nonneg_right hx zero_le).trans_lt (by simpa using hbv)
    have haP := (prueferMaximalRealValuation_lt_one_iff B hB hfield P a).mp hav
    obtain ⟨u, w, huw⟩ := hcop
    exact P.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _
      (huw ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left u haP)
        (P.asIdeal.mul_mem_left w hbP)) isUnit_one)
  · intro hbP
    have hbv : v (b : K) = 1 := le_antisymm (hvB b)
      (not_lt.mp (fun h => hbP ((prueferMaximalRealValuation_lt_one_iff B hB hfield P b).mp h)))
    simpa only [map_div₀, hbv, div_one] using hvB a

/-- Membership of a fraction in the actual valuation branch is clopen. -/
theorem isClopen_mem_prueferMaximalValuation
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (hJ : Ideal.jacobson (⊥ : Ideal B) ≠ ⊥) (x : K) :
    IsClopen {P : MaximalSpectrum B | x ∈ prueferMaximalValuation B hB P} := by
  let : IsBezout B := isBezout_of_pruefer_of_nonzero_jacobson hB hJ
  obtain ⟨a, b, hb, hcop, rfl⟩ := exists_coprime_fraction B x
  have heq : {P : MaximalSpectrum B | (a : K) / (b : K) ∈ prueferMaximalValuation B hB P} =
      {P : MaximalSpectrum B | b ∉ P.asIdeal} := by
    ext P
    exact coprime_fraction_mem_prueferMaximalValuation_iff B hB hfield hcop hb P
  rw [heq]
  exact isClopen_maximal_basicOpen_of_nonzero_jacobson hJ b

/-- The canonical additive profile, normalized at a nonzero Jacobson element. -/
def branchProfile
    (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
    (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
    (t : B) (ht0 : t ≠ 0) (htJ : t ∈ Ideal.jacobson (⊥ : Ideal B))
    (x : K) (P : MaximalSpectrum B) : ℝ :=
  realValuationOrder (normalizedPrueferValuation B hB hfield t ht0 htJ P) x


section Profiles
variable (B : Subring K) [IsFractionRing B K] [Ring.KrullDimLE 1 B]
  (hB : IsPrueferDomain B) (hfield : ¬ IsField B)
  (t : B) (ht0 : t ≠ 0) (htJ : t ∈ Ideal.jacobson (⊥ : Ideal B))

omit [IsFractionRing B K] [Ring.KrullDimLE 1 B] in
private theorem profile_jacobson_ne_bot (t : B) (ht0 : t ≠ 0)
    (htJ : t ∈ Ideal.jacobson (⊥ : Ideal B)) : Ideal.jacobson (⊥ : Ideal B) ≠ ⊥ := by
  intro h
  exact ht0 (Ideal.mem_bot.mp (h ▸ htJ))

/-- The profile agrees with the scale-independent ratio of actual branch orders. -/
theorem branchProfile_eq_order_div (x : K) (P : MaximalSpectrum B) :
    branchProfile B hB hfield t ht0 htJ x P =
      realValuationOrder (prueferMaximalRealValuation B hB hfield P) x /
        realValuationOrder (prueferMaximalRealValuation B hB hfield P) t := by
  rw [branchProfile, normalizedPrueferValuation, normalizeRealValuation,
    realValuationOrder_scale, div_eq_mul_inv, mul_comm]

@[simp] theorem branchProfile_self (P : MaximalSpectrum B) :
    branchProfile B hB hfield t ht0 htJ t P = 1 :=
  realValuationOrder_normalize_self _ _ _

@[simp] theorem branchProfile_one (P : MaximalSpectrum B) :
    branchProfile B hB hfield t ht0 htJ 1 P = 0 :=
  realValuationOrder_one _

theorem branchProfile_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (P : MaximalSpectrum B) :
    branchProfile B hB hfield t ht0 htJ (x*y) P =
      branchProfile B hB hfield t ht0 htJ x P + branchProfile B hB hfield t ht0 htJ y P :=
  realValuationOrder_mul _ hx hy

theorem branchProfile_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (P : MaximalSpectrum B) :
    branchProfile B hB hfield t ht0 htJ (x/y) P =
      branchProfile B hB hfield t ht0 htJ x P - branchProfile B hB hfield t ht0 htJ y P :=
  realValuationOrder_div _ hx hy

theorem branchProfile_pow (x : K) (n : ℕ) (P : MaximalSpectrum B) :
    branchProfile B hB hfield t ht0 htJ (x^n) P =
      n * branchProfile B hB hfield t ht0 htJ x P :=
  realValuationOrder_pow _ _ _

theorem realValuationOrder_zpow (v : Valuation K ℝ≥0) (x : K) (n : ℤ) :
    realValuationOrder v (x^n) = n * realValuationOrder v x := by
  cases n with
  | ofNat n => simpa using realValuationOrder_pow v x n
  | negSucc n =>
      simp only [zpow_negSucc, realValuationOrder_inv, realValuationOrder_pow,
        Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
      ring

theorem branchProfile_nonneg_iff {x : K} (hx : x ≠ 0) (P : MaximalSpectrum B) :
    0 ≤ branchProfile B hB hfield t ht0 htJ x P ↔ x ∈ prueferMaximalValuation B hB P := by
  rw [branchProfile, realValuationOrder_nonneg_iff _ hx,
    normalizedPrueferValuation, normalizeRealValuation_le_one_iff]
  rw [← prueferMaximalRealValuation_valuationSubring B hB hfield P]
  rfl

theorem mem_pruefer_iff_branchProfile_nonneg {x : K} (hx : x ≠ 0) :
    x ∈ B ↔ ∀ P, 0 ≤ branchProfile B hB hfield t ht0 htJ x P := by
  rw [mem_pruefer_iff_mem_all_maximalValuations B hB]
  exact forall_congr' fun P => (branchProfile_nonneg_iff B hB hfield t ht0 htJ hx P).symm

theorem branchProfile_pos_of_jacobson {x : B} (hx0 : x ≠ 0)
    (hxJ : x ∈ Ideal.jacobson (⊥ : Ideal B)) (P : MaximalSpectrum B) :
    0 < branchProfile B hB hfield t ht0 htJ x P := by
  apply (realValuationOrder_normalize_pos_iff _ _ _ _).mpr
  exact pruefer_jacobson_real_order_pos B hB hfield hx0 hxJ P

theorem isClopen_branchProfile_le_rat {x : K} (hx : x ≠ 0) (q : ℚ) :
    IsClopen {P : MaximalSpectrum B | branchProfile B hB hfield t ht0 htJ x P ≤ q} := by
  have htK : (t : K) ≠ 0 := Subtype.coe_ne_coe.mpr ht0
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have heq : {P : MaximalSpectrum B | branchProfile B hB hfield t ht0 htJ x P ≤ q} =
      {P : MaximalSpectrum B | (t : K)^q.num / x^q.den ∈ prueferMaximalValuation B hB P} := by
    ext P
    simp only [Set.mem_ofPred_eq]
    rw [← branchProfile_nonneg_iff B hB hfield t ht0 htJ
      (div_ne_zero (zpow_ne_zero _ htK) (pow_ne_zero _ hx)) P,
      branchProfile_div B hB hfield t ht0 htJ (zpow_ne_zero _ htK) (pow_ne_zero _ hx),
      branchProfile_pow]
    change _ ↔ 0 ≤ realValuationOrder _ ((t : K)^q.num) - _
    rw [realValuationOrder_zpow]
    change _ ↔ 0 ≤ (q.num : ℝ) * branchProfile B hB hfield t ht0 htJ t P - _
    rw [branchProfile_self, mul_one, Rat.cast_def, le_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact isClopen_mem_prueferMaximalValuation B hB hfield (profile_jacobson_ne_bot B t ht0 htJ) _

theorem isClopen_rat_le_branchProfile {x : K} (hx : x ≠ 0) (q : ℚ) :
    IsClopen {P : MaximalSpectrum B | (q : ℝ) ≤ branchProfile B hB hfield t ht0 htJ x P} := by
  have htK : (t : K) ≠ 0 := Subtype.coe_ne_coe.mpr ht0
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have heq : {P : MaximalSpectrum B | (q : ℝ) ≤ branchProfile B hB hfield t ht0 htJ x P} =
      {P : MaximalSpectrum B | x^q.den / (t : K)^q.num ∈ prueferMaximalValuation B hB P} := by
    ext P
    simp only [Set.mem_ofPred_eq]
    rw [← branchProfile_nonneg_iff B hB hfield t ht0 htJ
      (div_ne_zero (pow_ne_zero _ hx) (zpow_ne_zero _ htK)) P,
      branchProfile_div B hB hfield t ht0 htJ (pow_ne_zero _ hx) (zpow_ne_zero _ htK),
      branchProfile_pow]
    change _ ↔ 0 ≤ _ - realValuationOrder _ ((t : K)^q.num)
    rw [realValuationOrder_zpow]
    change _ ↔ 0 ≤ _ - (q.num : ℝ) * branchProfile B hB hfield t ht0 htJ t P
    rw [branchProfile_self, mul_one, Rat.cast_def, div_le_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact isClopen_mem_prueferMaximalValuation B hB hfield (profile_jacobson_ne_bot B t ht0 htJ) _

/-- Actual branch profiles are continuous, including infinite branch spaces. -/
theorem continuous_branchProfile {x : K} (hx : x ≠ 0) :
    Continuous (branchProfile B hB hfield t ht0 htJ x) := by
  apply OrderTopology.continuous_iff.mpr
  intro c
  constructor
  · apply isOpen_iff_forall_mem_open.mpr
    intro P hP
    change c < branchProfile B hB hfield t ht0 htJ x P at hP
    obtain ⟨q, hcq, hqP⟩ := exists_rat_btwn hP
    refine ⟨{Q | (q : ℝ) ≤ branchProfile B hB hfield t ht0 htJ x Q}, ?_,
      (isClopen_rat_le_branchProfile B hB hfield t ht0 htJ hx q).isOpen, hqP.le⟩
    intro Q hQ
    exact hcq.trans_le hQ
  · apply isOpen_iff_forall_mem_open.mpr
    intro P hP
    change branchProfile B hB hfield t ht0 htJ x P < c at hP
    obtain ⟨q, hPq, hqc⟩ := exists_rat_btwn hP
    refine ⟨{Q | branchProfile B hB hfield t ht0 htJ x Q ≤ (q : ℝ)}, ?_,
      (isClopen_branchProfile_le_rat B hB hfield t ht0 htJ hx q).isOpen, hPq.le⟩
    intro Q hQ
    exact hQ.trans_lt hqc

/-- Both extrema of any nonzero fraction's profile are attained. -/
theorem branchProfile_exists_extrema {x : K} (hx : x ≠ 0) :
    ∃ Pmin Pmax : MaximalSpectrum B, ∀ P,
      branchProfile B hB hfield t ht0 htJ x Pmin ≤ branchProfile B hB hfield t ht0 htJ x P ∧
      branchProfile B hB hfield t ht0 htJ x P ≤ branchProfile B hB hfield t ht0 htJ x Pmax := by
  let : CompactSpace (MaximalSpectrum B) :=
    compactSpace_maximalSpectrum_of_nonzero_jacobson (profile_jacobson_ne_bot B t ht0 htJ)
  have hc : ContinuousOn (branchProfile B hB hfield t ht0 htJ x) Set.univ :=
    (continuous_branchProfile B hB hfield t ht0 htJ hx).continuousOn
  obtain ⟨Pmin, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc
  obtain ⟨Pmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc
  exact ⟨Pmin, Pmax, fun P => ⟨hmin (Set.mem_univ P), hmax (Set.mem_univ P)⟩⟩

/-- A positive profile has one strictly positive lower bound on every branch. -/
theorem branchProfile_uniform_pos_of_jacobson {x : B} (hx0 : x ≠ 0)
    (hxJ : x ∈ Ideal.jacobson (⊥ : Ideal B)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P, ε ≤ branchProfile B hB hfield t ht0 htJ x P := by
  obtain ⟨Pmin, _, hmin⟩ := branchProfile_exists_extrema B hB hfield t ht0 htJ
    (Subtype.coe_ne_coe.mpr hx0)
  exact ⟨_, branchProfile_pos_of_jacobson B hB hfield t ht0 htJ hx0 hxJ Pmin,
    fun P => (hmin P).1⟩

end Profiles
end HereditaryAtomicity
