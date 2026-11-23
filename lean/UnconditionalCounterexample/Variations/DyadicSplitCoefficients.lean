import UnconditionalCounterexample.Variations.DyadicLedger
import UnconditionalCounterexample.Variations.DyadicSplitSigned
import UnconditionalCounterexample.Variations.DyadicRegularWords
import UnconditionalCounterexample.Variations.DyadicSplitPrefix

/-!
# Encoding a signed split by the labels of the actual raw polynomials

The finite coefficient table stored at round opening contains balanced and
adjacent entries and one correction for each auxiliary prime. Reading those
labels back recovers the entire column combination from signed elimination.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open DyadicEscape DyadicDeviations GuardSupport

variable {J : Bool → Type*} (prime : (Σ k, J k) ↪ PrimeIndex)
    (index : (k : Bool) → J k → ℕ) (positive : (k : Bool) → J k → Bool)

/-- Include precisely the regular columns and the auxiliary columns with
their actual prime, sign and dyadic weight. -/
def basisLabel : Generator ⊕ (Σ k, J k) ↪ RawColumn where
  toFun
    | .inl (.balanced k n) => .balanced k n
    | .inl (.adjacent k n) => .adjacent k n
    | .inr ⟨k,j⟩ => .auxiliary (prime ⟨k,j⟩) k (index k j) (positive k j)
  inj' := by
    rintro (a | ⟨k,i⟩) (b | ⟨l,j⟩)
    · cases a <;> cases b <;> simp
    · cases a <;> simp
    · cases b <;> simp
    · intro h
      exact congrArg Sum.inr (prime.injective (RawColumn.auxiliary.inj h).1)

def rawCoefficients (c : Columns J) : RawColumn →₀ ℤ :=
  ((Generator.pack c.1 c.2.1).sumElim (Finsupp.sigmaFinsuppEquivPiFinsupp.symm c.2.2)).embDomain
    (basisLabel prime index positive)

theorem rawCoefficients_balanced (c : Columns J) (k : Bool) (n : ℕ) :
    rawCoefficients prime index positive c (.balanced k n) = c.1 k n :=
  Finsupp.embDomain_apply_self (basisLabel prime index positive) _ (.inl (.balanced k n))

theorem rawCoefficients_adjacent (c : Columns J) (k : Bool) (n : ℕ) :
    rawCoefficients prime index positive c (.adjacent k n) = c.2.1 k n :=
  Finsupp.embDomain_apply_self (basisLabel prime index positive) _ (.inl (.adjacent k n))

theorem rawCoefficients_auxiliary (c : Columns J) (k : Bool) (j : J k) :
    rawCoefficients prime index positive c
      (.auxiliary (prime ⟨k,j⟩) k (index k j) (positive k j)) = c.2.2 k j :=
  Finsupp.embDomain_apply_self (basisLabel prime index positive) _ (.inr ⟨k,j⟩)

/-- Restrict a raw coefficient table to its three actual basis families. -/
def columnsOfRaw : (RawColumn →₀ ℤ) →+ Columns J where
  toFun e := (fun k => e.comapDomain (.balanced k) (fun _ _ _ _ h => (RawColumn.balanced.inj h).2),
    fun k => e.comapDomain (.adjacent k) (fun _ _ _ _ h => (RawColumn.adjacent.inj h).2),
    fun k => e.comapDomain (fun j => .auxiliary (prime ⟨k,j⟩) k (index k j) (positive k j))
      (fun i _ j _ h => by
        have he := prime.injective (RawColumn.auxiliary.inj h).1
        exact Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq))
  map_zero' := by ext <;> rfl
  map_add' _ _ := by ext <;> rfl

@[simp] theorem columnsOfRaw_rawCoefficients (c : Columns J) :
    columnsOfRaw prime index positive (rawCoefficients prime index positive c) = c := by
  apply Prod.ext (funext fun k => Finsupp.ext fun n => rawCoefficients_balanced _ _ _ _ k n)
  exact Prod.ext (funext fun k => Finsupp.ext fun n => rawCoefficients_adjacent _ _ _ _ k n)
    (funext fun k => Finsupp.ext fun j => rawCoefficients_auxiliary _ _ _ _ k j)

variable {G H : Type*}

/-- At a fixed valuation site, a formal raw combination changes the order
additively, independent of the initial profile. -/
def rowChange (sign : (k : Bool) → J k → ℤ) (p : Profile J G H)
    (i : DyadicProfiles.Site (Supplement J G H)) : (RawColumn →₀ ℤ) →+ ℤ where
  toFun e := (p.translate index sign (columnsOfRaw prime index positive e)).signedValues i - p.signedValues i
  map_zero' := by simp
  map_add' e f := by
    rw [map_add, ← Profile.translate_add]
    have hc := Profile.translate_difference
      (p.translate index sign (columnsOfRaw prime index positive e)) p index sign (columnsOfRaw prime index positive f) i
    omega

theorem rowChange_eq_sum (sign : (k : Bool) → J k → ℤ) (p : Profile J G H)
    (i : DyadicProfiles.Site (Supplement J G H)) (e : RawColumn →₀ ℤ) :
    rowChange prime index positive sign p i e = e.sum (fun c z =>
      z * rowChange prime index positive sign p i (Finsupp.single c 1)) := by
  let row := rowChange prime index positive sign p i
  have single (c : RawColumn) (z : ℤ) : row (Finsupp.single c z) = z * row (Finsupp.single c 1) := by
    calc
      _ = row ((Finsupp.singleAddHom c) (z • (1 : ℤ))) := by simp
      _ = row (z • Finsupp.single c 1) := by rw [map_zsmul]; rfl
      _ = _ := by simp only [map_zsmul, zsmul_eq_mul, Int.cast_id]
  calc
    row e = row (e.sum Finsupp.single) := congrArg row e.sum_single.symm
    _ = _ := by
      unfold Finsupp.sum
      rw [map_sum]
      exact Finset.sum_congr rfl (fun c _ => single c _)

/-- The order prescribed for the new factor already equals the order of its
prefix over each modulus fibre: the reserved column contributes zero there.
This computation uses no valuation of the unselected raw. -/
theorem prefix_order_of_zero_row (sign : (k : Bool) → J k → ℤ) (p : Profile J G H)
    (i : DyadicProfiles.Site (Supplement J G H)) (v : Valuation (RatFunc ℚ) (WithZero (Multiplicative ℤ)))
    {n : ℕ} (P : RecursivePrefix.Prefix n) (base : (RatFunc ℚ)ˣ) (e : RawColumn →₀ ℤ) (label : ℕ → RawColumn)
    (hs : e.support ⊆ (Finset.range (n+1)).image label) (hinj : Set.InjOn label ↑(Finset.range (n+1)))
    (hb : DiscreteOrders.order v (base : RatFunc ℚ) = p.signedValues i)
    (hraw : ∀ j < n, DiscreteOrders.order v (P.generators j) =
      rowChange prime index positive sign p i (Finsupp.single (label j) 1))
    (hzero : rowChange prime index positive sign p i (Finsupp.single (label n) 1) = 0) :
    DiscreteOrders.order v (DyadicSplit.prefixFactor P base (fun j => e (label j)) : RatFunc ℚ) =
      (p.translate index sign (columnsOfRaw prime index positive e)).signedValues i := by
  have he := rowChange_eq_sum prime index positive sign p i e
  rw [e.sum_of_support_subset hs _ (by simp), Finset.sum_image hinj, Finset.sum_range_succ,
    hzero, mul_zero, add_zero] at he
  rw [DyadicSplit.prefixFactor_order, hb]
  have hsum := Finset.sum_congr (s₁ := Finset.range n) rfl
    (fun j hj => congrArg (fun z : ℤ => e (label j) * z) (hraw j (Finset.mem_range.mp hj)))
  rw [hsum, ← he]
  change p.signedValues i + ((p.translate index sign (columnsOfRaw prime index positive e)).signedValues i -
    p.signedValues i) = _
  omega

/-- Signed profile elimination now produces a finite instruction over ledger
labels, with coefficient exactly one on the reserved balanced raw. -/
theorem exists_split_coefficients (sign : (k : Bool) → J k → ℤ) {p u v : Profile J G H} {M : ℕ}
    (split : SplitAt index sign p u v M) (base : Profile J G H)
    (hb : base.MassEquations index sign) (hh : base.height = u.height)
    (hg : base.guards = u.guards) (hhoriz : base.horizontal = u.horizontal) (hsite : base.minus true M = 0) :
    ∃ e : RawColumn →₀ ℤ, e (.balanced true M) = 1 ∧
      base.translate index sign (columnsOfRaw prime index positive e) = u := by
  obtain ⟨hR, q, hq⟩ := split.reserved_coefficient index sign base hb hh hg hhoriz hsite
  let c : Columns J := (fun k => u.minusDeviation k - base.minusDeviation k, q,
    fun k => u.auxiliary k - base.auxiliary k)
  refine ⟨rawCoefficients prime index positive c, (rawCoefficients_balanced _ _ _ _ _ _).trans hR, ?_⟩
  rw [columnsOfRaw_rawCoefficients]
  exact hq

/-- Restrict a split to the labels available in its finite block. A plus
discrepancy through index `N` only requires adjacent generators below `N`.
Auxiliary coefficients are supported exactly where the old and target
auxiliary orders differ. -/
theorem exists_split_coefficients_supported (sign : (k : Bool) → J k → ℤ)
    {p u v : Profile J G H} {M : ℕ} (split : SplitAt index sign p u v M) (base : Profile J G H)
    (hb : base.MassEquations index sign) (hh : base.height = u.height) (hg : base.guards = u.guards)
    (hhoriz : base.horizontal = u.horizontal) (hsite : base.minus true M = 0) (N : ℕ) (available : Finset RawColumn)
    (hr : ∀ k, (u.minusDeviation k - base.minusDeviation k).support ⊆ Finset.range N)
    (hd : ∀ k, (u.plusDeviation k - base.plusDeviation k - (u.minusDeviation k - base.minusDeviation k)
      + DyadicColumns.auxiliaryTransfer (index k) (sign k) (u.auxiliary k - base.auxiliary k)).support ⊆
        Finset.range (N+1))
    (hreg : ∀ k n, n < N → RawColumn.balanced k n ∈ available ∧ RawColumn.adjacent k n ∈ available)
    (haux : ∀ k j, j ∈ (u.auxiliary k - base.auxiliary k).support →
      RawColumn.auxiliary (prime ⟨k,j⟩) k (index k j) (positive k j) ∈ available) :
    ∃ e : RawColumn →₀ ℤ, e.support ⊆ available ∧ e (.balanced true M) = 1 ∧
      base.translate index sign (columnsOfRaw prime index positive e) = u := by
  classical
  obtain ⟨hR,q,hq⟩ := split.reserved_coefficient index sign base hb hh hg hhoriz hsite
  let c : Columns J := (fun k => u.minusDeviation k - base.minusDeviation k, q,
    fun k => u.auxiliary k - base.auxiliary k)
  let e := rawCoefficients prime index positive c
  refine ⟨e,?_, (rawCoefficients_balanced _ _ _ _ _ _).trans hR,?_⟩
  · intro x hx
    have hne := Finsupp.mem_support_iff.mp hx
    dsimp only [e,rawCoefficients] at hx
    rw [Finsupp.support_embDomain] at hx
    obtain ⟨g,_,rfl⟩ := Finset.mem_map.mp hx
    rcases g with (⟨k,n⟩ | ⟨k,n⟩) | ⟨k,j⟩
    · have hrn := (rawCoefficients_balanced prime index positive c k n) ▸ hne
      exact (hreg k n (Finset.mem_range.mp (hr k (Finsupp.mem_support_iff.mpr hrn)))).1
    · have hqn := (rawCoefficients_adjacent prime index positive c k n) ▸ hne
      have he := congrArg (fun w : Profile J G H => w.plusDeviation k) hq
      change base.plusDeviation k + c.1 k + DyadicColumns.adjacent (q k) -
        DyadicColumns.auxiliaryTransfer (index k) (sign k) (c.2.2 k) = u.plusDeviation k at he
      have hcol : DyadicColumns.adjacent (q k) = u.plusDeviation k - base.plusDeviation k - c.1 k +
          DyadicColumns.auxiliaryTransfer (index k) (sign k) (c.2.2 k) := by rw [← he]; abel
      have hs := DyadicColumns.adjacent_support_lt (q k) N (hcol ▸ hd k)
      exact (hreg k n (Finset.mem_range.mp (hs (Finsupp.mem_support_iff.mpr hqn)))).2
    · apply haux k j
      exact Finsupp.mem_support_iff.mpr ((rawCoefficients_auxiliary prime index positive c k j) ▸ hne)
  · rw [show e = rawCoefficients prime index positive c from rfl,columnsOfRaw_rawCoefficients]
    exact hq

/-- Valuation identities for the selected normalized raws realize the given
encoded split. Unrequested or ill-formed labels never enter the product. -/
theorem splitWord_profile {K : Type*} [CommGroup K] (sign : (k : Bool) → J k → ℤ)
    (signed : K → Profile J G H) (w : RawColumn → K) (base : K) (e : RawColumn →₀ ℤ)
    (u : Profile J G H) (he : (signed base).translate index sign (columnsOfRaw prime index positive e) = u)
    (hraw : ∀ c ∈ e.support, ∀ x, signed (x * w c) =
      (signed x).translate index sign (columnsOfRaw prime index positive (Finsupp.single c 1))) :
    signed (base * DyadicSplit.weightedProduct w e) = u :=
  (signed_word_translates index sign w (columnsOfRaw prime index positive) signed e hraw base).trans he

end UnconditionalCounterexample.Variations.DyadicLedger
