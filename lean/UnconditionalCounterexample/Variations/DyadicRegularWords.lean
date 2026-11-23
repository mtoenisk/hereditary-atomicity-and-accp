import UnconditionalCounterexample.Variations.DyadicColumnLifting
import UnconditionalCounterexample.Variations.DyadicEscapeDivisors

/-!
# Expressing pure dyadic elements in the scheduled regular generators

The columns of a zero-height element with zero supplementary values have no
auxiliary coefficients. Reindexing its balanced and adjacent coefficients
along the stage schedule gives the actual word whose exponents are bounded
by the escaping-divisor argument.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicEscape

open DyadicDeviations

namespace Generator

/-- Coefficients on the two regular families, combined in the generator index. -/
def pack (r q : Bool → ℕ →₀ ℤ) : Generator →₀ ℤ :=
  Finsupp.onFinset (Finset.univ.biUnion fun k =>
    (r k).support.image (balanced k) ∪ (q k).support.image (adjacent k))
    (fun | .balanced k n => r k n | .adjacent k n => q k n) (by
      rintro (⟨k, n⟩ | ⟨k, n⟩) hn
      · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨n, Finsupp.mem_support_iff.mpr hn, rfl⟩)⟩
      · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨n, Finsupp.mem_support_iff.mpr hn, rfl⟩)⟩)

def scheduled (s : Schedule) (e : Generator →₀ ℤ) : Word s where
  exponent := e.embDomain ⟨s.stage, s.injective⟩
  regular j hj := by
    by_contra hn
    exact hj (Finsupp.embDomain_of_notMem_range _ _ _ hn)

@[simp] theorem scheduled_exponent (s : Schedule) (e : Generator →₀ ℤ) (g : Generator) :
    (scheduled s e).exponent (s.stage g) = e g :=
  Finsupp.embDomain_apply_self ⟨s.stage, s.injective⟩ _ _

variable {J : Bool → Type*}

/-- Read off both channel families as the coefficient tuple of regular columns. -/
def columns : (Generator →₀ ℤ) →+ Columns J where
  toFun e := (fun k => e.comapDomain (balanced k) (fun _ _ _ _ h => (balanced.inj h).2),
    fun k => e.comapDomain (adjacent k) (fun _ _ _ _ h => (adjacent.inj h).2), 0)
  map_zero' := Prod.ext (funext fun _ => Finsupp.ext fun _ => rfl)
    (Prod.ext (funext fun _ => Finsupp.ext fun _ => rfl) rfl)
  map_add' _ _ := Prod.ext (funext fun _ => Finsupp.ext fun _ => rfl)
    (Prod.ext (funext fun _ => Finsupp.ext fun _ => rfl) (zero_add _).symm)

@[simp] theorem columns_pack (r q : Bool → ℕ →₀ ℤ) :
    columns (J := J) (pack r q) = (r, q, 0) := by
  exact Prod.ext (funext fun _ => Finsupp.ext fun _ => rfl)
    (Prod.ext (funext fun _ => Finsupp.ext fun _ => rfl) rfl)

@[simp] theorem scheduled_minus (s : Schedule) (r q : Bool → ℕ →₀ ℤ) (k : Bool) (n : ℕ) :
    (scheduled s (pack r q)).minus k n = r k n := scheduled_exponent _ _ _

@[simp] theorem scheduled_q (s : Schedule) (r q : Bool → ℕ →₀ ℤ) (k : Bool) :
    (scheduled s (pack r q)).q k = q k := Finsupp.ext fun _ => scheduled_exponent _ _ _

@[simp] theorem scheduled_plus (s : Schedule) (r q : Bool → ℕ →₀ ℤ) (k : Bool) (n : ℕ) :
    (scheduled s (pack r q)).plus k n = r k n + DyadicColumns.adjacent (q k) n := by
  simp [Word.plus]

variable {K : Type*} [CommGroup K]

/-- Actual product of the selected generators with these integral exponents. -/
def wordProduct (s : Schedule) (W : ℕ → K) (e : Generator →₀ ℤ) : K :=
  e.prod (fun g z => W (s.stage g) ^ z)

theorem wordProduct_add (s : Schedule) (W : ℕ → K) (e d : Generator →₀ ℤ) :
    wordProduct s W (e+d) = wordProduct s W e * wordProduct s W d :=
  Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add ..)

theorem scheduled_prod (s : Schedule) (W : ℕ → K) (e : Generator →₀ ℤ) :
    (scheduled s e).exponent.prod (fun j z => W j ^ z) = wordProduct s W e :=
  Finsupp.prod_embDomain

variable {G H : Type*}

/-- Multiplication by a raw at a specified stage acts by its one concrete
column. This identity propagates to the actual product for every signed finite
word. -/
theorem wordProduct_translates (s : Schedule) (W : ℕ → K) (v : K → Profile J G H)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (hsingle : ∀ g x, v (x * W (s.stage g)) =
      (v x).translate index sign (columns (Finsupp.single g 1)))
    (e : Generator →₀ ℤ) (x : K) :
    v (x * wordProduct s W e) = (v x).translate index sign (columns e) :=
  signed_word_translates index sign (fun g => W (s.stage g)) columns v e
    (fun g _ => hsingle g) x

end Generator

/-- The zero signed profile records all valuations of a unit. -/
def zeroProfile (J : Bool → Type*) (G H : Type*) : Profile J G H :=
  ⟨0, 0, 0, 0, ⟨0, 0, 0, 0⟩, 0⟩

variable {K G H : Type*} {J : Bool → Type*} [Field K]

/-- An actual element with only pure regular support equals, up to sign, an
actual scheduled R/Q word with precisely its plus and minus values. Inputs on
the regular generators are individual valuation identities. -/
theorem exists_signed_word_of_pure (s : Schedule) (W : ℕ → Kˣ) (v : Kˣ → Profile J G H)
    (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (h1 : v 1 = zeroProfile J G H) (hmass : ∀ a, (v a).MassEquations index sign)
    (hunit : ∀ a b : Kˣ, v a = v b → (a : K) = b ∨ (a : K) = -(b : K))
    (hraw : ∀ g x, v (x * W (s.stage g)) =
      (v x).translate index sign (Generator.columns (Finsupp.single g 1)))
    (a : Kˣ) (hh : (v a).height = 0) (hg : (v a).guards = (zeroProfile J G H).guards)
    (hhoriz : (v a).horizontal = 0) (haux : (v a).auxiliary = 0) :
    ∃ w : Word s,
      ((a : K) = w.exponent.prod (fun j z => (W j : K) ^ z) ∨
       (a : K) = -(w.exponent.prod (fun j z => (W j : K) ^ z))) ∧
      (∀ k n, w.plus k n = (v a).plus k n) ∧ ∀ k n, w.minus k n = (v a).minus k n := by
  have hm0 : (zeroProfile J G H).MassEquations index sign := h1 ▸ hmass 1
  obtain ⟨q, hq⟩ := (zeroProfile J G H).exists_columns_of_massEquations (v a) index sign
    hm0 (hmass a) hh.symm hg.symm hhoriz.symm
  let r := (v a).minusDeviation
  let e := Generator.pack r q
  have htranslate : (zeroProfile J G H).translate index sign (Generator.columns e) = v a := by
    rw [Generator.columns_pack]
    simpa [Profile.translate, zeroProfile, haux, r] using! hq
  let b := Generator.wordProduct s W e
  have hval : v b = v a := by
    have he := Generator.wordProduct_translates s W v index sign hraw e 1
    simpa [h1, htranslate, b] using he
  have hprod : ((Generator.scheduled s e).exponent.prod (fun j z => (W j : K) ^ z)) = (b : K) := by
    change _ = (Units.coeHom K) (Generator.wordProduct s W e)
    rw [← Generator.scheduled_prod s W e]
    simp [Finsupp.prod, map_prod]
  refine ⟨Generator.scheduled s e, ?_, ?_, ?_⟩
  · rw [hprod]
    exact hunit a b hval.symm
  · intro k n
    have he := congrArg (fun p : Profile J G H => p.plus k n) htranslate
    simpa [e, Profile.translate, Profile.addColumns, Profile.plus, zeroProfile] using he
  · intro k n
    simp [e, r, Profile.minus, hh]

end UnconditionalCounterexample.DyadicEscape
