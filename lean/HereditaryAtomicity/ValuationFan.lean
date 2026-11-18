import Factorization.Hereditary
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Ideal.Operations

/-!
# The nonatomic subring of a valuation fan

The ring is the literal intersection in the common field. The private-zero
units are ambient units, but their nonunitness in the intersection is detected
at their own valuation. No existence of such a fan is assumed implicitly.
-/

namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- The literal intersection of the ambient ring, the limit, and the fan. -/
def fanSubring (D : Subring K) (V : ValuationSubring K)
    (W : ℕ → ValuationSubring K) : Subring K :=
  D ⊓ V.toSubring ⊓ ⨅ n, (W n).toSubring

@[simp]
theorem mem_fanSubring {D : Subring K} {V : ValuationSubring K}
    {W : ℕ → ValuationSubring K} {x : K} :
    x ∈ fanSubring D V W ↔ x ∈ D ∧ x ∈ V ∧ ∀ n, x ∈ W n := by
  simp only [fanSubring, Subring.mem_inf, Subring.mem_iInf]
  tauto

/-- Inclusion of the actual intersection into its limit valuation ring. -/
def fanToLimit (D : Subring K) (V : ValuationSubring K)
    (W : ℕ → ValuationSubring K) : fanSubring D V W →+* V :=
  Subring.inclusion (fun _ h => (mem_fanSubring.mp h).2.1)

/-- The prime ideal cut out by positivity at the limit valuation. -/
def fanIdeal (D : Subring K) (V : ValuationSubring K)
    (W : ℕ → ValuationSubring K) : Ideal (fanSubring D V W) :=
  Ideal.comap (fanToLimit D V W) (IsLocalRing.maximalIdeal V)

instance fanIdeal_isPrime (D : Subring K) (V : ValuationSubring K)
    (W : ℕ → ValuationSubring K) : (fanIdeal D V W).IsPrime := by
  dsimp [fanIdeal]
  infer_instance

@[simp]
theorem mem_fanIdeal {D : Subring K} {V : ValuationSubring K}
    {W : ℕ → ValuationSubring K} {y : fanSubring D V W} :
    y ∈ fanIdeal D V W ↔ (y : K) ∈ V.nonunits := by
  exact ValuationSubring.coe_mem_nonunits_iff.symm

/-- Private-zero ambient units. The own-valuation division property states the
uniformizer property in the ambient field, without choosing a value-group model. -/
structure FanUnitData (D : Subring K) (V : ValuationSubring K)
    (W : ℕ → ValuationSubring K) where
  unit : ℕ → Dˣ
  own_nonunit : ∀ n, ((unit n : D) : K) ∈ (W n).nonunits
  own_division : ∀ n (y : K), y ∈ (W n).nonunits → y / ((unit n : D) : K) ∈ W n
  limit_value : ∀ n, V.valuation ((unit n : D) : K) = 1
  other_value : ∀ n i, i ≠ n → (W i).valuation ((unit n : D) : K) = 1

namespace FanUnitData

variable {D : Subring K} {V : ValuationSubring K} {W : ℕ → ValuationSubring K}

/-- Each private-zero unit belongs to every ring in the intersection. -/
theorem unit_mem (data : FanUnitData D V W) (n : ℕ) :
    ((data.unit n : D) : K) ∈ fanSubring D V W := by
  refine mem_fanSubring.mpr ⟨(data.unit n : D).property, ?_, ?_⟩
  · rw [← V.valuation_le_one_iff, data.limit_value]
  · intro i
    by_cases hi : i = n
    · subst i
      exact (W n).nonunits_subset (data.own_nonunit n)
    · rw [← (W i).valuation_le_one_iff, data.other_value n i hi]

/-- A positive element of the fan ideal splits into two intrinsic nonunits,
provided it is positive at one private-zero valuation. -/
theorem split (data : FanUnitData D V W) {y : fanSubring D V W}
    (hy : y ∈ fanIdeal D V W) (n : ℕ) (hn : (y : K) ∈ (W n).nonunits) :
    ∃ a b : fanSubring D V W, y = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
  let u : Dˣ := data.unit n
  let uK : Kˣ := Units.map D.subtype.toMonoidHom u
  have huK : (uK : K) = ((data.unit n : D) : K) := rfl
  have hune : ((data.unit n : D) : K) ≠ 0 := uK.ne_zero
  have hyD : (y : K) ∈ D := (mem_fanSubring.mp y.property).1
  have hinv : (((data.unit n : D) : K))⁻¹ ∈ D := by
    have heq : (((u⁻¹ : Dˣ) : D) : K) = ((data.unit n : D) : K)⁻¹ := by
      change ((Units.map D.subtype.toMonoidHom u⁻¹ : Kˣ) : K) = (uK : K)⁻¹
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [← heq]
    exact ((u⁻¹ : Dˣ) : D).property
  have hquot : (y : K) / ((data.unit n : D) : K) ∈ fanSubring D V W := by
    refine mem_fanSubring.mpr ⟨?_, ?_, ?_⟩
    · simpa only [div_eq_mul_inv] using D.mul_mem hyD hinv
    · rw [← V.valuation_le_one_iff, map_div₀, data.limit_value, div_one]
      exact V.valuation_le_one (fanToLimit D V W y)
    · intro i
      by_cases hi : i = n
      · subst i
        exact data.own_division n y hn
      · rw [← (W i).valuation_le_one_iff, map_div₀, data.other_value n i hi, div_one]
        exact (W i).valuation_le_one ⟨y, (mem_fanSubring.mp y.property).2.2 i⟩
  let a : fanSubring D V W := ⟨((data.unit n : D) : K), data.unit_mem n⟩
  let b : fanSubring D V W := ⟨(y : K) / ((data.unit n : D) : K), hquot⟩
  refine ⟨a, b, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (y : K) = ((data.unit n : D) : K) * ((y : K) / ((data.unit n : D) : K))
    exact (mul_div_cancel₀ _ hune).symm
  · intro ha
    let f : fanSubring D V W →+* W n :=
      Subring.inclusion (fun _ hx => (mem_fanSubring.mp hx).2.2 n)
    have hone := ((W n).valuation_eq_one_iff (f a)).mp (ha.map f)
    exact (ne_of_lt ((W n).mem_nonunits_iff.mp (data.own_nonunit n))) hone
  · intro hb
    have hone := (V.valuation_eq_one_iff (fanToLimit D V W b)).mp
      (hb.map (fanToLimit D V W))
    have hyval := V.mem_nonunits_iff.mp (mem_fanIdeal.mp hy)
    have hbval : V.valuation (b : K) = V.valuation (y : K) := by
      change V.valuation ((y : K) / ((data.unit n : D) : K)) = _
      rw [map_div₀, data.limit_value, div_one]
    exact (ne_of_lt hyval) (hbval.symm.trans hone)

end FanUnitData

/-- A nonzero prime ideal with no irreducible elements obstructs atomicity. -/
theorem not_isAtomicDomain_of_prime_without_irreducibles
    {R : Type*} [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime]
    (hne : P ≠ ⊥) (hno : ∀ x ∈ P, ¬ Irreducible x) :
    ¬ Factorization.IsAtomicDomain R := by
  intro hA
  obtain ⟨x, hxP, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨s, hs, hprod⟩ := hA x hx
  have hsP : s.prod ∈ P := (Ideal.mem_iff_of_associated hprod).mpr hxP
  obtain ⟨p, hp, hpP⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem
    (inferInstance : P.IsPrime) s).mp hsP
  exact hno p hpP (hs p hp)

/-- A nonzero limit-positive element makes the prime ideal nonzero. -/
theorem fanIdeal_ne_bot {D : Subring K} {V : ValuationSubring K}
    {W : ℕ → ValuationSubring K} {h : K} (hne : h ≠ 0)
    (hD : h ∈ D) (hV : h ∈ V.nonunits) (hW : ∀ n, h ∈ W n) :
    fanIdeal D V W ≠ ⊥ := by
  intro heq
  let x : fanSubring D V W := ⟨h, mem_fanSubring.mpr ⟨hD, V.nonunits_subset hV, hW⟩⟩
  have hx : x ∈ fanIdeal D V W := mem_fanIdeal.mpr hV
  rw [heq, Ideal.mem_bot] at hx
  exact hne (congrArg Subtype.val hx)

/-- The fan is nonatomic when every nonzero limit-positive element is positive
at some member of the sequence. Convergence supplies this last hypothesis. -/
theorem not_isAtomicDomain_fanSubring {D : Subring K} {V : ValuationSubring K}
    {W : ℕ → ValuationSubring K} (data : FanUnitData D V W)
    (hne : fanIdeal D V W ≠ ⊥)
    (hpos : ∀ y : fanSubring D V W, y ≠ 0 → y ∈ fanIdeal D V W →
      ∃ n, (y : K) ∈ (W n).nonunits) :
    ¬ Factorization.IsAtomicDomain (fanSubring D V W) := by
  apply not_isAtomicDomain_of_prime_without_irreducibles (fanIdeal D V W) hne
  intro y hy hirr
  obtain ⟨n, hn⟩ := hpos y hirr.ne_zero hy
  obtain ⟨a, b, hab, ha, hb⟩ := data.split hy n hn
  exact (hirr.isUnit_or_isUnit hab).elim ha hb

end HereditaryAtomicity
