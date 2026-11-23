import UnconditionalCounterexample.PrincipalProfiles
import UnconditionalCounterexample.DiscreteOrders

/-!
# Laurent words for polynomial pole-algebra units

The selected irreducibles may carry any normalization of their leading
coefficient. Every unit of the embedded localization is a scalar times a
finite Laurent product of the given polynomials, indexed by their original
labels. One set of exponents computes its order at every discrete valuation.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.PoleUnits
open Polynomial PrincipalProfiles DiscreteOrders WithZero

variable {ι k : Type*} [Field k] (F : ι → k[X])

abbrev raw (i : ι) : RatFunc k := algebraMap k[X] (RatFunc k) (F i)

private theorem raw_ne (hF : ∀ i, Irreducible (F i)) (i : ι) : raw F i ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr (hF i).ne_zero

private def expressions (hF : ∀ i, Irreducible (F i)) : Submonoid (RatFunc k) where
  carrier := {x | ∃ c : k, c ≠ 0 ∧ ∃ e : ι →₀ ℤ, x = RatFunc.C c * word (raw F) e}
  one_mem' := ⟨1,one_ne_zero,0,by simp [word]⟩
  mul_mem' := by
    rintro _ _ ⟨c,hc,e,rfl⟩ ⟨d,hd,f,rfl⟩
    exact ⟨c*d,mul_ne_zero hc hd,e+f,by rw [map_mul,word_add _ (raw_ne F hF)]; ring⟩

private theorem constant_expression (hF : ∀ i, Irreducible (F i)) (c : k) (hc : c ≠ 0) :
    RatFunc.C c ∈ expressions F hF := ⟨c,hc,0,by simp [word]⟩

private theorem power_expression (hF : ∀ i, Irreducible (F i)) (p : MonicIrreducible k)
    (i : ι) (hd : p.val ∣ F i) (z : ℤ) : factor p ^ z ∈ expressions F hF := by
  classical
  obtain ⟨u,hu⟩ := (p.property.2.associated_of_dvd (hF i) hd).symm
  obtain ⟨c,hc,he⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hp : factor p = raw F i * RatFunc.C c := by
    change algebraMap k[X] (RatFunc k) p.val = _
    rw [← hu,← he,map_mul,RatFunc.algebraMap_C]
  refine ⟨c^z,zpow_ne_zero _ hc.ne_zero,Finsupp.single i z,?_⟩
  simp only [hp,mul_zpow,map_zpow₀,word,Finsupp.prod_single_index,zpow_zero,mul_comm]

/-- A unit has a finite signed word in the actual selected polynomials. -/
theorem exists_word (hF : ∀ i, Irreducible (F i)) (x : PoleAlgebra.generated (Set.range F))
    (hx : IsUnit x) : ∃ c : k, c ≠ 0 ∧ ∃ e : ι →₀ ℤ, (x : RatFunc k) =
      RatFunc.C c * word (raw F) e := by
  classical
  have hx0 : (x : RatFunc k) ≠ 0 := fun h => hx.ne_zero (Subtype.ext h)
  obtain ⟨y,hy⟩ := hx.exists_right_inv
  have hy' : (y : RatFunc k) = (x : RatFunc k)⁻¹ :=
    eq_inv_of_mul_eq_one_right (congrArg Subtype.val hy)
  have hS : ∀ f ∈ Set.range F, f ≠ 0 := by rintro _ ⟨i,rfl⟩; exact (hF i).ne_zero
  change (x : RatFunc k) ∈ expressions F hF
  rw [signed_factorization (x : RatFunc k) hx0]
  apply (expressions F hF).mul_mem (constant_expression F hF _ (div_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hx0))
    (Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.denom_ne_zero _))))
  apply Submonoid.prod_mem
  intro p hp
  obtain ⟨_,⟨i,rfl⟩,hd⟩ := exponent_support_of_unit _ hS x hx0 x.property (hy' ▸ y.property) p hp
  exact power_expression F hF p i hd _

/-- A finite signed word with nonzero entries is nonzero in the field. -/
theorem word_ne {K : Type*} [Field K] (G : ι → K) (hG : ∀ i, G i ≠ 0) (e : ι →₀ ℤ) :
    word G e ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hG i))

/-- A signed word computes every discrete order by summation against its exponents. -/
theorem order_word {K : Type*} [Field K] (G : ι → K) (hG : ∀ i, G i ≠ 0)
    (e : ι →₀ ℤ) (v : Valuation K ℤᵐ⁰) :
    order v (word G e) = ∑ i ∈ e.support, e i * order v (G i) := by
  classical
  change order v (∏ i ∈ e.support, G i ^ e i) = _
  generalize e.support = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj,Finset.sum_insert hj,order_mul v (zpow_ne_zero _ (hG j))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hG i))),order_zpow,ih]

theorem exists_orders (hF : ∀ i, Irreducible (F i)) (x : PoleAlgebra.generated (Set.range F))
    (hx : IsUnit x) : ∃ c : k, c ≠ 0 ∧ ∃ e : ι →₀ ℤ, ∀ v : Valuation (RatFunc k) ℤᵐ⁰,
      order v (x : RatFunc k) = order v (RatFunc.C c) + ∑ i ∈ e.support, e i * order v (raw F i) := by
  obtain ⟨c,hc,e,he⟩ := exists_word F hF x hx
  refine ⟨c,hc,e,fun v => ?_⟩
  rw [he,order_mul v ((map_ne_zero_iff _ RatFunc.C_injective).mpr hc) (word_ne _ (raw_ne F hF) _),
    order_word _ (raw_ne F hF)]

/-- Every signed product of selected factors belongs to the localization. -/
theorem word_mem (e : ι →₀ ℤ) : word (raw F) e ∈ PoleAlgebra.generated (Set.range F) := by
  apply Subalgebra.prod_mem
  intro i _
  cases e i with
  | ofNat n => exact Subalgebra.pow_mem _ (PoleAlgebra.polynomial_mem _ _) n
  | negSucc n =>
    change raw F i ^ Int.negSucc n ∈ _
    rw [zpow_negSucc,← inv_pow]
    exact Subalgebra.pow_mem _ (PoleAlgebra.inverse_mem (Set.mem_range_self i)) _

/-- The converse to the unit decomposition, in the embedded pole algebra itself. -/
theorem isUnit_iff (hF : ∀ i, Irreducible (F i)) (x : PoleAlgebra.generated (Set.range F)) :
    IsUnit x ↔ ∃ c : k, c ≠ 0 ∧ ∃ e : ι →₀ ℤ, (x : RatFunc k) = RatFunc.C c * word (raw F) e := by
  refine ⟨exists_word F hF x,?_⟩
  rintro ⟨c,hc,e,he⟩
  have hm : (x : RatFunc k)⁻¹ ∈ PoleAlgebra.generated (Set.range F) := by
    rw [he,mul_inv,← map_inv₀,← word_neg]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (word_mem F _)
  have hx0 : (x : RatFunc k) ≠ 0 := he ▸ mul_ne_zero ((map_ne_zero_iff _ RatFunc.C_injective).mpr hc)
    (word_ne _ (raw_ne F hF) _)
  exact isUnit_iff_exists_inv.mpr ⟨⟨_,hm⟩,Subtype.ext (mul_inv_cancel₀ hx0)⟩

/-- Agreement of generator orders modulo a fixed integer extends to every pole unit. -/
theorem order_modEq (hF : ∀ i, Irreducible (F i)) (x : PoleAlgebra.generated (Set.range F))
    (hx : IsUnit x) (v w : Valuation (RatFunc k) ℤᵐ⁰) (m : ℤ)
    (hc : ∀ c : k, c ≠ 0 → order v (RatFunc.C c) = order w (RatFunc.C c))
    (hord : ∀ i, Int.ModEq m (order v (raw F i)) (order w (raw F i))) :
    Int.ModEq m (order v (x : RatFunc k)) (order w (x : RatFunc k)) := by
  classical
  obtain ⟨c,hc',e,h⟩ := exists_orders F hF x hx
  rw [h v,h w,hc _ hc']
  apply Int.ModEq.add Int.ModEq.rfl
  generalize e.support = s
  induction s using Finset.induction_on with
  | empty => exact Int.ModEq.rfl
  | insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using ((hord i).mul_left (e i)).add ih

end UnconditionalCounterexample.Hierarchy.PoleUnits
