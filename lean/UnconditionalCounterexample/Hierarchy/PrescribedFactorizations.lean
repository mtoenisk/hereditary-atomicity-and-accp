import UnconditionalCounterexample.Hierarchy.PrescribedPoleProfile
import Factorization.StrictHierarchy

/-!
# Factorizations of the distinguished prime by rows

Each row consists of its selected polynomials and one quotient completing
their product to the rational prime. All these factors have the single-slice
order profile and zero guard orders.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy.Prescribed.Generators

open GuardSupport DiscreteOrders Factorization Polynomial WithZero

variable {m : ℕ → ℕ} {p : PrimeIndex} (G : Generators m p)

private abbrev B := PoleAlgebra.generated G.poles

private def inField : (B G)ˣ →* RatFunc ℚ where
  toFun u := u.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

private def polyUnit (k : Slot m) : (B G)ˣ := by
  let f := algebraMap ℚ[X] (RatFunc ℚ) (G.poly k)
  have hf : f ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (G.irreducible k).ne_zero
  exact ⟨⟨f, PoleAlgebra.polynomial_mem _ _⟩, ⟨f⁻¹, PoleAlgebra.inverse_mem (Set.mem_range_self k)⟩,
    Subtype.ext (mul_inv_cancel₀ hf), Subtype.ext (inv_mul_cancel₀ hf)⟩

private theorem coe_polyUnit (k : Slot m) : G.inField (G.polyUnit k) =
    algebraMap ℚ[X] (RatFunc ℚ) (G.poly k) := rfl

private def primeUnit : (B G)ˣ :=
  Units.map (algebraMap ℚ (B G)).toMonoidHom
    (Units.mk0 (p.val : ℚ) (Nat.cast_ne_zero.mpr p.property.ne_zero))

private theorem coe_primeUnit : G.inField G.primeUnit = (p.val : RatFunc ℚ) := by
  change ((algebraMap ℚ (B G) (p.val : ℚ) : B G) : RatFunc ℚ) = _
  simp

private def rowUnit (i : ℕ) (j : Fin (m i + 2)) : (B G)ˣ :=
  Fin.lastCases (G.primeUnit / ∏ k, G.polyUnit ⟨i, k⟩) (fun k => G.polyUnit ⟨i, k⟩) j

private theorem rowUnit_prod (i : ℕ) : ∏ j, G.rowUnit i j = G.primeUnit := by
  rw [Fin.prod_univ_castSucc]
  simp [rowUnit]

private theorem inField_ne_zero (u : (B G)ˣ) : G.inField u ≠ 0 :=
  fun h => u.ne_zero (Subtype.ext h)

private theorem order_sum (v : Valuation (RatFunc ℚ) ℤᵐ⁰) (i : ℕ) :
    ∑ j, order v (G.inField (G.rowUnit i j)) = order v (p.val : RatFunc ℚ) := by
  let ord : (B G)ˣ →* Multiplicative ℤ := {
    toFun := fun u => Multiplicative.ofAdd (order v (G.inField u))
    map_one' := by simp
    map_mul' := fun u w => by change order v _ = _ + _; rw [map_mul, order_mul _ (G.inField_ne_zero u) (G.inField_ne_zero w)]; rfl }
  have h := congrArg Multiplicative.toAdd (map_prod ord (G.rowUnit i) Finset.univ)
  rw [G.rowUnit_prod] at h
  simpa [ord, G.coe_primeUnit] using h.symm

private theorem rowUnit_order (i : ℕ) (j : Fin (m i + 2)) (x : RowPoint m) :
    order (rowVal m p x) (G.inField (G.rowUnit i j)) = (sliceAt i j x : ℤ) := by
  have first (k : Fin (m i + 1)) :
      order (rowVal m p x) (G.inField (G.rowUnit i k.castSucc)) = (sliceAt i k.castSucc x : ℤ) := by
    simpa only [rowUnit, Fin.lastCases_castSucc, coe_polyUnit] using G.row_order ⟨i, k⟩ x
  refine Fin.lastCases ?_ first j
  have h := G.order_sum (rowVal m p x) i
  rw [Fin.sum_univ_castSucc] at h
  simp_rw [first] at h
  have hp : order (rowVal m p x) (p.val : RatFunc ℚ) = 1 := by simp [order, rowVal, EvaluationDVR.evaluationValuation]
  rw [hp] at h
  have ht : (∑ j, (sliceAt i j x : ℤ)) = 1 := by exact_mod_cast sum_sliceAt i x
  rw [Fin.sum_univ_castSucc] at ht
  omega

private theorem rowUnit_guard (i : ℕ) (j : Fin (m i + 2)) (q : PrimeIndex) (hq : q ≠ p) :
    order (guardVal q) (G.inField (G.rowUnit i j)) = 0 := by
  have first (k : Fin (m i + 1)) : order (guardVal q) (G.inField (G.rowUnit i k.castSucc)) = 0 := by
    simpa only [rowUnit, Fin.lastCases_castSucc, coe_polyUnit] using G.guard_order ⟨i, k⟩ q hq
  refine Fin.lastCases ?_ first j
  have h := G.order_sum (guardVal q) i
  rw [Fin.sum_univ_castSucc] at h
  simp_rw [first] at h
  simpa [order, guardVal, PairedDomain.vertical, PairedSpectrum.valuation_other_prime q p _ hq] using h

/-- The actual factor at a slot, including the quotient at the last slot. -/
def factor (i : ℕ) (j : Fin (m i + 2)) : G.domain := by
  let u := G.rowUnit i j
  refine ⟨G.inField u, (mem_ring_iff ..).mpr ⟨(u : B G).property, ?_, ?_⟩⟩
  · intro x
    apply (order_nonneg_iff _ (G.inField_ne_zero u)).mp
    exact (G.rowUnit_order i j x) ▸ Int.natCast_nonneg _
  · intro q hq
    apply (order_nonneg_iff _ (G.inField_ne_zero u)).mp
    exact (G.rowUnit_guard i j q hq).symm ▸ le_rfl

theorem factor_order (i : ℕ) (j : Fin (m i+2)) (x : RowPoint m) :
    order (rowVal m p x) (G.factor i j : RatFunc ℚ) = (sliceAt i j x : ℤ) := G.rowUnit_order i j x

theorem factor_guard (i : ℕ) (j : Fin (m i+2)) (q : PrimeIndex) (hq : q ≠ p) :
    order (guardVal q) (G.factor i j : RatFunc ℚ) = 0 := G.rowUnit_guard i j q hq

theorem factor_horizontal_unit (i : ℕ) (j : Fin (m i+2)) :
    IsUnit (ringSubtype m p G.poles (G.factor i j)) := (G.rowUnit i j).isUnit

theorem factor_prod (i : ℕ) : ∏ j, G.factor i j = (p.val : G.domain) := by
  apply Subtype.ext
  change G.domain.subtype (∏ j, G.factor i j) = (p.val : RatFunc ℚ)
  rw [map_prod]
  change ∏ j, G.inField (G.rowUnit i j) = (p.val : RatFunc ℚ)
  rw [← map_prod, G.rowUnit_prod, G.coe_primeUnit]


/-- At an original slot the factor is literally the selected polynomial. -/
theorem factor_castSucc_val (i : ℕ) (k : Fin (m i+1)) :
    (G.factor i k.castSucc : RatFunc ℚ) = algebraMap ℚ[X] (RatFunc ℚ) (G.poly ⟨i,k⟩) := by
  change G.inField (G.rowUnit i k.castSucc) = _
  rw [rowUnit, Fin.lastCases_castSucc, G.coe_polyUnit]

/-- The last factor is the distinguished prime divided by the product of
the other factors in the row. -/
theorem factor_last_val (i : ℕ) :
    (G.factor i (Fin.last (m i + 1)) : RatFunc ℚ) =
      p.val / ∏ k : Fin (m i + 1), algebraMap ℚ[X] (RatFunc ℚ) (G.poly ⟨i,k⟩) := by
  have hn : (∏ k : Fin (m i+1), algebraMap ℚ[X] (RatFunc ℚ) (G.poly ⟨i,k⟩)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ =>
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr (G.irreducible ⟨i,k⟩).ne_zero
  apply (eq_div_iff hn).mpr
  have h := congrArg G.domain.subtype (G.factor_prod i)
  rw [map_prod, Fin.prod_univ_castSucc] at h
  change (∏ k : Fin (m i+1), (G.factor i k.castSucc : RatFunc ℚ)) *
    (G.factor i (Fin.last (m i+1)) : RatFunc ℚ) = p.val at h
  simpa only [G.factor_castSucc_val, mul_comm] using h

private theorem factor_ne_zero (i : ℕ) (j : Fin (m i+2)) : (G.factor i j : RatFunc ℚ) ≠ 0 :=
  G.inField_ne_zero (G.rowUnit i j)

private theorem row_unit_zero (a : G.domain) (ha : IsUnit a) (x : RowPoint m) :
    order (rowVal m p x) (a : RatFunc ℚ) = 0 :=
  order_eq_zero_of_isUnit _ _ (fun _ hz => ((mem_ring_iff ..).mp hz).2.1 x) ha

theorem factor_irreducible (i : ℕ) (j : Fin (m i+2)) : Irreducible (G.factor i j) := by
  constructor
  · intro hu
    let x : RowPoint m := Function.update (fun _ => 0) i j
    have hh := G.row_unit_zero _ hu x
    simp [G.factor_order, sliceAt, x] at hh
  · intro a b hab
    have hf : IsUnit ((ringSubtype m p G.poles) a * (ringSubtype m p G.poles) b) := by
      rw [← map_mul, ← hab]
      exact G.factor_horizontal_unit i j
    have ha := isUnit_of_mul_isUnit_left hf
    have hb := isUnit_of_mul_isUnit_right hf
    have ha0 : (a : RatFunc ℚ) ≠ 0 := fun h => ha.ne_zero (Subtype.ext h)
    have hb0 : (b : RatFunc ℚ) ≠ 0 := fun h => hb.ne_zero (Subtype.ext h)
    have he : (G.factor i j : RatFunc ℚ) = (a : RatFunc ℚ) * (b : RatFunc ℚ) := congrArg Subtype.val hab
    have vg (q : PrimeIndex) (hq : q ≠ p) :
        order (guardVal q) (a : RatFunc ℚ) = 0 ∧ order (guardVal q) (b : RatFunc ℚ) = 0 := by
      have hs := G.factor_guard i j q hq
      rw [he, order_mul _ ha0 hb0] at hs
      have h₁ := (order_nonneg_iff _ ha0).mpr (((mem_ring_iff ..).mp a.property).2.2 q hq)
      have h₂ := (order_nonneg_iff _ hb0).mpr (((mem_ring_iff ..).mp b.property).2.2 q hq)
      omega
    obtain ⟨A, hA⟩ := G.profile_exists a ha
    have rows (x : RowPoint m) :
        (A.eval x : ℤ) + order (rowVal m p x) (b : RatFunc ℚ) = sliceAt i j x := by
      rw [hA, ← order_mul _ ha0 hb0, ← he, G.factor_order]
    have hle (x : RowPoint m) : A.eval x ≤ sliceAt i j x := by
      have h := rows x
      have h₀ := (order_nonneg_iff _ hb0).mpr (((mem_ring_iff ..).mp b.property).2.1 x)
      omega
    obtain h | h := A.eq_zero_or_sliceAt i j hle
    · exact Or.inl (G.unit_of_orders_zero a ha (fun x => by rw [← hA, h x]; simp)
        (fun q hq => (vg q hq).1))
    · exact Or.inr (G.unit_of_orders_zero b hb (fun x => by have hh := rows x; rw [h x] at hh; omega)
        (fun q hq => (vg q hq).2))

theorem factor_not_associated_of_ne_row {i k : ℕ} (hik : i ≠ k)
    (j : Fin (m i+2)) (l : Fin (m k+2)) : ¬ Associated (G.factor i j) (G.factor k l) := by
  rintro ⟨u, hu⟩
  obtain ⟨l', hl'⟩ := exists_ne l
  let x : RowPoint m := Function.update (Function.update (fun _ => 0) i j) k l'
  have hj : x i = j := by simp [x, hik]
  have hl : x k = l' := by simp [x]
  have h : (G.factor i j : RatFunc ℚ) * ((u : G.domain) : RatFunc ℚ) = (G.factor k l : RatFunc ℚ) :=
    congrArg Subtype.val hu
  have hu0 : ((u : G.domain) : RatFunc ℚ) ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have hv := congrArg (order (rowVal m p x)) h
  simp only [order_mul _ (G.factor_ne_zero i j) hu0, G.row_unit_zero _ u.isUnit, G.factor_order,
    add_zero, sliceAt, hj, hl, hl', ite_true, ite_false, Nat.cast_one, Nat.cast_zero] at hv
  exact one_ne_zero hv

/-- The factorization in row i, with permutation and individual associates removed. -/
def rowClasses (i : ℕ) : Multiset (Associates G.domain) :=
  Finset.univ.val.map (fun j => Associates.mk (G.factor i j))

theorem rowClasses_mem (i : ℕ) :
    G.rowClasses i ∈ atomicFactorizationClasses (p.val : G.domain) := by
  constructor
  · intro a ha
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp ha
    exact Associates.irreducible_mk.mpr (G.factor_irreducible i j)
  · change (∏ j, Associates.mk (G.factor i j)) = _
    rw [Associates.finsetProd_mk, G.factor_prod]

theorem rowClasses_card (i : ℕ) : (G.rowClasses i).card = m i + 2 := by simp [rowClasses]

theorem rowClasses_injective : Function.Injective G.rowClasses := by
  intro i k he
  by_contra hik
  have hin : Associates.mk (G.factor i 0) ∈ G.rowClasses i :=
    Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ _))
  rw [he] at hin
  obtain ⟨l, _, hl⟩ := Multiset.mem_map.mp hin
  exact G.factor_not_associated_of_ne_row hik 0 l (Associates.mk_eq_mk_iff_associated.mp hl.symm)

theorem infinite_factorizations :
    (atomicFactorizationClasses (p.val : G.domain)).Infinite :=
  (Set.infinite_range_of_injective G.rowClasses_injective).mono
    (Set.range_subset_iff.mpr G.rowClasses_mem)

theorem not_isFFDomain : ¬ IsFFDomain G.domain := fun h =>
  G.infinite_factorizations (h _ (Nat.cast_ne_zero.mpr p.property.ne_zero)).2

theorem row_mem_lengths (i : ℕ) : m i + 2 ∈ factorizationLengths (p.val : G.domain) := by
  rw [factorizationLengths_eq_image_card]
  exact ⟨_, G.rowClasses_mem i, G.rowClasses_card i⟩

theorem binary_infinite_length_two {p : PrimeIndex} (G : Generators (fun _ => 0) p) :
    {s ∈ atomicFactorizationClasses (p.val : G.domain) | s.card = 2}.Infinite := by
  apply (Set.infinite_range_of_injective G.rowClasses_injective).mono
  exact Set.range_subset_iff.mpr fun i => ⟨G.rowClasses_mem i, G.rowClasses_card i⟩

theorem growing_unbounded_lengths {p : PrimeIndex} (G : Generators id p) (N : ℕ) :
    ∃ n ∈ factorizationLengths (p.val : G.domain), N < n :=
  ⟨N+2, G.row_mem_lengths N, by omega⟩

theorem growing_not_isBFDomain {p : PrimeIndex} (G : Generators id p) :
    ¬ IsBFDomain G.domain := by
  intro h
  obtain ⟨N, hN⟩ := h (p.val : G.domain) (Nat.cast_ne_zero.mpr p.property.ne_zero)
  obtain ⟨n, ⟨s, hat, hp, he⟩, hlt⟩ := G.growing_unbounded_lengths N
  have hh := hN s (fun a ha => (hat a ha).not_isUnit) hp
  omega

end UnconditionalCounterexample.Hierarchy.Prescribed.Generators
