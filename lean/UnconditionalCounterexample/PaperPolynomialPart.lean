import UnconditionalCounterexample.PaperIntegerOrders

/-!
# The polynomial part of the constructed domain

The subring `A = D ∩ ℚ[t]` consists of those elements of the constructed domain
whose rational function is a polynomial. Inclusion induces the isomorphism
`A/nA ≃ D/nD` of §7.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperConstruction

open Polynomial

/-- The polynomial part of the actual domain, as a unital subring of that domain. -/
def polynomialPart : Subring domain :=
  (algebraMap ℚ[X] (RatFunc ℚ)).range.comap domain.subtype

theorem mem_polynomialPart_iff (x : domain) :
    x ∈ polynomialPart ↔ ∃ f : ℚ[X], algebraMap ℚ[X] (RatFunc ℚ) f = x.val :=
  Iff.rfl

/-- A polynomial belongs to the domain exactly when it is integral at every
primary and guard evaluation. -/
theorem polynomial_mem_domain_iff (f : ℚ[X]) :
    algebraMap ℚ[X] (RatFunc ℚ) f ∈ domain ↔
      ∀ v, PairedDomain.vertical places v (algebraMap ℚ[X] (RatFunc ℚ) f) ≤ 1 :=
  (IntersectionDomain.mem_intersection _ _ _).trans
    (and_iff_right (PoleAlgebra.polynomial_mem poles f))

theorem parameter_mem_polynomialPart : parameter ∈ polynomialPart :=
  ⟨X, RatFunc.algebraMap_X⟩

private def polynomialImageEquiv :=
  RingEquiv.ofLeftInverse (f := algebraMap ℚ[X] (RatFunc ℚ)) RatFunc.num_algebraMap

/-- Read an element of the polynomial part as its unique rational polynomial. -/
def polynomialPartToPolynomial : polynomialPart →+* ℚ[X] :=
  polynomialImageEquiv.symm.toRingHom.comp
    ((domain.subtype.comp polynomialPart.subtype).codRestrict _ fun x => x.property)

theorem polynomialPartToPolynomial_spec (x : polynomialPart) :
    algebraMap ℚ[X] (RatFunc ℚ) (polynomialPartToPolynomial x) = x.val.val := by
  exact congrArg Subtype.val (polynomialImageEquiv.apply_symm_apply ⟨x.val.val, x.property⟩)

theorem polynomialPartToPolynomial_injective : Function.Injective polynomialPartToPolynomial := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  rw [← polynomialPartToPolynomial_spec x, ← polynomialPartToPolynomial_spec y, h]

/-- Division in `D` by a nonzero integer preserves polynomiality. -/
theorem mem_polynomialPart_of_nat_mul_mem (n : ℕ) (hn : 0 < n) (x : domain)
    (hx : (n : domain) * x ∈ polynomialPart) : x ∈ polynomialPart := by
  obtain ⟨f, hf⟩ := (mem_polynomialPart_iff _).mp hx
  refine ⟨C (n : ℚ)⁻¹ * f, ?_⟩
  change algebraMap ℚ[X] (RatFunc ℚ) f = (n : RatFunc ℚ) * x.val at hf
  have hn' : (n : RatFunc ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [map_mul, RatFunc.algebraMap_C, map_inv₀, map_natCast, hf, inv_mul_cancel_left₀ hn']
  rfl

/-- Contraction of the ideal `nD` to the polynomial part is exactly `nA`. -/
theorem polynomialPart_comap_span_natCast (n : ℕ) (hn : 0 < n) :
    (Ideal.span {(n : domain)}).comap polynomialPart.subtype =
      Ideal.span {(n : polynomialPart)} := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    have hxA : x ∈ polynomialPart := mem_polynomialPart_of_nat_mul_mem n hn x (hx ▸ a.property)
    exact ⟨⟨x, hxA⟩, Subtype.ext hx⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, rfl⟩

/-- Every element of `D` is represented modulo `nD` by a linear integral polynomial. -/
theorem exists_integer_linear_mod_natCast (n : ℕ) (hn : 0 < n) (x : domain) :
    ∃ a b : ℤ, ∃ y : domain, x = a + b * parameter + (n : domain) * y := by
  let T := PaperTargets.integerOrder domain n
  obtain ⟨b, hb⟩ := integer_order_quotient_generated_by_parameter n hn
    (QuotientAddGroup.mk' T.toAddSubgroup x)
  rw [← map_zsmul] at hb
  have hmem : x - b • parameter ∈ T :=
    QuotientAddGroup.eq_iff_sub_mem.mp hb.symm
  obtain ⟨a, y, hy⟩ := (PaperTargets.mem_integerOrder domain n _).mp hmem
  refine ⟨a, b, y, ?_⟩
  rw [zsmul_eq_mul] at hy
  linear_combination hy

/-- The ring equivalence `A/nA ≃ D/nD` induced by the literal inclusion `A ↪ D`. -/
def polynomialPartQuotientEquiv (n : ℕ) (hn : 0 < n) :
    (polynomialPart ⧸ Ideal.span {(n : polynomialPart)}) ≃+*
      (domain ⧸ Ideal.span {(n : domain)}) := by
  let I : Ideal domain := Ideal.span {(n : domain)}
  have h := polynomialPart_comap_span_natCast n hn
  let φ := Ideal.quotientMap I polynomialPart.subtype h.ge
  refine RingEquiv.ofBijective φ ⟨Ideal.quotientMap_injective' h.le, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, b, y, hx⟩ := exists_integer_linear_mod_natCast n hn x
  let f : polynomialPart := a + b * (⟨parameter, parameter_mem_polynomialPart⟩ : polynomialPart)
  refine ⟨Ideal.Quotient.mk _ f, ?_⟩
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨-y, ?_⟩
  change (a : domain) + b * parameter - x = n * (-y)
  rw [hx]
  ring

@[simp] theorem polynomialPartQuotientEquiv_mk (n : ℕ) (hn : 0 < n) (x : polynomialPart) :
    polynomialPartQuotientEquiv n hn (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ x.val := rfl

end UnconditionalCounterexample.PaperConstruction
