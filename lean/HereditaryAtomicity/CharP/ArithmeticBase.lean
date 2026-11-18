import HereditaryAtomicity.CharP.FunctionFieldCoordinate
import HereditaryAtomicity.CharP.LevelConductor
import HereditaryAtomicity.PrueferBranches
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The actual arithmetic base DVR

The localization of k[X] at (X) is kept as a literal subring of k(X).
The coherent chart X ↦ π then embeds it into the actual source stalk at any
prime containing π, and identifies its irreducible uniformizer with π.
-/

noncomputable section
namespace HereditaryAtomicity.CharP
open scoped Polynomial nonZeroDivisors

/-- The coordinate prime in the polynomial base. -/
def arithmeticBasePrime (k : Type*) [Field k] : Ideal k[X] :=
  Ideal.span {Polynomial.X}

instance arithmeticBasePrime_isPrime (k : Type*) [Field k] :
    (arithmeticBasePrime k).IsPrime := by
  apply (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr
  exact Polynomial.prime_X

theorem arithmeticBasePrime_ne_bot (k : Type*) [Field k] :
    arithmeticBasePrime k ≠ ⊥ := by
  intro h
  have hx : Polynomial.X ∈ arithmeticBasePrime k := Ideal.subset_span (Set.mem_singleton _)
  rw [h] at hx
  exact Polynomial.X_ne_zero (Ideal.mem_bot.mp hx)

/-- The literal localization k[X]_(X) inside k(X). -/
@[instance_reducible]
def arithmeticBaseRing (k : Type*) [Field k] : Subalgebra k[X] (RatFunc k) :=
  Localization.subalgebra.ofField (RatFunc k) (arithmeticBasePrime k).primeCompl
    (arithmeticBasePrime k).primeCompl_le_nonZeroDivisors

instance arithmeticBaseRing_isLocalization (k : Type*) [Field k] :
    IsLocalization.AtPrime (arithmeticBaseRing k) (arithmeticBasePrime k) := by
  unfold arithmeticBaseRing
  infer_instance

instance arithmeticBaseRing_isFractionRing (k : Type*) [Field k] :
    IsFractionRing (arithmeticBaseRing k).toSubring (RatFunc k) := by
  change IsFractionRing (arithmeticBaseRing k) (RatFunc k)
  infer_instance

instance arithmeticBaseRing_isDiscreteValuationRing (k : Type*) [Field k] :
    IsDiscreteValuationRing (arithmeticBaseRing k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X]
    (arithmeticBasePrime_ne_bot k) (arithmeticBaseRing k)

/-- The same literal base localization, regarded as a valuation subring. -/
@[instance_reducible]
def arithmeticBase (k : Type*) [Field k] : ValuationSubring (RatFunc k) := by
  let : IsDiscreteValuationRing (arithmeticBaseRing k).toSubring :=
    inferInstanceAs (IsDiscreteValuationRing (arithmeticBaseRing k))
  exact valuationSubringOfIsFractionRing (arithmeticBaseRing k).toSubring

instance arithmeticBase_isDiscreteValuationRing (k : Type*) [Field k] :
    IsDiscreteValuationRing (arithmeticBase k) :=
  inferInstanceAs (IsDiscreteValuationRing (arithmeticBaseRing k))

/-- The actual coordinate in the arithmetic DVR. -/
def arithmeticUniformizer (k : Type*) [Field k] : arithmeticBase k :=
  algebraMap k[X] (arithmeticBaseRing k) Polynomial.X

@[simp] theorem arithmeticUniformizer_coe (k : Type*) [Field k] :
    (arithmeticUniformizer k : RatFunc k) = RatFunc.X := by
  change algebraMap k[X] (RatFunc k) Polynomial.X = RatFunc.X
  simp

theorem arithmeticUniformizer_irreducible (k : Type*) [Field k] :
    Irreducible (arithmeticUniformizer k) := by
  change Irreducible (algebraMap k[X] (arithmeticBaseRing k) Polynomial.X)
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal (arithmeticBasePrime k) (arithmeticBaseRing k)]
  simp only [arithmeticBasePrime, Ideal.map_span, Set.image_singleton]

/-- Membership in the arithmetic DVR is an actual polynomial fraction whose
denominator does not vanish at zero. -/
theorem mem_arithmeticBase_iff (k : Type*) [Field k] (x : RatFunc k) :
    x ∈ arithmeticBase k ↔ ∃ f g : k[X], g.coeff 0 ≠ 0 ∧
      x = algebraMap k[X] (RatFunc k) f * (algebraMap k[X] (RatFunc k) g)⁻¹ := by
  change (∃ (f g : k[X]) (_ : g ∈ (arithmeticBasePrime k).primeCompl),
    x = algebraMap k[X] (RatFunc k) f * (algebraMap k[X] (RatFunc k) g)⁻¹) ↔ _
  have hmem (g : k[X]) : g ∈ (arithmeticBasePrime k).primeCompl ↔ g.coeff 0 ≠ 0 := by
    change g ∉ Ideal.span ({Polynomial.X} : Set k[X]) ↔ _
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
  constructor
  · rintro ⟨f, g, hg, hx⟩
    exact ⟨f, g, (hmem g).mp hg, hx⟩
  · rintro ⟨f, g, hg, hx⟩
    exact ⟨f, g, (hmem g).mpr hg, hx⟩

/-- A compatible rational-function chart embeds its arithmetic DVR into the
actual localization of the source at every prime containing the coordinate. -/
theorem arithmeticBase_image_mem_localization
    (k D F : Type*) [Field k] [CommRing D] [IsDomain D] [Field F]
    [Algebra k D] [Algebra k[X] D] [IsScalarTower k k[X] D]
    [Algebra D F] [IsFractionRing D F] [Algebra k[X] F]
    [IsScalarTower k[X] D F] [Algebra (RatFunc k) F]
    [IsScalarTower k[X] (RatFunc k) F]
    (M : Ideal D) [M.IsPrime] (hX : algebraMap k[X] D Polynomial.X ∈ M)
    (a : arithmeticBase k) :
    algebraMap (RatFunc k) F (a : RatFunc k) ∈
      Localization.subalgebra.ofField F M.primeCompl M.primeCompl_le_nonZeroDivisors := by
  obtain ⟨f, g, hg, ha⟩ := (mem_arithmeticBase_iff k (a : RatFunc k)).mp a.property
  refine ⟨algebraMap k[X] D f, algebraMap k[X] D g,
    polynomial_image_not_mem_of_constantCoeff_ne_zero k D M hX g hg, ?_⟩
  rw [ha, map_mul, map_inv₀]
  simp only [← IsScalarTower.algebraMap_apply]

/-- The arithmetic DVR image lies in the literal source prime stalk used by
the normalized-branch construction. -/
theorem arithmeticBase_image_mem_ofPrime
    (k F : Type*) [Field k] [Field F] (D : Subring F) [IsFractionRing D F]
    [Algebra k D] [Algebra k[X] D] [IsScalarTower k k[X] D]
    [Algebra k[X] F] [IsScalarTower k[X] D F] [Algebra (RatFunc k) F]
    [IsScalarTower k[X] (RatFunc k) F]
    (M : Ideal D) [M.IsPrime] (hX : algebraMap k[X] D Polynomial.X ∈ M)
    (a : arithmeticBase k) :
    algebraMap (RatFunc k) F (a : RatFunc k) ∈ (LocalSubring.ofPrime D M).toSubring := by
  rw [ofPrime_eq_localization_ofField]
  exact arithmeticBase_image_mem_localization k D F M hX a

/-- The coherent chart sends the arithmetic uniformizer to the chosen actual
coordinate, rather than to an unspecified associate. -/
theorem arithmeticUniformizer_coordinate_image
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (π : F) (hπ : Transcendental k π) :
    let := FunctionField.rationalAlgebra π hπ
    algebraMap (RatFunc k) F (arithmeticUniformizer k : RatFunc k) = π := by
  let := FunctionField.rationalAlgebra π hπ
  rw [arithmeticUniformizer_coe]
  exact FunctionField.rationalAlgebra_map_X π hπ

/-- Starting with a transcendental element of the source prime, the actual
coordinate chart discharges every base-DVR containment hypothesis. -/
theorem arithmeticBase_coordinate_image_mem_ofPrime
    (k F : Type*) [Field k] [Field F] [Algebra k F]
    (D : Subring F) [IsFractionRing D F] [Algebra k D] [IsScalarTower k D F]
    (π : D) (hπ : Transcendental k (π : F)) (M : Ideal D) [M.IsPrime]
    (hπM : π ∈ M) :
    let := FunctionField.rationalAlgebra (π : F) hπ
    ∀ a : arithmeticBase k, algebraMap (RatFunc k) F (a : RatFunc k) ∈
      (LocalSubring.ofPrime D M).toSubring := by
  let : Algebra k[X] D := (Polynomial.aeval π).toRingHom.toAlgebra
  let := FunctionField.polynomialAlgebra (k := k) (π : F)
  let := FunctionField.rationalAlgebra (π : F) hπ
  let : IsScalarTower k k[X] D := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k D c = Polynomial.aeval π (algebraMap k k[X] c)
    simp)
  let : IsScalarTower k[X] D F := IsScalarTower.of_algebraMap_eq (fun q => by
    change Polynomial.aeval (π : F) q = algebraMap D F (Polynomial.aeval π q)
    exact Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k D F) π q)
  let := FunctionField.coordinate_scalarTower (π : F) hπ
  apply arithmeticBase_image_mem_ofPrime k F D M
  change Polynomial.aeval π Polynomial.X ∈ M
  simpa using hπM

/-- Range formulation of the actual arithmetic-base embedding, matching the
source-stalk input of the normalization/prolongation homeomorphism. -/
theorem arithmeticBase_coordinate_image_mem_range_ofPrime
    (k F : Type*) [Field k] [Field F] [Algebra k F]
    (D : Subring F) [IsFractionRing D F] [Algebra k D] [IsScalarTower k D F]
    (π : D) (hπ : Transcendental k (π : F)) (M : Ideal D) [M.IsPrime]
    (hπM : π ∈ M) :
    let := FunctionField.rationalAlgebra (π : F) hπ
    ∀ a : arithmeticBase k, algebraMap (RatFunc k) F (a : RatFunc k) ∈
      (algebraMap (LocalSubring.ofPrime D M).toSubring F).range := by
  let := FunctionField.rationalAlgebra (π : F) hπ
  dsimp only
  intro a
  exact ⟨⟨_, arithmeticBase_coordinate_image_mem_ofPrime k F D π hπ M hπM a⟩, rfl⟩

end HereditaryAtomicity.CharP
