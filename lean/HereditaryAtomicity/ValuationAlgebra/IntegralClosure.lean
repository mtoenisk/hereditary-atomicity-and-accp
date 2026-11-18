import HereditaryAtomicity.ValuationAlgebra.DegreeBound
import Mathlib.RingTheory.LocalRing.LocalSubring

/-!
# Integral closure of a valuation in a finite field extension

All valuation rings in the intersections are actual prolongations along the
specified algebra map. The center-localization statements use the entire
mathlib integral closure, with no assumed Prüfer or localization property.
-/

namespace HereditaryAtomicity.ValuationAlgebra

open HereditaryAtomicity.ValuationProlongation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- In a finite separable extension, the entire integral closure is detected by
membership in all prolongations of the actual base valuation. -/
theorem isIntegral_iff_mem_all_extensions_of_isSeparable
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L] (x : L) :
    IsIntegral V x ↔ ∀ W : ValuationSubring L,
      W.comap (algebraMap K L) = V → x ∈ W := by
  constructor
  · intro hx W hW
    exact mem_of_isIntegral_of_comap_eq V W hW hx
  · intro hx
    let M := IntermediateField.normalClosure K L (AlgebraicClosure L)
    let : IsGalois K M := isGalois_normalClosure_separable
    let : Algebra V M := ((algebraMap K M).comp V.subtype).toAlgebra
    let : IsScalarTower V K M := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower V L M := IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply V K L]
      rw [← IsScalarTower.algebraMap_apply K L M]
      rfl
    obtain ⟨U, hU⟩ := exists_prolongation (algebraMap K M) V
    apply (isIntegral_algebraMap_iff (R := V) (B := M)).mp
    apply (isIntegral_iff_mem_all_conjugates V U hU (algebraMap L M x)).mpr
    intro σ
    have hr : ((U.comap σ.toRingHom).comap (algebraMap L M)).comap
        (algebraMap K L) = V := by
      rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq K L M,
        comap_algEquiv_restrict, hU]
    exact hx ((U.comap σ.toRingHom).comap (algebraMap L M)) hr

/-- In any finite field extension, membership in every prolongation is exactly
integrality over the original valuation ring. -/
theorem isIntegral_iff_mem_all_extensions [FiniteDimensional K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L] (x : L) :
    IsIntegral V x ↔ ∀ W : ValuationSubring L,
      W.comap (algebraMap K L) = V → x ∈ W := by
  constructor
  · intro hx W hW
    exact mem_of_isIntegral_of_comap_eq V W hW hx
  · intro hx
    let S := separableClosure K L
    let : Algebra V S := ((algebraMap K S).comp V.subtype).toAlgebra
    let : IsScalarTower V K S := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower V S L := IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply V K L]
      rw [IsScalarTower.algebraMap_apply K S L]
      rfl
    obtain ⟨n, hn, y, hy⟩ := power_descent_of_purelyInseparable (K := S) x
    have hyI : IsIntegral V y := by
      apply (isIntegral_iff_mem_all_extensions_of_isSeparable V y).mpr
      intro U hU
      obtain ⟨W, hW⟩ := exists_prolongation (algebraMap S L) U
      have hr : W.comap (algebraMap K L) = V := by
        rw [IsScalarTower.algebraMap_eq K S L]
        change (W.comap (algebraMap S L)).comap (algebraMap K S) = V
        rw [hW, hU]
      have hp : x ^ n ∈ W := W.pow_mem (hx W hr) n
      rw [hy] at hp
      change y ∈ W.comap (algebraMap S L) at hp
      rwa [hW] at hp
    have hpI : IsIntegral V (x ^ n) := by
      rw [hy]
      exact hyI.algebraMap
    exact hpI.of_pow (Nat.pos_of_ne_zero hn)

/-- The entire embedded integral closure equals the intersection over the
actual full restriction fiber. -/
theorem integralClosure_eq_iInf_extensions [FiniteDimensional K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L] :
    (integralClosure V L).toSubring =
      ⨅ W : extensionFiber (algebraMap K L) V, W.val.toSubring := by
  ext x
  rw [Subring.mem_iInf]
  change IsIntegral V x ↔ ∀ W : extensionFiber (algebraMap K L) V, x ∈ W.val
  rw [isIntegral_iff_mem_all_extensions]
  exact ⟨fun h W => h W.val W.property, fun h W hW => h ⟨W, hW⟩⟩

/-- Every element of a prolongation is a fraction of elements in the entire
integral closure with denominator outside its actual center. -/
theorem mem_extension_iff_fraction [FiniteDimensional K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) (x : L) :
    x ∈ W ↔ ∃ a s : integralClosure V L,
      s ∉ prolongationCenter V W hW ∧ x = (a : L) / (s : L) := by
  constructor
  · intro hx
    let := (extensionFiber_finite (L := L) V).fintype
    obtain ⟨s, hs0, hs, hsx, hsi⟩ := FiniteIntersection.exists_denominator
      (fun U : extensionFiber (algebraMap K L) V => U.val) ⟨W, hW⟩ hx
    have hsI : IsIntegral V s := (isIntegral_iff_mem_all_extensions V s).mpr
      (fun U hU => hs ⟨U, hU⟩)
    have hsxI : IsIntegral V (s * x) := (isIntegral_iff_mem_all_extensions V (s * x)).mpr
      (fun U hU => hsx ⟨U, hU⟩)
    refine ⟨⟨s * x, hsxI⟩, ⟨s, hsI⟩, ?_, ?_⟩
    · rw [mem_prolongationCenter, W.mem_nonunits_iff_or]
      exact not_or.mpr ⟨hs0, not_not.mpr hsi⟩
    · exact (eq_div_iff hs0).mpr (mul_comm _ _)
  · rintro ⟨a, s, hs, rfl⟩
    rw [mem_prolongationCenter, W.mem_nonunits_iff_or, not_or] at hs
    simpa only [div_eq_mul_inv] using W.mul_mem _ _
      (mem_of_isIntegral_of_comap_eq V W hW a.property) (not_not.mp hs.2)

/-- The canonical inclusion identifies a prolongation with the localization
of the entire integral closure at its center, in mathlib's actual predicate. -/
theorem isLocalization_integralClosure_prolongation [FiniteDimensional K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    letI := (integralClosureToProlongation V W hW).toAlgebra
    IsLocalization (prolongationCenter V W hW).primeCompl W := by
  let := (integralClosureToProlongation V W hW).toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact IsLocalRing.notMem_maximalIdeal.mp s.property
  · intro x
    obtain ⟨a, s, hs, heq⟩ := (mem_extension_iff_fraction V W hW x).mp x.property
    have hs0 : (s : L) ≠ 0 := by
      intro h
      exact hs ((Subtype.ext h : s = 0).symm ▸ (prolongationCenter V W hW).zero_mem)
    refine ⟨⟨a, ⟨s, hs⟩⟩, ?_⟩
    exact Subtype.ext ((eq_div_iff hs0).mp heq)
  · intro x y h
    refine ⟨1, ?_⟩
    have hxy : x = y := Subtype.ext (congrArg (fun z : W => (z : L)) h)
    rw [hxy]

/-- The localization representation is equality of the actual embedded rings,
using mathlib's `LocalSubring.ofPrime` construction. -/
theorem prolongation_toSubring_eq_ofPrime [FiniteDimensional K L]
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    W.toSubring = (@LocalSubring.ofPrime L _ (integralClosure V L).toSubring
      (prolongationCenter V W hW) (prolongationCenter_isPrime V W hW)).toSubring := by
  let B := integralClosure V L
  let P := prolongationCenter V W hW
  let : P.IsPrime := prolongationCenter_isPrime V W hW
  let T := (LocalSubring.ofPrime B.toSubring P).toSubring
  let : Algebra B T := inferInstanceAs (Algebra B.toSubring T)
  let : IsLocalization P.primeCompl T := IsLocalization.isLocalization_of_algEquiv
    P.primeCompl (LocalSubring.ofPrimeEquiv B.toSubring P)
  let := (integralClosureToProlongation V W hW).toAlgebra
  have : IsLocalization P.primeCompl W := isLocalization_integralClosure_prolongation V W hW
  let e : W ≃ₐ[B] T := IsLocalization.algEquiv P.primeCompl W T
  have he : T.subtype.comp e.toRingHom = W.subtype := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext a
    change (e (algebraMap B W a) : L) = (a : L)
    rw [e.commutes]
    rfl
  have hev (a : W) : (e a : L) = (a : L) := congrArg (fun f : W →+* L => f a) he
  apply le_antisymm
  · intro x hx
    have ht : (e ⟨x, hx⟩ : L) ∈ T := (e ⟨x, hx⟩).property
    rw [hev] at ht
    exact ht
  · intro x hx
    obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
    have hax : (a : L) = x := (hev a).symm.trans (congrArg Subtype.val ha)
    exact hax ▸ a.property

/-- Centers of prolongations are maximal ideals of the entire integral closure.
This is an integrality theorem, with no normalization-finiteness assumption. -/
instance prolongationCenter_isMaximal
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V) :
    (prolongationCenter V W hW).IsMaximal := by
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := V)
  rw [prolongationCenter_under]
  infer_instance

/-- Every maximal ideal of the entire integral closure is the actual center
of a prolongation. This existence statement does not need finite degree. -/
theorem exists_prolongation_with_center
    (V : ValuationSubring K) [Algebra V L] [IsScalarTower V K L]
    (P : Ideal (integralClosure V L)) [P.IsMaximal] :
    ∃ (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V),
      prolongationCenter V W hW = P := by
  let B := integralClosure V L
  let : (P : Ideal B.toSubring).IsPrime := inferInstanceAs P.IsPrime
  let T := LocalSubring.ofPrime B.toSubring P
  let : Algebra B T.toSubring := inferInstanceAs (Algebra B.toSubring T.toSubring)
  let : IsLocalization P.primeCompl T.toSubring := IsLocalization.isLocalization_of_algEquiv
    P.primeCompl (LocalSubring.ofPrimeEquiv B.toSubring P)
  obtain ⟨W, hTW⟩ := T.exists_le_valuationSubring
  let u : T.toSubring →+* W := Subring.inclusion hTW.1
  let : IsLocalHom u := hTW.2
  let g : B →+* W := u.comp (algebraMap B T.toSubring)
  have hc : Ideal.comap g (IsLocalRing.maximalIdeal W) = P := by
    dsimp only [g]
    rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact IsLocalization.AtPrime.under_maximalIdeal T.toSubring P
  let gV : V →+* W := g.comp (algebraMap V B)
  have hlocal : IsLocalHom gV := by
    apply ((IsLocalRing.local_hom_TFAE gV).out 5 1).mp
    dsimp only [gV]
    rw [← Ideal.comap_comap, hc]
    exact IsLocalRing.eq_maximalIdeal (inferInstanceAs (P.under V).IsMaximal)
  have heq (a : V) : (gV a : L) = algebraMap K L (a : K) := by
    change algebraMap V L a = algebraMap K L (a : K)
    rw [IsScalarTower.algebraMap_apply V K L]
    rfl
  have hmem : ∀ a : V, algebraMap K L (a : K) ∈ W :=
    fun a => heq a ▸ (gV a).property
  have hg : ((algebraMap K L).comp V.subtype).codRestrict W.toSubring hmem = gV := by
    ext a
    exact (heq a).symm
  let : IsLocalHom (((algebraMap K L).comp V.subtype).codRestrict W.toSubring hmem) := by
    rw [hg]
    exact hlocal
  have hW : W.comap (algebraMap K L) = V :=
    comap_eq_of_isLocalHom (algebraMap K L) V W hmem
  refine ⟨W, hW, ?_⟩
  exact hc

end HereditaryAtomicity.ValuationAlgebra
