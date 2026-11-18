import HereditaryAtomicity.ValuationAlgebra.ExtensionFiber
import HereditaryAtomicity.ValuationAlgebra.PurelyInseparable
import HereditaryAtomicity.ValuationProlongation
import HereditaryAtomicity.ValuationAlgebra.GaloisOrbit
import HereditaryAtomicity.ValuationAlgebra.NormalClosure
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Counting prolongations through field embeddings

The degree count is obtained from embeddings of the original upstairs field,
not from the degree of an auxiliary normal closure. The intermediate counting
lemmas below separate this linear-algebra argument from valuation conjugacy.
The final theorem proves the unconditional sharp finite-extension bound for
arbitrary valuation ranks, through the maximal separable subfield and a finite
Galois normal closure.
-/

namespace HereditaryAtomicity.ValuationAlgebra

open HereditaryAtomicity.ValuationProlongation

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- The restrictions of one valuation along all base-field embeddings form a
finite set of cardinality at most the degree of the embedded field. -/
theorem comap_embeddings_encard_le [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] (U : ValuationSubring M) :
    (Set.range fun e : L →ₐ[K] M => U.comap e.toRingHom).encard ≤
      Module.finrank K L := by
  calc
    _ ≤ (Set.univ : Set (L →ₐ[K] M)).encard := by
      simpa only [Set.image_univ] using
        Set.encard_image_le (fun e : L →ₐ[K] M => U.comap e.toRingHom) Set.univ
    _ = (Nat.card (L →ₐ[K] M) : ℕ∞) := by
      rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    _ ≤ Module.finrank K L := by
      exact_mod_cast card_algHom_le_finrank K L M

/-- Once every prolongation is realized by restricting one valuation along a
base-field embedding, the sharp field-degree bound follows. This implication
keeps the required realization assertion explicit. -/
theorem extensionFiber_encard_le_of_embeddings [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] (V : ValuationSubring K) (U : ValuationSubring M)
    (hrealize : ∀ W ∈ extensionFiber (algebraMap K L) V,
      ∃ e : L →ₐ[K] M, U.comap e.toRingHom = W) :
    (extensionFiber (algebraMap K L) V).encard ≤ Module.finrank K L := by
  apply (Set.encard_le_encard (t := Set.range fun e : L →ₐ[K] M =>
    U.comap e.toRingHom) ?_).trans (comap_embeddings_encard_le U)
  intro W hW
  exact hrealize W hW

/-- Prolongation existence and conjugacy in an auxiliary field imply the sharp
bound for the original extension. Counting embeddings of `L`, rather than
all automorphisms of `M`, keeps the bound equal to `[L : K]`. -/
theorem extensionFiber_encard_le_of_conjugacy [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [FiniteDimensional K L]
    (hconjugacy : ∀ U U' : ValuationSubring M,
      U.comap (algebraMap K M) = U'.comap (algebraMap K M) →
        ∃ σ : M ≃ₐ[K] M, U.comap σ.toRingHom = U')
    (V : ValuationSubring K) :
    (extensionFiber (algebraMap K L) V).encard ≤ Module.finrank K L := by
  obtain ⟨U, hU⟩ := exists_prolongation (algebraMap K M) V
  apply extensionFiber_encard_le_of_embeddings V U
  intro W hW
  obtain ⟨U', hU'⟩ := exists_prolongation (algebraMap L M) W
  have heq : U.comap (algebraMap K M) = U'.comap (algebraMap K M) := by
    rw [hU, IsScalarTower.algebraMap_eq K L M]
    change V = (U'.comap (algebraMap L M)).comap (algebraMap K L)
    rw [hU', hW]
  obtain ⟨σ, hσ⟩ := hconjugacy U U' heq
  refine ⟨σ.toAlgHom.comp (IsScalarTower.toAlgHom K L M), ?_⟩
  change (U.comap σ.toRingHom).comap (algebraMap L M) = W
  rw [hσ, hU']

/-- Injective restriction on the upper part of a tower transfers a bound for
fibers over the original base. The embeddings remain explicit. -/
theorem extensionFiber_encard_le_of_injective_tower (f : K →+* L) (g : L →+* M)
    (hinj : Function.Injective (fun W : ValuationSubring M => W.comap g))
    (V : ValuationSubring K) :
    (extensionFiber (g.comp f) V).encard ≤ (extensionFiber f V).encard := by
  refine Set.encard_le_encard_of_injOn (f := fun W : ValuationSubring M => W.comap g)
    ?_ hinj.injOn
  intro W hW
  exact hW

/-- The purely inseparable part of a finite extension cannot increase the
number of prolongations; any bound for the maximal separable subfield suffices. -/
theorem extensionFiber_encard_le_separableClosure [Algebra K L]
    [FiniteDimensional K L] (V : ValuationSubring K) :
    (extensionFiber (algebraMap K L) V).encard ≤
      (extensionFiber (algebraMap K (separableClosure K L)) V).encard := by
  convert extensionFiber_encard_le_of_injective_tower
    (algebraMap K (separableClosure K L)) (algebraMap (separableClosure K L) L)
    comap_injective_of_purelyInseparable V using 1
  rw [IsScalarTower.algebraMap_eq K (separableClosure K L) L]

/-- Reduction of the sharp finite-extension bound to its separable part. -/
theorem extensionFiber_encard_le_of_separableClosure_bound [Algebra K L]
    [FiniteDimensional K L] (V : ValuationSubring K)
    (hsep : (extensionFiber (algebraMap K (separableClosure K L)) V).encard ≤
      Module.finrank K (separableClosure K L)) :
    (extensionFiber (algebraMap K L) V).encard ≤ Module.finrank K L := by
  apply (extensionFiber_encard_le_separableClosure V).trans (hsep.trans ?_)
  exact_mod_cast Module.finrank_bot_le_finrank_of_isScalarTower K (separableClosure K L) L

/-- The sharp degree bound for a finite separable extension. The auxiliary
normal closure may have much larger degree; only embeddings of the original
upstairs field are counted. -/
theorem extensionFiber_encard_le_finrank_of_isSeparable [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (V : ValuationSubring K) :
    (extensionFiber (algebraMap K L) V).encard ≤ Module.finrank K L := by
  let M := IntermediateField.normalClosure K L (AlgebraicClosure L)
  have : IsGalois K M := isGalois_normalClosure_separable
  apply extensionFiber_encard_le_of_conjugacy (M := M) ?_ V
  intro U U' hres
  exact exists_comap_eq_of_comap_eq U U' hres

/-- A valuation of the base of a finite field extension has at most the field
degree many prolongations. This uses no rank, discreteness, separability, or
external extension-count assumption. -/
theorem extensionFiber_encard_le_finrank [Algebra K L] [FiniteDimensional K L]
    (V : ValuationSubring K) :
    (extensionFiber (algebraMap K L) V).encard ≤ Module.finrank K L := by
  apply extensionFiber_encard_le_of_separableClosure_bound V
  exact extensionFiber_encard_le_finrank_of_isSeparable V

/-- Every named valuation restriction fiber of a finite field extension is
finite, with no separate degree-bound hypothesis. -/
theorem extensionFiber_finite [Algebra K L] [FiniteDimensional K L]
    (V : ValuationSubring K) : (extensionFiber (algebraMap K L) V).Finite :=
  Set.finite_of_encard_le_coe (extensionFiber_encard_le_finrank V)

/-- Natural-cardinality version of the degree bound; finiteness is proved
independently by `extensionFiber_finite`. -/
theorem extensionFiber_ncard_le_finrank [Algebra K L] [FiniteDimensional K L]
    (V : ValuationSubring K) :
    (extensionFiber (algebraMap K L) V).ncard ≤ Module.finrank K L := by
  have h := extensionFiber_encard_le_finrank (L := L) V
  rw [← (extensionFiber_finite (L := L) V).cast_ncard_eq] at h
  exact_mod_cast h

/-- Finite sets of base valuations have finite inverse images under
restriction through a finite field extension. -/
theorem finite_preimage_of_finite_extension [Algebra K L] [FiniteDimensional K L]
    {Y : Set (ValuationSubring K)} (hY : Y.Finite) :
    ((fun W : ValuationSubring L => W.comap (algebraMap K L)) ⁻¹' Y).Finite :=
  finite_preimage_of_finite_fibers (algebraMap K L) extensionFiber_finite hY

end HereditaryAtomicity.ValuationAlgebra
