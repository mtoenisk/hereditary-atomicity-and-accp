import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Valuation extension fibers along a named field map

These are restriction fibers, independently of any Rees or exceptional family.
The general finite-extension degree bound is an explicit input to the conditional
adapter below; defining a fiber does not establish that bound or nonemptiness.
-/

namespace HereditaryAtomicity.ValuationAlgebra

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- All valuation rings upstairs restricting to the specified base valuation
ring along the specified field embedding. -/
def extensionFiber (f : K →+* L) (V : ValuationSubring K) : Set (ValuationSubring L) :=
  {W | W.comap f = V}

@[simp] theorem mem_extensionFiber (f : K →+* L) (V : ValuationSubring K)
    (W : ValuationSubring L) : W ∈ extensionFiber f V ↔ W.comap f = V := Iff.rfl

/-- Membership tests use the actual field map. -/
theorem mem_iff_of_mem_extensionFiber (f : K →+* L) (V : ValuationSubring K)
    {W : ValuationSubring L} (hW : W ∈ extensionFiber f V) (x : K) :
    f x ∈ W ↔ x ∈ V := by
  change x ∈ W.comap f ↔ x ∈ V
  rw [hW]

/-- Distinct base valuations have disjoint full extension fibers. -/
theorem extensionFiber_disjoint (f : K →+* L) {V V' : ValuationSubring K}
    (h : V ≠ V') : Disjoint (extensionFiber f V) (extensionFiber f V') := by
  rw [Set.disjoint_left]
  intro W hW hW'
  exact h (hW.symm.trans hW')

/-- Restriction through a field tower gives the disjoint union of the intermediate
fibers; no finiteness or separability is needed. -/
theorem extensionFiber_comp (f : K →+* L) (g : L →+* M) (V : ValuationSubring K) :
    extensionFiber (g.comp f) V =
      ⋃ W ∈ extensionFiber f V, extensionFiber g W := by
  ext U
  constructor
  · intro hU
    exact Set.mem_iUnion₂.mpr ⟨U.comap g, hU, rfl⟩
  · intro hU
    obtain ⟨W, hW, hUW⟩ := Set.mem_iUnion₂.mp hU
    change (U.comap g).comap f = V
    rw [hUW]
    exact hW

/-- A finite set downstairs has finite inverse image whenever the full fibers
are finite. This is the finite-to-one input used for nonprincipal ultrafilters. -/
theorem finite_preimage_of_finite_fibers (f : K →+* L)
    (hf : ∀ V, (extensionFiber f V).Finite)
    {Y : Set (ValuationSubring K)} (hY : Y.Finite) :
    ((fun W : ValuationSubring L => W.comap f) ⁻¹' Y).Finite := by
  have heq : ((fun W : ValuationSubring L => W.comap f) ⁻¹' Y) =
      ⋃ V ∈ Y, extensionFiber f V := by
    ext W
    simp only [Set.mem_preimage, Set.mem_iUnion, mem_extensionFiber]
    exact ⟨fun h => ⟨W.comap f, h, rfl⟩, fun ⟨V, hV, h⟩ => h ▸ hV⟩
  rw [heq]
  exact hY.biUnion fun V _ => hf V

/-- Checked implication from the classical finite-extension degree bound.
The input is the mathematical extension-count theorem, not proved here. The
`Algebra` instance fixes the field embedding used by `Module.finrank`. -/
theorem finite_fibers_of_degree_bound [Algebra K L] [FiniteDimensional K L]
    (hdegree : ∀ V : ValuationSubring K,
      (extensionFiber (algebraMap K L) V).encard ≤ Module.finrank K L) :
    ∀ V : ValuationSubring K, (extensionFiber (algebraMap K L) V).Finite :=
  fun V => Set.finite_of_encard_le_coe (hdegree V)

/-- A positive power detects membership in any valuation subring. -/
theorem pow_mem_iff (V : ValuationSubring L) (x : L) {n : ℕ} (hn : n ≠ 0) :
    x ^ n ∈ V ↔ x ∈ V := by
  constructor
  · intro h
    apply V.mem_of_valuation_le_one
    have hp := V.valuation_le_one ⟨x ^ n, h⟩
    change V.valuation (x ^ n) ≤ 1 at hp
    rw [map_pow] at hp
    exact (pow_le_one_iff hn).mp hp
  · intro h
    exact V.toSubring.pow_mem h n

/-- If every upstairs element has a positive power in the actual base-field
image, restriction is injective. This abstracts the purely inseparable argument
without imposing a characteristic or a common value group. -/
theorem comap_injective_of_power_descent (f : K →+* L)
    (hpower : ∀ x : L, ∃ (n : ℕ) (_ : n ≠ 0) (y : K), x ^ n = f y) :
    Function.Injective (fun W : ValuationSubring L => W.comap f) := by
  intro W W' heq
  change W.comap f = W'.comap f at heq
  ext x
  obtain ⟨n, hn, y, hxy⟩ := hpower x
  rw [← pow_mem_iff W x hn, ← pow_mem_iff W' x hn, hxy]
  change y ∈ W.comap f ↔ y ∈ W'.comap f
  rw [heq]

/-- Under power descent every extension fiber contains at most one ring. -/
theorem extensionFiber_subsingleton_of_power_descent (f : K →+* L)
    (hpower : ∀ x : L, ∃ (n : ℕ) (_ : n ≠ 0) (y : K), x ^ n = f y)
    (V : ValuationSubring K) : (extensionFiber f V).Subsingleton := by
  intro W hW W' hW'
  exact comap_injective_of_power_descent f hpower (hW.trans hW'.symm)

end HereditaryAtomicity.ValuationAlgebra
