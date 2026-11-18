import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Clopen
import Mathlib.Topology.Metrizable.Urysohn
import HereditaryAtomicity.ValuationProlongation

/-!
# Compact patch topology on actual valuation rings

The patch topology records both membership and nonmembership in an embedded valuation
ring. Ultrafilter compactness, countable metrizability, and compactness of positive
support apply independently of a finite-extension or rank hypothesis.
-/

open Set Filter TopologicalSpace
open scoped Topology

namespace HereditaryAtomicity.ValuationPatch

noncomputable section

universe u v w
variable {K : Type u} {F : Type v} [Field K] [Field F]

/-- All Boolean membership tests determine the actual embedded ring. -/
noncomputable def membership (V : ValuationSubring K) : K → Bool :=
  fun x => @decide (x ∈ V) (Classical.propDecidable _)

@[simp] theorem membership_eq_true (V : ValuationSubring K) (x : K) :
    membership V x = true ↔ x ∈ V := by
  classical
  simp [membership]

@[simp] theorem membership_eq_false (V : ValuationSubring K) (x : K) :
    membership V x = false ↔ x ∉ V := by
  classical
  simp [membership]

theorem membership_injective : Function.Injective (membership (K := K)) := by
  intro V W h
  ext x
  simpa only [membership_eq_true] using
    (eq_iff_iff.mp (congrArg (fun b => b x = true) h))

/-- Patch topology is induced by the membership map into the Boolean product. -/
@[instance_reducible]
noncomputable def patchTopology : TopologicalSpace (ValuationSubring K) :=
  TopologicalSpace.induced membership inferInstance

scoped instance : TopologicalSpace (ValuationSubring K) := patchTopology

theorem isEmbedding_membership : Topology.IsEmbedding (membership (K := K)) :=
  membership_injective.isEmbedding_induced

scoped instance : T2Space (ValuationSubring K) := isEmbedding_membership.t2Space

/-- Eventual membership along an ultrafilter is again an actual valuation ring. -/
def ultrafilterLimit {I : Type w} (U : Ultrafilter I) (A : I → ValuationSubring K) :
    ValuationSubring K where
  carrier := {x | ∀ᶠ i in U, x ∈ A i}
  zero_mem' := Eventually.of_forall fun i => (A i).zero_mem
  one_mem' := Eventually.of_forall fun i => (A i).one_mem
  add_mem' := fun hx hy => (hx.and hy).mono fun i h => (A i).toSubring.add_mem h.1 h.2
  mul_mem' := fun hx hy => (hx.and hy).mono fun i h => (A i).toSubring.mul_mem h.1 h.2
  neg_mem' := fun hx => hx.mono fun i h => (A i).toSubring.neg_mem h
  mem_or_inv_mem' x := Ultrafilter.eventually_or.mp
    (Eventually.of_forall fun i => (A i).mem_or_inv_mem x)

theorem tendsto_ultrafilterLimit {I : Type w} (U : Ultrafilter I)
    (A : I → ValuationSubring K) : Tendsto A U (𝓝 (ultrafilterLimit U A)) := by
  apply isEmbedding_membership.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro x
  rw [nhds_discrete, tendsto_pure]
  by_cases hx : x ∈ ultrafilterLimit U A
  · have he : ∀ᶠ i in U, x ∈ A i := hx
    exact he.mono fun i hi => by simp [membership, hx, hi]
  · have hn : ∀ᶠ i in U, x ∉ A i := Ultrafilter.eventually_not.mpr hx
    exact hn.mono fun i hi => by simp [membership, hx, hi]

theorem isCompact_univ : IsCompact (Set.univ : Set (ValuationSubring K)) := by
  apply isCompact_iff_ultrafilter_le_nhds.mpr
  intro U _
  refine ⟨ultrafilterLimit U id, Set.mem_univ _, ?_⟩
  simpa only [Filter.Tendsto, Filter.map_id] using tendsto_ultrafilterLimit U id

scoped instance : CompactSpace (ValuationSubring K) := ⟨isCompact_univ⟩

scoped instance [Countable K] : SecondCountableTopology (ValuationSubring K) :=
  isEmbedding_membership.secondCountableTopology

scoped instance [Countable K] : MetrizableSpace (ValuationSubring K) := by
  infer_instance

theorem continuous_comap (f : F →+* K) :
    Continuous (fun V : ValuationSubring K => V.comap f) := by
  apply isEmbedding_membership.continuous_iff.mpr
  apply continuous_pi
  intro x
  change Continuous (fun V : ValuationSubring K => membership V (f x))
  exact (continuous_apply (f x)).comp isEmbedding_membership.continuous

theorem isClopen_mem (x : K) : IsClopen {V : ValuationSubring K | x ∈ V} := by
  simpa only [Set.preimage, Set.mem_singleton_iff, Function.comp_def,
    membership_eq_true] using
    (isClopen_discrete ({true} : Set Bool)).preimage
      ((continuous_apply x).comp isEmbedding_membership.continuous)

theorem isClopen_not_mem (x : K) : IsClopen {V : ValuationSubring K | x ∉ V} :=
  (isClopen_mem x).compl

/-- Positive additive value, expressed intrinsically as maximal-ideal membership. -/
theorem isClopen_nonunits (x : K) :
    IsClopen {V : ValuationSubring K | x ∈ V.nonunits} := by
  by_cases hx : x = 0
  · simpa [hx] using (isClopen_univ : IsClopen (Set.univ : Set (ValuationSubring K)))
  · simpa only [ValuationSubring.mem_nonunits_iff_or, hx, false_or] using
      isClopen_not_mem x⁻¹

theorem isCompact_nonunits (x : K) :
    IsCompact {V : ValuationSubring K | x ∈ V.nonunits} :=
  (isClopen_nonunits x).isClosed.isCompact

theorem isCompact_extensionFiber (f : F →+* K) (V : ValuationSubring F) :
    IsCompact {W : ValuationSubring K | W.comap f = V} :=
  (isClosed_singleton.preimage (continuous_comap f)).isCompact

/-- Actual prolongations of a named embedded valuation ring. -/
abbrev Prolongations (f : F →+* K) (V : ValuationSubring F) :=
  {W : ValuationSubring K // W.comap f = V}

instance (f : F →+* K) (V : ValuationSubring F) : Nonempty (Prolongations f V) :=
  let ⟨W, hW⟩ := ValuationProlongation.exists_prolongation f V
  ⟨⟨W, hW⟩⟩

scoped instance (f : F →+* K) (V : ValuationSubring F) :
    CompactSpace (Prolongations f V) :=
  isCompact_iff_compactSpace.mp (isCompact_extensionFiber f V)

/-- Patch convergence eventually preserves each positive membership test. -/
theorem eventually_mem {I : Type w} {l : Filter I} {A : I → ValuationSubring K}
    {V : ValuationSubring K} (hA : Tendsto A l (𝓝 V)) {x : K} (hx : x ∈ V) :
    ∀ᶠ i in l, x ∈ A i :=
  hA.eventually ((isClopen_mem x).isOpen.mem_nhds hx)

theorem eventually_not_mem {I : Type w} {l : Filter I} {A : I → ValuationSubring K}
    {V : ValuationSubring K} (hA : Tendsto A l (𝓝 V)) {x : K} (hx : x ∉ V) :
    ∀ᶠ i in l, x ∉ A i :=
  hA.eventually ((isClopen_not_mem x).isOpen.mem_nhds hx)

theorem eventually_nonunits {I : Type w} {l : Filter I} {A : I → ValuationSubring K}
    {V : ValuationSubring K} (hA : Tendsto A l (𝓝 V)) {x : K}
    (hx : x ∈ V.nonunits) : ∀ᶠ i in l, x ∈ (A i).nonunits :=
  hA.eventually ((isClopen_nonunits x).isOpen.mem_nhds hx)

/-- Patch convergence eventually preserves unit value for a fixed element. -/
theorem eventually_valuation_eq_one {I : Type w} {l : Filter I}
    {A : I → ValuationSubring K} {V : ValuationSubring K}
    (hA : Tendsto A l (𝓝 V)) {x : K} (hx : V.valuation x = 1) :
    ∀ᶠ i in l, (A i).valuation x = 1 := by
  have hx0 : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hmem : x ∈ V := (V.valuation_le_one_iff x).mp hx.le
  have hinv : x⁻¹ ∈ V := (V.valuation_le_one_iff x⁻¹).mp
    ((V.valuation.val_eq_one_iff).mp hx).le
  apply ((eventually_mem hA hmem).and (eventually_mem hA hinv)).mono
  intro i hi
  exact le_antisymm ((A i).valuation_le_one_iff x |>.mpr hi.1)
    (((A i).valuation.one_le_val_iff hx0).mpr
      ((A i).valuation_le_one_iff x⁻¹ |>.mpr hi.2))

/-- An infinite set inside a closed locus supplies a convergent sequence of
distinct actual rings, whose limit remains in that locus. -/
theorem exists_injective_tendsto_of_infinite_subset [Countable K]
    {X C : Set (ValuationSubring K)} (hX : X.Infinite) (hC : IsClosed C)
    (hXC : X ⊆ C) :
    ∃ V ∈ C, ∃ A : ℕ → ValuationSubring K,
      Function.Injective A ∧ (∀ n, A n ∈ X) ∧ Tendsto A atTop (𝓝 V) := by
  let e : ℕ ↪ X := hX.natEmbedding X
  let a : ℕ → ValuationSubring K := fun n => e n
  obtain ⟨V, hV, φ, hφ, hlim⟩ := hC.isCompact.tendsto_subseq
    (x := a) (fun n => hXC (e n).property)
  refine ⟨V, hV, a ∘ φ, ?_, fun n => (e (φ n)).property, hlim⟩
  exact (Subtype.val_injective.comp e.injective).comp hφ.injective

/-- The sequence of distinct rings can additionally be chosen to omit its
limit, even when that limit belongs to the infinite source set. -/
theorem exists_injective_tendsto_ne_of_infinite_subset [Countable K]
    {X C : Set (ValuationSubring K)} (hX : X.Infinite) (hC : IsClosed C)
    (hXC : X ⊆ C) :
    ∃ V ∈ C, ∃ A : ℕ → ValuationSubring K,
      Function.Injective A ∧ (∀ n, A n ∈ X) ∧ (∀ n, A n ≠ V) ∧
        Tendsto A atTop (𝓝 V) := by
  obtain ⟨V, hV, A, hA, hAX, hlim⟩ :=
    exists_injective_tendsto_of_infinite_subset hX hC hXC
  by_cases hex : ∃ n, A n = V
  · obtain ⟨n, hn⟩ := hex
    refine ⟨V, hV, fun k => A (k + (n + 1)), ?_,
      fun k => hAX (k + (n + 1)), ?_, ?_⟩
    · exact hA.comp (fun _ _ h => Nat.add_right_cancel h)
    · intro k hk
      have heq := hA (hk.trans hn.symm)
      omega
    · exact hlim.comp (tendsto_add_atTop_nat (n + 1))
  · exact ⟨V, hV, A, hA, hAX, fun n hn => hex ⟨n, hn⟩, hlim⟩

end
end HereditaryAtomicity.ValuationPatch
