import HereditaryAtomicity.Basic
import HereditaryAtomicity.ValuationFan
import HereditaryAtomicity.ValuationPatch
import HereditaryAtomicity.PositiveCenter
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Fintype.Basic

/-!
# Finite outside support from a convergent valuation fan

The compactness argument concerns actual embedded valuation rings. Its finite
approximation input is explicit and states a simultaneous ambient-unit
uniformizer construction, never an assumed finiteness conclusion.
-/

open Set Filter
open scoped Topology HereditaryAtomicity.ValuationPatch

namespace HereditaryAtomicity

variable {K : Type*} [Field K]

/-- Finite approximation by ambient units: at one outside ring the unit is a
uniformizer, and at every finitely prescribed other ring it has value one.
The division clause is the uniformizer property in the common field. -/
def HasFiniteOutsideUnitApproximation (D : Subring K) : Prop :=
  ∀ A : ValuationSubring K, ¬ D ≤ A.toSubring →
    ∀ T : Finset (ValuationSubring K), A ∉ T →
      ∃ u : Dˣ, ((u : D) : K) ∈ A.nonunits ∧
        (∀ y : K, y ∈ A.nonunits → y / ((u : D) : K) ∈ A) ∧
        ∀ B ∈ T, B.valuation ((u : D) : K) = 1

/-- A uniformizer divides every maximal-ideal element in a DVR, with quotient
belonging to the actual embedded ring. -/
theorem div_mem_of_irreducible (A : ValuationSubring K)
    [IsDiscreteValuationRing A] {p : A} (hp : Irreducible p)
    {y : K} (hy : y ∈ A.nonunits) : y / (p : K) ∈ A := by
  let yA : A := ⟨y, A.nonunits_subset hy⟩
  have hyI : yA ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.mp hy
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hyI
  obtain ⟨b, hb⟩ := hyI
  have hp0 : (p : K) ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  have heq : y / (p : K) = (b : K) := by
    apply (div_eq_iff hp0).mpr
    have hh : y = (p : K) * (b : K) := congrArg Subtype.val hb
    simpa only [mul_comm] using hh
  rw [heq]
  exact b.property

/-- Given a convergent injective sequence and finite unit approximation, pass to
a subsequence with private-zero ambient units. A fixed positive limit element
can be retained in every ring of that subsequence. -/
theorem exists_fanUnitData
    {D : Subring K} (happrox : HasFiniteOutsideUnitApproximation D)
    {V : ValuationSubring K} {A : ℕ → ValuationSubring K}
    (hinj : Function.Injective A) (hout : ∀ n, ¬ D ≤ (A n).toSubring)
    (hlim : Tendsto A atTop (𝓝 V)) {h : K} (hh : h ∈ V.nonunits) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, h ∈ (A (φ n)).nonunits) ∧
      Nonempty (FanUnitData D V (A ∘ φ)) := by
  classical
  let P : ℕ × Dˣ → Prop := fun q =>
    h ∈ (A q.1).nonunits ∧ ((q.2 : D) : K) ∈ (A q.1).nonunits ∧
      (∀ y : K, y ∈ (A q.1).nonunits → y / ((q.2 : D) : K) ∈ A q.1) ∧
      V.valuation ((q.2 : D) : K) = 1
  let r : (ℕ × Dˣ) → (ℕ × Dˣ) → Prop := fun q t =>
    q.1 < t.1 ∧ (A q.1).valuation ((t.2 : D) : K) = 1 ∧
      (A t.1).valuation ((q.2 : D) : K) = 1
  have hstep : ∀ s : Finset (ℕ × Dˣ), (∀ q ∈ s, P q) →
      ∃ t, P t ∧ ∀ q ∈ s, r q t := by
    intro s hs
    have hev : ∀ᶠ j in atTop, ∀ q ∈ s,
        q.1 < j ∧ (A j).valuation ((q.2 : D) : K) = 1 := by
      apply (Filter.eventually_all_finset s).mpr
      intro q hq
      exact (eventually_gt_atTop q.1).and
        (ValuationPatch.eventually_valuation_eq_one hlim (hs q hq).2.2.2)
    have hne : ∀ᶠ j in atTop, A j ≠ V := by
      by_cases hex : ∃ k, A k = V
      · obtain ⟨k, hk⟩ := hex
        exact (eventually_ne_atTop k).mono fun j hj hjV => hj (hinj (hjV.trans hk.symm))
      · exact Eventually.of_forall fun j hj => hex ⟨j, hj⟩
    obtain ⟨j, hj, hjV, hjh⟩ :=
      (hev.and (hne.and (ValuationPatch.eventually_nonunits hlim hh))).exists
    let T : Finset (ValuationSubring K) := insert V (s.image fun q => A q.1)
    have hjT : A j ∉ T := by
      simp only [T, Finset.mem_insert, Finset.mem_image, not_or, not_exists]
      refine ⟨hjV, ?_⟩
      rintro q ⟨hq, hqj⟩
      exact (Nat.ne_of_lt (hj q hq).1) (hinj hqj)
    obtain ⟨u, hu, hdiv, hvals⟩ := happrox (A j) (hout j) T hjT
    refine ⟨(j, u), ⟨hjh, hu, hdiv, hvals V (Finset.mem_insert_self ..)⟩, ?_⟩
    intro q hq
    refine ⟨(hj q hq).1, ?_, (hj q hq).2⟩
    exact hvals (A q.1) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
  obtain ⟨f, hf, hfr⟩ := exists_seq_of_forall_finset_exists P r hstep
  refine ⟨fun n => (f n).1, fun m n hmn => (hfr m n hmn).1,
    fun n => (hf n).1, ⟨?_⟩⟩
  exact {
    unit := fun n => (f n).2
    own_nonunit := fun n => (hf n).2.1
    own_division := fun n => (hf n).2.2.1
    limit_value := fun n => (hf n).2.2.2
    other_value := fun n i hi => by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact (hfr i n hlt).2.1
      · exact (hfr n i hgt).2.2 }

/-- In a countable field, finite outside unit approximation and positive centers
force the positive support of a fixed element to be finite. This is an actual
finiteness conclusion; no finite-support premise is used. -/
theorem finite_outside_nonunits_of_positive_centers [Countable K]
    {D : Subring K} (hHA : Factorization.IsHereditarilyAtomic D)
    (happrox : HasFiniteOutsideUnitApproximation D) (z : K)
    (hcenter : ∀ V : ValuationSubring K, z ∈ V.nonunits →
      ∃ h : K, h ≠ 0 ∧ h ∈ D ∧ h ∈ V.nonunits) :
    Set.Finite {W : ValuationSubring K | ¬ D ≤ W.toSubring ∧ z ∈ W.nonunits} := by
  classical
  by_contra hfinite
  obtain ⟨V, hzV, A, hinj, hA, hlim⟩ :=
    ValuationPatch.exists_injective_tendsto_of_infinite_subset
      (show Set.Infinite {W : ValuationSubring K | ¬ D ≤ W.toSubring ∧
        z ∈ W.nonunits} from hfinite)
      (ValuationPatch.isClopen_nonunits z).isClosed (fun _ h => h.2)
  obtain ⟨h, hh0, hhD, hhV⟩ := hcenter V hzV
  obtain ⟨φ, hφ, hhW, ⟨data⟩⟩ := exists_fanUnitData happrox hinj
    (fun n => (hA n).1) hlim hhV
  have hlimW : Tendsto (A ∘ φ) atTop (𝓝 V) := hlim.comp hφ.tendsto_atTop
  have hI : fanIdeal D V (A ∘ φ) ≠ ⊥ :=
    fanIdeal_ne_bot hh0 hhD hhV (fun n => (A (φ n)).nonunits_subset (hhW n))
  have hnonatomic := not_isAtomicDomain_fanSubring data hI (fun y _ hy =>
    (ValuationPatch.eventually_nonunits hlimW (mem_fanIdeal.mp hy)).exists)
  apply hnonatomic
  exact (of_subring_le (fun _ hy => (mem_fanSubring.mp hy).1) hHA).isAtomicDomain

/-- For a full fraction field, finite outside unit approximation supplies the
outside centers and the positive-numerator argument supplies centered ones.
The nonzero hypothesis excludes the all-valuation support of zero. -/
theorem finite_outside_nonunits [Countable K] {D : Subring K} [IsFractionRing D K]
    (hHA : Factorization.IsHereditarilyAtomic D)
    (happrox : HasFiniteOutsideUnitApproximation D) {z : K} (hz : z ≠ 0) :
    Set.Finite {W : ValuationSubring K | ¬ D ≤ W.toSubring ∧ z ∈ W.nonunits} := by
  apply finite_outside_nonunits_of_positive_centers hHA happrox z
  intro V hzV
  by_cases hDV : D ≤ V.toSubring
  · exact exists_nonzero_positive_of_centered D V hDV z hz hzV
  · obtain ⟨u, hu, _⟩ := happrox V hDV ∅ (Finset.notMem_empty V)
    refine ⟨((u : D) : K), ?_, (u : D).property, hu⟩
    exact (Units.map D.subtype.toMonoidHom u).ne_zero

/-- Every nonzero element has finite full value support among outside rings:
both positive and negative values are included. -/
theorem finite_outside_value_ne_one [Countable K] {D : Subring K} [IsFractionRing D K]
    (hHA : Factorization.IsHereditarilyAtomic D)
    (happrox : HasFiniteOutsideUnitApproximation D) {z : K} (hz : z ≠ 0) :
    Set.Finite {W : ValuationSubring K | ¬ D ≤ W.toSubring ∧ W.valuation z ≠ 1} := by
  apply ((finite_outside_nonunits hHA happrox hz).union
    (finite_outside_nonunits hHA happrox (inv_ne_zero hz))).subset
  intro W hW
  rcases lt_or_gt_of_ne hW.2 with hlt | hgt
  · exact Or.inl ⟨hW.1, W.mem_nonunits_iff.mpr hlt⟩
  · exact Or.inr ⟨hW.1, W.mem_nonunits_iff.mpr ((W.valuation.one_lt_val_iff hz).mp hgt)⟩

/-- Each nontrivial base valuation has only finitely many outside prolongations.
The fiber consists of literal valuation rings with the stated actual comap. -/
theorem finite_outside_extensionFiber [Countable K] {D : Subring K} [IsFractionRing D K]
    (hHA : Factorization.IsHereditarilyAtomic D)
    (happrox : HasFiniteOutsideUnitApproximation D)
    {F : Type*} [Field F] (f : F →+* K) (V : ValuationSubring F) (hV : V ≠ ⊤) :
    Set.Finite {W : ValuationSubring K | ¬ D ≤ W.toSubring ∧ W.comap f = V} := by
  classical
  have hex : ∃ x : F, x ∉ V := by
    by_contra! h
    apply hV
    ext x
    exact iff_of_true (h x) (show x ∈ (⊤ : ValuationSubring F) from trivial)
  obtain ⟨x, hx⟩ := hex
  have hx0 : x ≠ 0 := fun hzero => hx (hzero ▸ V.zero_mem)
  have hfx0 : f x ≠ 0 := (map_ne_zero f).mpr hx0
  apply (finite_outside_nonunits hHA happrox (inv_ne_zero hfx0)).subset
  intro W hW
  refine ⟨hW.1, W.inv_mem_nonunits_iff.mpr (Or.inr ?_)⟩
  intro hfx
  apply hx
  rw [← hW.2]
  exact hfx

end HereditaryAtomicity
