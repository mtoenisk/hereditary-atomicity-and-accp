import UnconditionalCounterexample.Variations.PrivateGuardsLive
import UnconditionalCounterexample.Variations.MultivariateSelectionOpen

/-!
# A chronological main stage with all earlier private pairs

The degree is chosen after taking the maximum of the local thresholds.
The selector then realizes the coefficient neighborhoods simultaneously at
regular primes and at both members of every private pair. Its auxiliary
prime and all processed primes are reserved for the following puncture.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial Filter GuardSupport MultivariateSelection MultivariateInfinity
open scoped Topology

variable {r n : ℕ} {M : ℕ → Type*}

abbrev LocalPoly (r : ℕ) (p : PrimeIndex) := MvPolynomial (Fin (r+1)) ℚ_[p.val]

private abbrev lowerMap (p : PrimeIndex) (f : Poly r) : LocalPoly r p :=
  MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) f

/-- An open coefficient target for the lower part at a single processed prime. -/
structure OpenLower (r d : ℕ) (p : PrimeIndex) where
  target : LocalPoly r p
  lower_lt : target.totalDegree < d
  neighborhood : Set (((Fin (r+1)) →₀ ℕ) → ℚ_[p.val])
  mem_nhds : neighborhood ∈ 𝓝 (fun m => target.coeff m)

/-- The finite local tests at a single old private pair. -/
structure PairTests (s : Round r n (M n)) where
  target : Bool → ℚ_[s.prime.val]
  target_unit : ∀ b, ‖target b‖ = 1
  idealGenerator : LocalPoly r s.prime
  vanishes : ∀ b, aeval (s.pair.point b) idealGenerator = 0
  words : ℕ
  denominator : Fin words → LocalPoly r s.prime
  exponent : Fin words → ℕ
  positive : ∀ j, 0 < exponent j
  avoids : ∀ b j, aeval (s.pair.point b) (denominator j) ≠ 0
  observations : ℕ
  observation : Fin observations → LocalPoly r s.prime →ₗ[ℚ_[s.prime.val]] ℚ_[s.prime.val]
  precision : ℝ
  precision_pos : 0 < precision
  minScale : ℕ

namespace PairTests
variable {s : Round r n (M n)} (U : PairTests s)

def Holds (D : Poly r) (F : LocalPoly r s.prime) : Prop :=
  (∀ b, let z := aeval (s.pair.point b) F / aeval (s.pair.point b) D
        ‖z‖ = 1 ∧ ‖z - U.target b‖ < U.precision) ∧
  ∃ N ≥ U.minScale, (∀ l, ‖(s.prime.val : ℚ_[s.prime.val]) ^ N * U.observation l F -
      U.observation l U.idealGenerator‖ < U.precision) ∧
    ∀ b j, ∃ α : ℚ_[s.prime.val], α ≠ 0 ∧ ‖α⁻¹‖ < U.precision ∧
      ‖α⁻¹ • residueWordGradient (s.pair.point b) F (U.denominator j) (U.exponent j) -
        (fun l => aeval (s.pair.point b) (pderiv l U.idealGenerator))‖ < U.precision

theorem open_lower (D : Poly r) (hD : D ≠ 0) :
    ∃ bound : ℕ, ∀ d > bound, ∀ lead : LocalPoly r s.prime,
      ∃ L : OpenLower r d s.prime, ∀ f : LocalPoly r s.prime, f.totalDegree < d →
        (fun m => f.coeff m) ∈ L.neighborhood → U.Holds D (lead + f) := by
  obtain ⟨b,hb⟩ := s.pair.main_neighborhood (κ := Fin U.words) (η := Fin U.observations)
    U.idealGenerator U.vanishes
  refine ⟨b,fun d hd lead ↦ ?_⟩
  obtain ⟨N,hN,f,hf,S,hS,h⟩ := hb d hd lead D hD U.target U.target_unit U.denominator U.exponent
    U.positive U.avoids U.observation U.precision U.precision_pos U.minScale
  refine ⟨⟨f,hf,S,hS⟩,fun g hg hgS ↦ ?_⟩
  have hh := h g hg hgS
  exact ⟨hh.1,N,hN,hh.2⟩

end PairTests

variable {k : Type*} [Field k] [CharZero k]

/-- Choose the next main polynomial under arbitrary regular-prime coefficient
conditions, bounded-degree private-pair conditions, and finite geometric tests. -/
theorem exists_main_stage (h : History r M n) (hinj : Function.Injective (fun j => (h j).prime))
    (memory : M n) (reg blocked : Finset PrimeIndex) (separate : ∀ j, (h j).prime ∉ reg)
    (degreeFloor : ℕ) (regular : ∀ d > degreeFloor, ∀ v : reg, OpenLower r d v.val)
    (pairTests : (j : Fin n) → PairTests (h j))
    (c : Fin (r+1) → ℚ) (T : Finset (MultivariateStage.Test k (Fin (r+1)))) (hT : ∀ t ∈ T, t.Valid) :
    ∃ x : MainChoice r n (M n), degreeFloor < x.entry.degree ∧ x.entry.memory = memory ∧
      (x.entry.raw n).totalDegree = x.entry.degree ∧ eval c (x.entry.raw n) ≠ 0 ∧
      UnitsAt h (x.entry.raw n) ∧
      (∀ j, (pairTests j).Holds (oldDenominator h) (lowerMap (h j).prime (x.entry.raw n))) ∧
      (∀ v : reg, ∃ hd : degreeFloor < x.entry.degree,
        (fun m => ((x.entry.lower.coeff m : ℚ) : ℚ_[v.val.val])) ∈
          (regular x.entry.degree hd v).neighborhood) ∧
      (∀ t ∈ T, t.Holds (MvPolynomial.map (algebraMap ℚ k) (x.entry.raw n))) ∧
      (∀ j, (h j).prime ∈ x.reserved) ∧ reg ⊆ x.reserved ∧ blocked ⊆ x.reserved ∧
      (∃ ell ∈ x.reserved, ell ∉ reg ∧ (∀ j, ell ≠ (h j).prime) ∧
        ∀ m, HasAuxiliaryResidue ell.val (x.entry.lower.coeff m)
          (if m = 0 then (ell.val : ZMod (ell.val^2)) else 0)) ∧
      ∀ m p, p.Prime → p ∣ (x.entry.lower.coeff m).den → (∃ v : reg, p = v.val.val) ∨
        ∃ j, p = (h j).prime.val := by
  classical
  choose b hb using fun j ↦ (pairTests j).open_lower (oldDenominator h) (oldDenominator_ne_zero h)
  let d := max 1 (max degreeFloor (Finset.univ.sup b)) + 1
  have hd : 2 ≤ d := Nat.succ_le_succ (Nat.le_max_left ..)
  have hfloor : degreeFloor < d := Nat.lt_succ_of_le ((Nat.le_max_left ..).trans (Nat.le_max_right ..))
  have hb' (j : Fin n) : b j < d := Nat.lt_succ_of_le (((Finset.le_sup (f := b) (Finset.mem_univ j)).trans
    (Nat.le_max_right ..)).trans (Nat.le_max_right ..))
  let l := vandermondeForm (k := ℚ) (r+1) n
  choose V hV using fun j ↦ hb j d (hb' j) (lowerMap (h j).prime (l ^ d))
  let I := Sum reg (Fin n)
  let prime : I → PrimeIndex := Sum.elim Subtype.val (fun j ↦ (h j).prime)
  have hpi : Function.Injective prime := by
    rintro (i|i) (j|j) he
    · exact congrArg Sum.inl (Subtype.ext he)
    · change i.val = (h j).prime at he
      exact (separate j (he ▸ i.property)).elim
    · change (h i).prime = j.val at he
      exact (separate i (he.symm ▸ j.property)).elim
    · exact congrArg Sum.inr (hinj he)
  let L : (i : I) → OpenLower r d (prime i) := Sum.rec (fun v ↦ regular d hfloor v) V
  let used := blocked ∪ Finset.univ.image prime
  obtain ⟨ell, _, hell⟩ := GuardStages.exists_fresh_prime used n
  have hpr (i : I) : prime i ∈ used :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let added := MultivariateStage.Test.point ((algebraMap ℚ k) ∘ c)
  let tests := insert added T
  have valid (t) (ht : t ∈ tests) : t.Valid := (Finset.mem_insert.mp ht).elim
    (fun he ↦ he ▸ (show added.Valid from trivial)) (hT t)
  obtain ⟨q,hq,hi,hdeg,hs,hU,hres,hGeo⟩ := exists_vandermonde_stage r n (fun i ↦ (prime i).val)
    (Subtype.val_injective.comp hpi) ell.val (fun i he ↦ hell ((Subtype.ext he : prime i = ell) ▸ hpr i))
    d hd (fun i ↦ (L i).target) (fun i ↦ (L i).lower_lt) (fun i ↦ (L i).neighborhood)
    (fun i ↦ (L i).mem_nhds) tests valid
  let x : MainChoice r n (M n) := ⟨⟨d,q,hq,memory⟩,hi,insert ell used⟩
  have hpairs (j : Fin n) : (pairTests j).Holds (oldDenominator h) (lowerMap (h j).prime (x.entry.raw n)) := by
    change (pairTests j).Holds _ (MvPolynomial.map _ (l^d + q))
    rw [map_add]
    apply hV j (lowerMap (h j).prime q)
    · exact (Finset.sup_mono (f := fun e => e.sum fun (_ : Fin (r+1)) (v : ℕ) => v)
        (support_map_subset (algebraMap ℚ ℚ_[(h j).prime.val]) q)).trans_lt hq
    · have hh : (fun m => ((q.coeff m : ℚ) : ℚ_[(h j).prime.val])) ∈ (V j).neighborhood := hU (Sum.inr j)
      simpa only [lowerMap, coeff_map, eq_ratCast] using hh
  refine ⟨x,hfloor,rfl,hdeg,?_,?_,hpairs,?_,?_,?_,?_,?_,?_,?_⟩
  · have havoids := hGeo added (Finset.mem_insert_self _ _)
    change eval ((algebraMap ℚ k) ∘ c) (MvPolynomial.map (algebraMap ℚ k) (x.entry.raw n)) ≠ 0 at havoids
    rw [← map_eval] at havoids
    exact fun h ↦ havoids (by rw [h, map_zero])
  · intro j t
    simpa only [lowerMap, aeval_map_algebraMap] using ((hpairs j).1 t).1
  · intro v; exact ⟨hfloor,hU (Sum.inl v)⟩
  · exact fun t ht ↦ hGeo t (Finset.mem_insert_of_mem ht)
  · exact fun j ↦ Finset.mem_insert_of_mem (hpr (Sum.inr j))
  · intro v hv; exact Finset.mem_insert_of_mem (hpr (Sum.inl ⟨v,hv⟩))
  · exact (Finset.subset_union_left (s₂ := Finset.univ.image prime)).trans (Finset.subset_insert _ _)
  · refine ⟨ell, Finset.mem_insert_self _ _, ?_, fun j he ↦ hell (he ▸ hpr (Sum.inr j)), hres⟩
    intro he; exact hell (hpr (Sum.inl ⟨ell,he⟩))
  · intro m p hp hpd
    obtain ⟨i,he⟩ := hs m p hp hpd
    cases i with
    | inl v => exact Or.inl ⟨v,he⟩
    | inr j => exact Or.inr ⟨j,he⟩

end UnconditionalCounterexample.Variations.PrivateGuards.Live
