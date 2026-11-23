import UnconditionalCounterexample.Variations.FrozenSites
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# A fair freezing and split-task calendar

The initial round takes both endpoints. Subsequent rounds cover every monic
irreducible, and every round may also handle the finitely many horizontal
factors of its split element or other named polynomials ahead of their turns.
Already frozen factors and the literal raw prefix are removed before calibration.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.FreezingCalendar

open Polynomial GuardSupport RecursivePrefix Univariate UniqueFactorizationMonoid

abbrev Horizontal := {f : ℚ[X] // f.Monic ∧ Irreducible f}

def zeroPoint : Horizontal := ⟨X, monic_X, irreducible_X⟩

def onePoint : Horizontal := ⟨X-C 1, monic_X_sub_C _, irreducible_X_sub_C _⟩

/-- Supply the primitive integral representative required by the simple-root
calibration at a monic rational horizontal factor. -/
theorem primitive_representative (f : Horizontal) :
    ∃ (F : ℤ[X]) (q : ℚ), F.IsPrimitive ∧ Irreducible F ∧ F.natDegree ≠ 0 ∧
      q ≠ 0 ∧ F.map (Int.castRingHom ℚ) = C q * f.val := by
  obtain ⟨d, V, hd, hV, he⟩ := exists_integer_multiple f.val f.property.2.ne_zero
  let φ := Int.castRingHom ℚ
  have hc : (V.content : ℚ) ≠ 0 := by exact_mod_cast (content_eq_zero_iff.not.mpr hV)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hm : C (V.content : ℚ) * V.primPart.map φ = C (d : ℚ) * f.val := by
    have hv := congrArg (Polynomial.map φ) V.eq_C_content_mul_primPart
    rw [Polynomial.map_mul, map_C] at hv
    exact hv.symm.trans he
  let q : ℚ := (V.content : ℚ)⁻¹ * d
  have hq : q ≠ 0 := mul_ne_zero (inv_ne_zero hc) hd'
  have heq : V.primPart.map φ = C q * f.val := calc
    V.primPart.map φ = C (V.content : ℚ)⁻¹ * (C (V.content : ℚ) * V.primPart.map φ) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    _ = C q * f.val := by rw [hm, ← mul_assoc, ← map_mul]
  have hi : Irreducible V.primPart := by
    apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast V.isPrimitive_primPart).mpr
    rw [heq, mul_comm]
    exact (irreducible_mul_isUnit (isUnit_C.mpr hq.isUnit)).mpr f.property.2
  have hdeg : V.primPart.natDegree ≠ 0 := by
    intro hz
    have h0 : (V.primPart.map φ).natDegree = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact natDegree_map_le.trans hz.le
    rw [heq, natDegree_C_mul hq] at h0
    have heC := eq_C_of_natDegree_eq_zero h0
    have hz1 : f.val.coeff 0 = 1 := by simpa [leadingCoeff, h0] using f.property.1.leadingCoeff
    have h1 : f.val = 1 := heC.trans (by rw [hz1, C_1])
    exact f.property.2.not_isUnit (h1 ▸ isUnit_one)
  exact ⟨V.primPart, q, V.isPrimitive_primPart, hi, hdeg, hq, heq⟩

private theorem exists_enumeration : ∃ h : ℕ → Horizontal, Function.Surjective h := by
  let _ : Countable ℚ[X] := Polynomial.toFinsuppIso ℚ |>.injective.countable
  let _ : Nonempty Horizontal := ⟨zeroPoint⟩
  exact exists_surjective_nat Horizontal

def enumeration : ℕ → Horizontal := exists_enumeration.choose

theorem enumeration_surjective : Function.Surjective enumeration := exists_enumeration.choose_spec

/-- A fixed enumeration of pairs schedules every rational-function element
and every positive modulus. Repetitions are harmless. -/
abbrev SplitPair := RatFunc ℚ × {m : ℕ // 0 < m}

private theorem exists_split_enumeration : ∃ h : ℕ → SplitPair, Function.Surjective h := by
  let _ : Countable ℚ[X] := (Polynomial.toFinsuppIso ℚ).injective.countable
  let _ : Countable (RatFunc ℚ) :=
    (show Function.Injective (fun x : RatFunc ℚ => (x.num,x.denom)) from fun x y h => by
      have hn : x.num = y.num := congrArg Prod.fst h
      have hd : x.denom = y.denom := congrArg Prod.snd h
      exact x.num_div_denom.symm.trans (hn ▸ hd ▸ y.num_div_denom)).countable
  let _ : Nonempty SplitPair := ⟨(1,⟨1,by decide⟩)⟩
  exact exists_surjective_nat SplitPair

def splitAt : ℕ → SplitPair := exists_split_enumeration.choose

theorem splitAt_surjective : Function.Surjective splitAt := exists_split_enumeration.choose_spec

def factors (x : RatFunc ℚ) : Finset ℚ[X] :=
  (normalizedFactors x.num).toFinset ∪ (normalizedFactors x.denom).toFinset

theorem mem_factors_of_dvd {f : ℚ[X]} (hf : f.Monic) (hirr : Irreducible f)
    {x : RatFunc ℚ} (hx : x ≠ 0) (hd : f ∣ x.num ∨ f ∣ x.denom) : f ∈ factors x := by
  rcases hd with hn | hd
  · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_normalizedFactors_iff (RatFunc.num_ne_zero hx)).mpr ⟨hirr, hf, hn⟩))
  · exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
      ((Polynomial.mem_normalizedFactors_iff x.denom_ne_zero).mpr ⟨hirr, hf, hd⟩))

def named : ℕ → Finset ℚ[X]
  | 0 => {zeroPoint.val, onePoint.val}
  | r+1 => {(enumeration r).val}

theorem eventually_named (f : Horizontal) : ∃ r, f.val ∈ named r := by
  obtain ⟨n, hn⟩ := enumeration_surjective f
  exact ⟨n+1, by simp [named, hn]⟩

def candidates (round : ℕ) (extras : Finset ℚ[X]) : Finset ℚ[X] :=
  named round ∪ factors (splitAt round).1 ∪ extras

def pending {n : ℕ} (P : Prefix n) (known : Finset ℚ[X]) (candidates : Finset ℚ[X]) : Finset ℚ[X] :=
  candidates.filter fun f => f ∉ known ∧ ∀ j : Fin n, P.raw j ≠ f

theorem pending_fresh {n : ℕ} (P : Prefix n) (known candidates : Finset ℚ[X])
    (f : ℚ[X]) (h : f ∈ pending P known candidates) : ∀ j : Fin n, P.raw j ≠ f :=
  (Finset.mem_filter.mp h).2.2

theorem candidate_trichotomy {n : ℕ} (P : Prefix n) (known candidates : Finset ℚ[X])
    {f : ℚ[X]} (h : f ∈ candidates) :
    f ∈ known ∨ (∃ j : Fin n, P.raw j = f) ∨ f ∈ pending P known candidates := by
  classical
  by_cases old : f ∈ known
  · exact Or.inl old
  by_cases hr : ∃ j : Fin n, P.raw j = f
  · exact Or.inr (Or.inl hr)
  exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨h, old, fun j hj => hr ⟨j,hj⟩⟩))

theorem initially_both (extras : Finset ℚ[X]) :
    zeroPoint.val ∈ pending empty ∅ (candidates 0 extras) ∧
    onePoint.val ∈ pending empty ∅ (candidates 0 extras) := by
  simp [pending, candidates, named]

/-- Each retained horizontal reaches a finite stage, irrespective of any
extra factors frozen early for split tasks. Round starts can be nonconsecutive
raw stages. The old-frozen condition is only persistence of actual requests. -/
theorem all_raw_or_requested (R : Requirements) (start : ℕ → ℕ)
    (known extra req : ℕ → Finset ℚ[X])
    (hreq : ∀ r, pending ((chain R).approx (start r)) (known r) (candidates r (extra r)) ⊆ req r)
    (hknown : ∀ r f, f ∈ known r → ∃ k, f ∈ req k) (f : Horizontal) :
    (∃ j, (chain R).raw j = f.val) ∨ ∃ r, f.val ∈ req r := by
  obtain ⟨r, hr⟩ := eventually_named f
  have hc : f.val ∈ candidates r (extra r) :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hr)
  rcases candidate_trichotomy ((chain R).approx (start r)) (known r) _ hc with h | ⟨j,hj⟩ | h
  · exact Or.inr (hknown r _ h)
  · exact Or.inl ⟨j.val, ((chain R).raw_agrees (start r) j).symm.trans hj⟩
  · exact Or.inr ⟨r, hreq r h⟩

/-- At the round naming a split pair all of its nonraw horizontal factors
have already been frozen or are ready for calibration in that round. -/
theorem split_factors_requested {x : RatFunc ℚ} (hx : x ≠ 0) (m : ℕ) (hm : 0 < m) :
    ∃ r, splitAt r = (x,⟨m,hm⟩) ∧
      ∀ {n : ℕ} (P : Prefix n) (known extras : Finset ℚ[X]) (f : Horizontal),
        f.val ∣ x.num ∨ f.val ∣ x.denom →
        f.val ∈ known ∨ (∃ j : Fin n, P.raw j = f.val) ∨
          f.val ∈ pending P known (candidates r extras) := by
  obtain ⟨r, hr⟩ := splitAt_surjective (x,⟨m,hm⟩)
  refine ⟨r, hr, ?_⟩
  intro n P known extras f hd
  apply candidate_trichotomy
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [hr]
  exact mem_factors_of_dvd f.property.1 f.property.2 hx hd

end UnconditionalCounterexample.Variations.FreezingCalendar
