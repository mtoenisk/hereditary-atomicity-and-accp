import Factorization.CommonFactorDescent
import Factorization.WeakACCP
import UnconditionalCounterexample.PaperAtomicity
import UnconditionalCounterexample.PaperChainHeight

/-!
# Simultaneous division at the single centre

Every sufficiently late return atom divides a fixed finite family of elements
of order at least two. A return congruent to one modulo the conductor also
divides the whole family in the original subring.
-/

namespace UnconditionalCounterexample.PaperConstruction

open Filter

private theorem common_late_atom {ι : Type*} (s : Finset ι) (f : ι → domain)
    (hne : ∀ i ∈ s, f i ≠ 0)
    (hhigh : ∀ i ∈ s, 2 ≤ valuationProfiles.value .limit (f i)) :
    ∀ᶠ n in atTop, ∀ i ∈ s, atom n ∣ f i := by
  apply (eventually_all_finset s).mpr
  intro i hi
  exact eventually_atTop.mpr (valuationProfiles.eventually_dvd_of_primaryAtomProfiles
    coordinate_divisibility atom atom_ne_zero atom_limit atom_outside atom_primary
    (hne i hi) (hhigh i hi))

private theorem common_atom_in_subring (T : Subring domain) (m : ℕ) (hm : 0 < m)
    (hc : ∀ z : domain, (m : domain) * z ∈ T) (s : Finset T)
    (hne : ∀ x ∈ s, x ≠ 0)
    (hhigh : ∀ x ∈ s, 2 ≤ valuationProfiles.value .limit (x : domain)) :
    ∃ a : T, valuationProfiles.value .limit (a : domain) = 1 ∧ ∀ x ∈ s, a ∣ x := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (common_late_atom s Subtype.val
    (fun x hx h => hne x hx (Subtype.ext h)) hhigh)
  obtain ⟨n, hn, hreturn⟩ := late_return m hm N
  have ha := mem_subring_of_conductor_dvd_sub_one T (m : domain) hc hreturn
  refine ⟨⟨atom n, ha⟩, atom_limit n, ?_⟩
  intro x hx
  obtain ⟨b, hb⟩ := hN n hn x hx
  have hbT := cofactor_mem_subring_of_conductor T (m : domain) hc (hb ▸ x.property) hreturn
  exact ⟨⟨b, hbT⟩, Subtype.ext hb⟩

/-- In every subring containing an integer conductor, a common divisor of
a finite nonempty family leaves some cofactor of order at most one at zero. -/
theorem exists_common_dvd_low_tOrder_of_conductor (T : Subring domain) (m : ℕ)
    (hm : 0 < m) (hc : ∀ z : domain, (m : domain) * z ∈ T)
    (s : Finset T) (hs : s.Nonempty) (hne : ∀ x ∈ s, x ≠ 0) :
    ∃ d : T, (∀ z ∈ s, d ∣ z) ∧ ∃ x ∈ s, ∃ q : T, x = d * q ∧
      PrimaryStabilization.tOrder ((q : domain) : RatFunc ℚ) ≤ 1 := by
  let ord (x : T) := valuationProfiles.value .limit (x : domain)
  have hmul (a b : T) (ha : a ≠ 0) (hb : b ≠ 0) : ord (a * b) = ord a + ord b :=
    valuationProfiles.value_mul .limit a b (fun h => ha (Subtype.ext h))
      (fun h => hb (Subtype.ext h))
  obtain ⟨d, hd, x, hx, q, hq, hlow⟩ :=
    Factorization.exists_common_dvd_lowOrder ord hmul
      (fun u _ hzero hhigh => common_atom_in_subring T m hm hc u hzero hhigh) s hs hne
  have hq0 : q ≠ 0 := right_ne_zero_of_mul (hq ▸ hne x hx)
  refine ⟨d, hd, x, hx, q, hq, ?_⟩
  rw [← valuationProfiles_limit_cast q (fun h => hq0 (Subtype.ext h))]
  exact_mod_cast hlow

/-- In every unital subring, a common divisor of a finite nonempty family
leaves an original member with a cofactor of bounded decomposition length. -/
theorem exists_common_dvd_bounded_cofactor (T : Subring domain)
    (s : Finset T) (hs : s.Nonempty) (hne : ∀ x ∈ s, x ≠ 0) :
    ∃ d : T, (∀ z ∈ s, d ∣ z) ∧ ∃ x ∈ s, ∃ q : T, x = d * q ∧
      Factorization.HasBoundedFactorizations q := by
  by_cases hBF : Factorization.IsBFDomain T
  · obtain ⟨x, hx⟩ := hs
    exact ⟨1, fun z _ => one_dvd z, x, hx, x, (one_mul x).symm, hBF x (hne x hx)⟩
  obtain ⟨m, hm, hc⟩ := PaperIntegerConductor.exists_integer_conductor T hBF
  obtain ⟨d, hd, x, hx, q, hq, hlow⟩ :=
    exists_common_dvd_low_tOrder_of_conductor T m hm hc s hs hne
  have hq0 : q ≠ 0 := right_ne_zero_of_mul (hq ▸ hne x hx)
  exact ⟨d, hd, x, hx, q, hq, subring_bounded_of_order_le_one T q hq0 hlow⟩

/-- Every unital subring of the original example satisfies weak ACCP. -/
theorem hereditarilyWeakACCP : Factorization.IsHereditarilyWeakACCP domain := by
  intro T
  refine ⟨hereditarilyAtomic T, ?_⟩
  intro s hs hne
  obtain ⟨d, hd, x, hx, q, hq, hbounded⟩ := exists_common_dvd_bounded_cofactor T s hs hne
  exact ⟨d, hd, x, hx, q, hq, hbounded.acc_dvdNotUnit⟩

/-- The original domain satisfies weak ACCP, despite its strict chain at
the square of the parameter. -/
theorem weakACCP : Factorization.IsWeakACCP domain :=
  hereditarilyWeakACCP.isWeakACCP

end UnconditionalCounterexample.PaperConstruction
