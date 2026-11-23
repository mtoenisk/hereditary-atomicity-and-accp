import Factorization.PrincipalIdeals
import Factorization.Descent
import UnconditionalCounterexample.Hierarchy.PrescribedSlices

/-!
# Transfer of ACCP along the inclusion into the localized polynomial ring

Once the images of the chain ratios become units, their partial products
divide the top element. A single ambient unit in the source that is divisible
by all such products supplies a new chain with the same ratios, this time
entirely among elements with unit image.
-/

namespace UnconditionalCounterexample.Hierarchy.Prescribed

open Factorization

variable {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]

/-- ACCP descends if divisors with unit image admit a common multiple of
unit image and every proper division between such elements decreases rank. -/
theorem wfDvdMonoid_of_dominatedUnitDivisors (f : R →+* B) (hf : Function.Injective f)
    (hB : WfDvdMonoid B)
    (dominate : ∀ x : R, x ≠ 0 → ∃ u : R, IsUnit (f u) ∧
      ∀ v : R, v ∣ x → IsUnit (f v) → v ∣ u)
    (rank : (u : R) → IsUnit (f u) → ℕ × ℕ)
    (lower : ∀ (u v a : R) (hu : IsUnit (f u)) (hv : IsUnit (f v)),
      u = v * a → ¬ IsUnit a → Prod.Lex (· < ·) (· < ·) (rank v hv) (rank u hu)) :
    WfDvdMonoid R := by
  classical
  by_contra hbad
  obtain ⟨x, a, hx, ha, hstep⟩ := not_wfDvdMonoid_iff_exists_nonunit_chain.mp hbad
  obtain ⟨N, hN⟩ := eventually_isUnit_ratios_of_wfDvdMonoid hB
    (fun n => f (x n)) (fun n => f (a n))
    (fun n h => hx n (hf (h.trans f.map_zero.symm)))
    (fun n => by simpa only [map_mul] using congrArg f (hstep n))
  obtain ⟨u, hu, hdom⟩ := dominate (x N) (hx N)
  let partialProduct (n : ℕ) := ∏ i ∈ Finset.range n, a (N + i)
  have hsucc (n : ℕ) : partialProduct (n+1) = partialProduct n * a (N+n) := Finset.prod_range_succ ..
  have hunit (n : ℕ) : IsUnit (f (partialProduct n)) := by
    induction n with
    | zero => simp [partialProduct]
    | succ n ih => rw [hsucc, map_mul]; exact ih.mul (hN _ (by omega))
  have hpartialProduct (n : ℕ) : x N = partialProduct n * x (N+n) := by
    induction n with
    | zero => simp [partialProduct]
    | succ n ih =>
      calc
        x N = partialProduct n * x (N+n) := ih
        _ = partialProduct (n+1) * x (N+(n+1)) := by
          rw [hstep (N+n), hsucc, Nat.add_assoc]
          ac_rfl
  choose y hy using fun n => hdom (partialProduct n) ⟨x (N+n), hpartialProduct n⟩ (hunit n)
  have hyunit (n : ℕ) : IsUnit (f (y n)) := by
    have h : IsUnit (f (partialProduct n) * f (y n)) := by rwa [← map_mul, ← hy n]
    exact isUnit_of_mul_isUnit_right h
  have hydesc (n : ℕ) : y n = y (n+1) * a (N+n) := by
    have hn : partialProduct n ≠ 0 := fun h => (hunit n).ne_zero (by rw [h, map_zero])
    apply mul_left_cancel₀ hn
    calc
      partialProduct n * y n = u := (hy n).symm
      _ = partialProduct (n+1) * y (n+1) := hy _
      _ = partialProduct n * (y (n+1) * a (N+n)) := by rw [hsucc]; ac_rfl
  let : WellFounded (Prod.Lex ((· < ·) : ℕ → ℕ → Prop) ((· < ·) : ℕ → ℕ → Prop)) :=
    Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf
  obtain ⟨n, h⟩ := WellFounded.not_rel_apply_succ (r := Prod.Lex (· < ·) (· < ·)) (fun n => rank (y n) (hyunit n))
  exact h (lower _ _ _ (hyunit n) (hyunit _) (hydesc n) (ha _))

/-- The row valuations and total guard order needed for descent from the
localized polynomial ring. Only elements with unit image require a
separated-coordinate presentation of their row valuations. -/
structure ProfileOrders (m : ℕ → ℕ) (f : R →+* B) where
  row : R → RowPoint m → ℕ
  guards : R → ℕ
  row_mul : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∀ x, row (a*b) x = row a x + row b x
  guards_mul : ∀ a b : R, a ≠ 0 → b ≠ 0 → guards (a*b) = guards a + guards b
  profile : ∀ a : R, IsUnit (f a) → ∃ q : Profile m, ∀ x, q.eval x = row a x
  unit_of_zero : ∀ a : R, IsUnit (f a) → guards a = 0 → (∀ x, row a x = 0) → IsUnit a

variable {m : ℕ → ℕ} {f : R →+* B}

/-- The positive row profiles supply the lexicographic rank on elements
with unit image. -/
theorem ProfileOrders.wfDvdMonoid (O : ProfileOrders m f) (hf : Function.Injective f)
    (hB : WfDvdMonoid B) (dominate : ∀ x : R, x ≠ 0 → ∃ u : R, IsUnit (f u) ∧
      ∀ v : R, v ∣ x → IsUnit (f v) → v ∣ u) : WfDvdMonoid R := by
  classical
  choose q hq using O.profile
  refine wfDvdMonoid_of_dominatedUnitDivisors f hf hB dominate
    (fun u hu => (q u hu).rank (O.guards u)) ?_
  rintro _ v a hu hv rfl hnon
  have hua : IsUnit (f v * f a) := by rwa [← map_mul]
  have ha := isUnit_of_mul_isUnit_right hua
  have hva : v ≠ 0 := fun h => hv.ne_zero (by rw [h, map_zero])
  have haa : a ≠ 0 := fun h => ha.ne_zero (by rw [h, map_zero])
  rw [O.guards_mul v a hva haa]
  apply (q (v*a) hu).rank_lt_of_add (q v hv) (q a ha)
  · intro x
    simp only [hq, O.row_mul v a hva haa]
  · by_contra! hn
    apply hnon (O.unit_of_zero a ha (by omega) _)
    intro x
    have h := hn.1 x
    simpa [hq] using h

/-- For two-entry rows the guard order and the two constant evaluation
points bound the number of nonunit factors that become units in `B`. -/
theorem ProfileOrders.isBFDomain (O : ProfileOrders (fun _ => 0) f)
    (hf : Function.Injective f) (hB : IsBFDomain B) : IsBFDomain R := by
  let d (a : R) := O.guards a + O.row a (fun _ => 0) + O.row a (fun _ => 1)
  have hadd (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) : d (a*b) = d a + d b := by
    simp only [d, O.guards_mul a b ha hb, O.row_mul a b ha hb]
    omega
  have hone : d 1 = 0 := by have := hadd 1 1 one_ne_zero one_ne_zero; simp_all
  have hunit (a : R) (ha : IsUnit a) : d a = 0 := by
    obtain ⟨b, hb⟩ := isUnit_iff_dvd_one.mp ha
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    have h := hadd a b ha.ne_zero hb0
    rw [← hb, hone] at h
    omega
  apply isBFDomain_of_boundedAmbientUnitFactors f hf _ hB
  intro x hx
  apply hasBoundedAmbientUnitFactors_of_finite_nat_detectors f.toMonoidHom
    ({()} : Finset Unit) (fun _ => d) (fun _ _ => hunit) (fun _ _ => hadd) hx
  intro a _ _ hnon ha
  refine ⟨(), by simp, ?_⟩
  by_contra! hz
  have hz' : O.guards a + O.row a (fun _ => 0) + O.row a (fun _ => 1) = 0 :=
    Nat.eq_zero_of_le_zero hz
  obtain ⟨q, hq⟩ := O.profile a ha
  apply hnon (O.unit_of_zero a ha (by omega) _)
  have h0 : q.eval (fun _ => 0) = 0 := by rw [hq]; omega
  have h1 : q.eval (fun _ => 1) = 0 := by rw [hq]; omega
  intro y
  exact (hq y).symm.trans (q.binary_eq_zero h0 h1 y)

end UnconditionalCounterexample.Hierarchy.Prescribed
