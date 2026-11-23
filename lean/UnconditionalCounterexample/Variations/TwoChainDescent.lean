import Factorization.WeakACCP
import UnconditionalCounterexample.ConductorAtomicity
import UnconditionalCounterexample.FiniteDivisorBounds
import UnconditionalCounterexample.Variations.TwoChainBox

/-!
# Descent for two endpoint orders

If every member is
high at one centre, choose a single returning factor there. Each step
decreases the sum of the orders of any one fixed original member. A residual
family can therefore be small at the two centres on different entries.
-/

noncomputable section
namespace UnconditionalCounterexample.TwoChains

open Factorization Filter

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Descend a whole tuple in its own ring. The small-box input supplies
finite common divisor classes even when the two minimizing entries differ. -/
theorem exists_mcd_of_two_orders (ord : Bool → R → ℕ)
    (hmul : ∀ c (x y : R), x ≠ 0 → y ≠ 0 → ord c (x*y) = ord c x + ord c y)
    (hbox : ∀ s : Finset R, (∀ x ∈ s, x ≠ 0) → (∀ c, ∃ x ∈ s, ord c x ≤ 1) →
      (Associates.mk '' {d : R | ∀ x ∈ s, d ∣ x}).Finite)
    (hcommon : ∀ (s : Finset R) (c : Bool), (∀ x ∈ s, x ≠ 0) →
      (∀ x ∈ s, 2 ≤ ord c x) → ∃ a : R, 0 < ord false a + ord true a ∧ ∀ x ∈ s, a ∣ x)
    (s : Finset R) (hn : ∀ x ∈ s, x ≠ 0) (hs : s.Nonempty) :
    ∃ d : R, IsMaximalCommonDivisor s d := by
  classical
  obtain ⟨b, hb⟩ := hs
  generalize he : ord false b + ord true b = n
  induction n using Nat.strong_induction_on generalizing b s with
  | h n ih =>
    by_cases hlow : ∀ c, ∃ x ∈ s, ord c x ≤ 1
    · exact exists_maximalCommonDivisor_of_finite_classes s ⟨b, hb, hn b hb⟩ (hbox s hn hlow)
    push Not at hlow
    obtain ⟨c, hc⟩ := hlow
    obtain ⟨a, ha, hall⟩ := hcommon s c hn (fun x hx => hc x hx)
    let q (x : R) : R := if h : x ∈ s then (hall x h).choose else 0
    have hq (x : R) (hx : x ∈ s) : x = a * q x := by
      simpa only [q, dite_eq_left hx] using (hall x hx).choose_spec
    have hprod (x : R) (hx : x ∈ s) : a * q x ≠ 0 := hq x hx ▸ hn x hx
    have haz := left_ne_zero_of_mul (hprod b hb)
    have hqz (x : R) (hx : x ∈ s) := right_ne_zero_of_mul (hprod x hx)
    have hlt : ord false (q b) + ord true (q b) < n := by
      have h₀ := hmul false a (q b) haz (hqz b hb)
      have h₁ := hmul true a (q b) haz (hqz b hb)
      rw [← hq b hb] at h₀ h₁
      omega
    obtain ⟨d, hd⟩ := ih _ hlt (s.image q)
      (fun y hy => by obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy; exact hqz x hx)
      (q b) (Finset.mem_image_of_mem q hb) rfl
    have heq : (s.image q).image (a * ·) = s := by
      ext y
      constructor
      · rintro hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        exact hq x hx ▸ hx
      · intro hy
        exact Finset.mem_image.mpr ⟨q y, Finset.mem_image_of_mem _ hy, (hq y hy).symm⟩
    exact ⟨a*d, heq ▸ hd.mul_left haz⟩

omit [IsDomain R] in
/-- Common ambient divisors can be restricted to a subring whose ambient units
are signs. This uses the same finite family in both rings. -/
theorem finite_classes_in_subring (T : Subring R) (s : Finset T)
    (hsign : ∀ u : R, IsUnit u → u = 1 ∨ u = -1)
    (hf : (Associates.mk '' {d : R | ∀ x ∈ s, d ∣ (x : R)}).Finite) :
    (Associates.mk '' {d : T | ∀ x ∈ s, d ∣ x}).Finite := by
  have hfin : {d : R | ∀ x ∈ s, d ∣ (x : R)}.Finite := by
    apply ((hf.image Quot.out).union ((hf.image Quot.out).image (fun z : R => -z))).subset
    intro z hz
    have hm : Associates.mk z ∈ Associates.mk '' {d : R | ∀ x ∈ s, d ∣ (x : R)} :=
      ⟨z, hz, rfl⟩
    obtain ⟨u, hu⟩ := Associates.mk_quot_out z
    rcases hsign u u.isUnit with h | h
    · exact Or.inl ⟨Associates.mk z, hm, by simpa only [h, mul_one] using hu⟩
    · exact Or.inr ⟨Quot.out (Associates.mk z), ⟨Associates.mk z, hm, rfl⟩,
        by simpa only [h, mul_neg_one] using hu⟩
  apply Set.Finite.image
  apply (hfin.preimage Subtype.val_injective.injOn).subset
  intro z hz x hx
  exact map_dvd T.subtype (hz x hx)

omit [IsDomain R] in
/-- Late divisibility and conductor returns give a common factor for each
colour in the subring itself. -/
theorem exists_returning_common_factor (T : Subring R) (m : R)
    (hcond : ∀ z : R, m*z ∈ T) (ord : Bool → R → ℕ) (a : Bool → ℕ → R)
    (hret : ∀ c (N : ℕ), ∃ n ≥ N, m ∣ a c n - 1)
    (hdvd : ∀ c x, x ≠ 0 → 2 ≤ ord c x → ∀ᶠ n in atTop, a c n ∣ x)
    (s : Finset T) (c : Bool) (hn : ∀ x ∈ s, x ≠ 0) (hh : ∀ x ∈ s, 2 ≤ ord c x) :
    ∃ (n : ℕ) (haT : a c n ∈ T), ∀ x ∈ s, (⟨a c n, haT⟩ : T) ∣ x := by
  have hevent : ∀ᶠ n in atTop, ∀ x ∈ s, a c n ∣ (x : R) :=
    (eventually_all_finset s).mpr fun x hx => hdvd c x (fun h => hn x hx (Subtype.ext h)) (hh x hx)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  obtain ⟨n, hlarge, hcong⟩ := hret c N
  refine ⟨n, mem_subring_of_conductor_dvd_sub_one T m hcond hcong, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hN n hlarge x hx
  exact ⟨⟨y, cofactor_mem_subring_of_conductor T m hcond (hy ▸ x.property) hcong⟩, Subtype.ext hy⟩

/-- Strong atomicity from the two geometric orders, a uniform bound for divisors,
and returns modulo the common conductor. -/
theorem hereditarilyStronglyAtomic_of_two_orders
    (ord : Bool → R → ℕ)
    (hmul : ∀ c (x y : R), x ≠ 0 → y ≠ 0 → ord c (x*y) = ord c x + ord c y)
    (hbox : ∀ s : Finset R, (∀ x ∈ s, x ≠ 0) → (∀ c, ∃ x ∈ s, ord c x ≤ 1) →
      (Associates.mk '' {d : R | ∀ x ∈ s, d ∣ x}).Finite)
    (hsign : ∀ u : R, IsUnit u → u = 1 ∨ u = -1)
    (a : Bool → ℕ → R) (hsum : ∀ c n, ord false (a c n) + ord true (a c n) = 1)
    (hret : ∀ (m : ℕ), 0 < m → ∀ c N, ∃ n ≥ N, (m : R) ∣ a c n - 1)
    (hdvd : ∀ c x, x ≠ 0 → 2 ≤ ord c x → ∀ᶠ n in atTop, a c n ∣ x)
    (hconductors : ∀ T : Subring R, ¬ IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : R, (m : R)*z ∈ T) : IsHereditarilyStronglyAtomic R := by
  classical
  intro T
  by_cases hBF : IsBFDomain T
  · exact (isWeakACCP_of_wfDvdMonoid hBF.wfDvdMonoid).isStronglyAtomicDomain
  obtain ⟨m, hm, hcond⟩ := hconductors T hBF
  let o (c : Bool) (x : T) := ord c (x : R)
  have hadd (c : Bool) (x y : T) (hx : x ≠ 0) (hy : y ≠ 0) : o c (x*y) = o c x + o c y :=
    hmul c x y (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h))
  have hsmall (s : Finset T) (hn : ∀ x ∈ s, x ≠ 0) (hlow : ∀ c, ∃ x ∈ s, o c x ≤ 1) :
      (Associates.mk '' {d : T | ∀ x ∈ s, d ∣ x}).Finite := by
    apply finite_classes_in_subring T s hsign
    let S := s.image (Subtype.val : T → R)
    have hn' : ∀ x ∈ S, x ≠ 0 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact fun h => hn y hy (Subtype.ext h)
    have hlow' (c : Bool) : ∃ x ∈ S, ord c x ≤ 1 := by
      obtain ⟨y, hy, hle⟩ := hlow c
      exact ⟨y, Finset.mem_image_of_mem _ hy, hle⟩
    simpa only [S, Finset.forall_mem_image] using hbox S hn' hlow'
  have hcommon (s : Finset T) (c : Bool) (hn : ∀ x ∈ s, x ≠ 0)
      (hh : ∀ x ∈ s, 2 ≤ o c x) :
      ∃ d : T, o false d + o true d = 1 ∧ ∀ x ∈ s, d ∣ x := by
    obtain ⟨n, ha, hall⟩ := exists_returning_common_factor T (m : R) hcond ord a
      (hret m hm) hdvd s c hn hh
    exact ⟨⟨a c n, ha⟩, hsum c n, hall⟩
  have hatomicLow (x : T) (hx : x ≠ 0) (hlow : ∀ c, o c x ≤ 1) : HasAtomicFactorization x := by
    apply HasBoundedFactorizations.hasAtomicFactorization
    apply FiniteDivisorBounds.hasBoundedFactorizations_of_finite_divisor_classes hx
    have h := hsmall {x} (by simpa) fun c => ⟨x, by simp, hlow c⟩
    apply h.subset
    rintro z hz
    obtain ⟨d, rfl⟩ := Associates.mk_surjective z
    exact ⟨d, by simpa using Associates.mk_dvd_mk.mp hz, rfl⟩
  constructor
  · intro x hx
    generalize he : o false x + o true x = n
    induction n using Nat.strong_induction_on generalizing x with
    | h n ih =>
      by_cases hlow : ∀ c, o c x ≤ 1
      · exact hatomicLow x hx hlow
      push Not at hlow
      obtain ⟨c, hc⟩ := hlow
      obtain ⟨d, hd, hf⟩ := hcommon {x} c (by simpa) (by simpa using (show 2 ≤ o c x by omega))
      obtain ⟨y, hxy⟩ := hf x (by simp)
      have hprod : d*y ≠ 0 := hxy ▸ hx
      have hd0 := left_ne_zero_of_mul hprod
      have hy0 := right_ne_zero_of_mul hprod
      have h₀ := hadd false d y hd0 hy0
      have h₁ := hadd true d y hd0 hy0
      rw [← hxy] at h₀ h₁
      have hda := hatomicLow d hd0 (fun col => by cases col <;> omega)
      rw [hxy]
      exact hda.mul (ih _ (by omega) y hy0 rfl)
  · intro x y hx hy
    have hmcd := exists_mcd_of_two_orders o hadd hsmall
    -- A returning divisor has positive total order. The existence-of-MCD
    -- descent uses this total, independently of which centre supplied it.
    obtain ⟨d, hd⟩ := hmcd (fun s c hn hh => by
      obtain ⟨d, hsumd, hdiv⟩ := hcommon s c hn hh
      exact ⟨d, by omega, hdiv⟩)
      {x,y} (by simpa using And.intro hx hy) (by simp)
    obtain ⟨u, hu⟩ := hd.1 x (by simp)
    obtain ⟨v, hv⟩ := hd.1 y (by simp)
    have hd0 := left_ne_zero_of_mul (hu ▸ hx)
    exact ⟨d,u,v,hu,hv,(isMaximalCommonDivisor_pair_iff hd0).mp (hu ▸ hv ▸ hd)⟩

/-- Combining BOX and SUBRINGS leaves the geometric profile calculations and
the integer conductor as construction inputs. -/
theorem hereditarilyStronglyAtomic_of_profiles {ι : Type*}
    (v : Variations.TwoChainBox.Orders R ι) (dvd : v.DetectsDivisibility)
    (hadd : ∀ c (x y : R), x ≠ 0 → y ≠ 0 →
      v.endpoint (x*y) c = v.endpoint x c + v.endpoint y c)
    (hsign : ∀ u : R, IsUnit u → u = 1 ∨ u = -1)
    (a : Bool → ℕ → R) (ha : ∀ c, Variations.TwoChainBox.MovingProfiles v c (a c))
    (hret : ∀ m : ℕ, 0 < m → ∀ c N, ∃ n ≥ N, (m : R) ∣ a c n - 1)
    (hconductors : ∀ T : Subring R, ¬ IsBFDomain T →
      ∃ m : ℕ, 0 < m ∧ ∀ z : R, (m : R)*z ∈ T) : IsHereditarilyStronglyAtomic R := by
  apply hereditarilyStronglyAtomic_of_two_orders (fun c x => v.endpoint x c)
    hadd (Variations.TwoChainBox.finite_common_divisor_classes v) hsign a _ hret _ hconductors
  · intro c n
    cases c
    · rw [(ha false).endpoint n, (ha false).other_endpoint n true (by decide)]
    · rw [(ha true).endpoint n, (ha true).other_endpoint n false (by decide)]
  · intro c x hx hh
    exact eventually_atTop.mpr ((ha c).eventually_dvd dvd hx hh)

end UnconditionalCounterexample.TwoChains
