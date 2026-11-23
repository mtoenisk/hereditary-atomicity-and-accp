import UnconditionalCounterexample.Variations.CalibrationTable
import UnconditionalCounterexample.Variations.DyadicLedger

/-! # Freezing a polynomial by two signed corrections on the adaptive ledger -/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger

open Polynomial GuardSupport RecursivePrefix Univariate Calibration

variable {n : ℕ} {P : Prefix n} {f G : ℤ[X]} {m : Ledger}

/-- All newly labelled fibres at a calibration step, and the channel
correction realized by each actual paired prime. -/
structure FreezeFibres (m : Ledger) (P : Prefix n) (f G : ℤ[X]) extends FreshFibres m P where
  correction : Bool → Option (Correction P f G)
  at_site : ∀ k u, correction k = some u → ∃ h : u.site.prime ∈ births.primes,
    role u.site.prime h = some (u.role k) ∧
      births.site u.site.prime h = ⟨u.site.guard.value, u.site.guard.transcendental, some u.site.primary⟩
  covers : ∀ p ∈ births.primes, ∃ k u, correction k = some u ∧ p = u.site.prime

private theorem mem_slot (c : Option (Correction P f G)) (p : PrimeIndex) :
    p ∈ (correctionBirths c).primes ↔ ∃ u, c = some u ∧ p = u.site.prime := by
  cases c <;> simp [correctionBirths, AtPrefix.births, Births.singleton]

private def slotRole (c : Bool → Option (Correction P f G)) (p : PrimeIndex) : Option FibreRole :=
  if p ∈ (correctionBirths (c false)).primes then (c false).map (fun u => u.role false)
  else (c true).map (fun u => u.role true)

private theorem slotRole_at (c : Bool → Option (Correction P f G))
    (hd : Disjoint (correctionBirths (c false)).primes (correctionBirths (c true)).primes)
    (k : Bool) (u : Correction P f G) (h : c k = some u) :
    slotRole c u.site.prime = some (u.role k) := by
  have hmem := (mem_slot (c k) u.site.prime).mpr ⟨u, h, rfl⟩
  cases k with
  | false => rw [slotRole, ite_eq_left hmem, h]; rfl
  | true =>
    have hnot : u.site.prime ∉ (correctionBirths (c false)).primes :=
      fun hm => Finset.disjoint_left.mp hd hm hmem
    simp [slotRole, hnot, h]

/-- Produce the actual fresh-fibre request for the polynomial on the current
table, with both channel masses calibrated to their horizontal targets. -/
theorem exists_freeze_fibres (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes)
    (f G : ℤ[X]) (hd : f.natDegree ≠ 0) (hprim : f.IsPrimitive) (hirr : Irreducible f)
    (hG : G ≠ 0) (hc : IsCoprime (f.map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ)))
    (hraw : ∀ j : Fin n, IsCoprime (f.map (algebraMap ℤ ℚ)) (P.raw j))
    (height : Bool → ℤ) {H : Type*} (hor : H →₀ ℤ) (bound L : ℕ) :
    ∃ F : FreezeFibres m P f G,
      (∀ k u, F.correction k = some u → L ≤ u.index ∧ bound < u.site.prime.val) ∧
      ∀ k, (tableProfile T m.role f height hor).signedMass (auxWeight m.role) (auxSign m.role) k +
        correctionMass (F.correction k) = height k := by
  classical
  obtain ⟨c, B, _, hm, hi, hdis, hB, hsite⟩ := exists_two_channel_correction P f G hd hprim
    hirr hG hc hraw (tableProfile T m.role f height hor) (auxWeight m.role) (auxSign m.role)
    height bound L
  have cover (p : PrimeIndex) (hp : p ∈ B.primes) : ∃ k u, c k = some u ∧ p = u.site.prime := by
    rw [hB, Finset.mem_union] at hp
    rcases hp with h | h
    · exact ⟨false, (mem_slot _ _).mp h⟩
    · exact ⟨true, (mem_slot _ _).mp h⟩
  have atSite (k : Bool) (u : Correction P f G) (hu : c k = some u) :
      ∃ h : u.site.prime ∈ B.primes, B.site u.site.prime h =
        ⟨u.site.guard.value, u.site.guard.transcendental, some u.site.primary⟩ := by
    obtain ⟨hp, he⟩ := hsite k u.site.prime ((mem_slot _ _).mpr ⟨u, hu, rfl⟩)
    refine ⟨hp, he.trans ?_⟩
    simp only [hu]
    rfl
  let fresh : FreshFibres m P := {
    births := B
    role := fun p _ => slotRole c p
    paired := by
      intro p hp
      obtain ⟨k, u, hu, rfl⟩ := cover p hp
      rw [(atSite k u hu).choose_spec, slotRole_at c hdis k u hu]
      rfl
    primary_before := by
      intro p hp _ j
      obtain ⟨k, u, hu, rfl⟩ := cover p hp
      rw [(atSite k u hu).choose_spec]
      exact u.site.old_primary j
    new_regular := by
      intro p hp a b i h
      obtain ⟨k, u, hu, rfl⟩ := cover p hp
      rw [slotRole_at c hdis k u hu] at h
      cases h
    distinct_regular := by
      intro p hp q hq a b i h
      obtain ⟨k, u, hu, rfl⟩ := cover p hp
      rw [slotRole_at c hdis k u hu] at h
      cases h }
  refine ⟨⟨fresh, c, ?_, cover⟩, hi, hm⟩
  intro k u hu
  obtain ⟨hp, he⟩ := atSite k u hu
  exact ⟨hp, slotRole_at c hdis k u hu, he⟩

namespace Driver

/-- Provisional mass read from the actual table immediately before raw
`n`. Horizontal support away from the centres carries no weight. -/
def provisionalMass (D : Driver) (n : ℕ) (f : ℤ[X]) (height : Bool → ℤ) (k : Bool) : ℚ :=
  (tableProfile (table D.requirements n) (D.state n).role f height
    (0 : Unit →₀ ℤ)).signedMass (auxWeight (D.state n).role) (auxSign (D.state n).role) k

/-- On the actual successor of the same recursive chain, a calibration
request increases both masses by precisely its two (possibly empty)
corrections. Additional requested fibres may be inserted if they screen
this polynomial at the predicted orders. -/
theorem mass_after_freeze (D : Driver) (n : ℕ) (f G : ℤ[X]) (height : Bool → ℤ)
    (F : FreezeFibres (D.state n) ((chain D.requirements).approx n) f G)
    (used : ∀ p (hp : p ∈ F.births.primes), ∃ h : p ∈ (D.actualRequest n).births.primes,
      (D.actualRequest n).role p h = F.role p hp ∧
      (D.actualRequest n).births.site p h = F.births.site p hp)
    (extra : ∀ p (hp : p ∈ (D.actualRequest n).births.primes), p ∉ F.births.primes →
      ∀ r, (D.actualRequest n).role p hp = some r →
        (aeval (((D.actualRequest n).births.site p hp).branch false) f).valuation =
            forecastOrder height (some r) ∧
          (aeval (((D.actualRequest n).births.site p hp).branch true) f).valuation = 0)
    (k : Bool) :
    D.provisionalMass (n+1) f height k = D.provisionalMass n f height k +
      correctionMass (F.correction k) := by
  let R := D.requirements
  let P := (chain R).approx n
  have holds (p : PrimeIndex) (h : p ∈ (D.actualRequest n).births.primes) :
      ∃ hp : p ∈ ((chain R).approx (n+1)).state.assignment.primes,
        table R (n+1) p hp = (D.actualRequest n).births.site p h := by
    have hp := (selection R n).batch.processed_subset_assigned (D.schedule.requested_processed n h)
    exact ⟨hp, (table_eq_permanentSite R (n+1) p hp).trans (D.permanent_role (n := n) p h).1⟩
  apply tableProfile_after_corrections (P := P) (table R n) (table R (n+1))
    (assigned_mono R (Nat.le_succ n)) (D.state n).role (D.state (n+1)).role height
    (0 : Unit →₀ ℤ) F.correction _ _ _ k
  · intro p hp
    exact ⟨table_persistent R n p hp _, D.role_old n p hp⟩
  · intro b u hu
    obtain ⟨hp, hl, hs⟩ := F.at_site b u hu
    obtain ⟨hreq, hl', hs'⟩ := used _ hp
    obtain ⟨hp', ht⟩ := holds _ hreq
    exact ⟨hp', ((D.permanent_role (n := n) _ hreq).2 _ (Nat.lt_succ_self n)).trans (hl'.trans hl),
      ht.trans (hs'.trans hs)⟩
  · intro p hp hnew
    by_cases hF : p ∈ F.births.primes
    · exact Or.inl (F.covers p hF)
    right
    intro r hr
    by_cases hreq : p ∈ (D.actualRequest n).births.primes
    · obtain ⟨hp', ht⟩ := holds p hreq
      have hrole := (D.permanent_role (n := n) p hreq).2 _ (Nat.lt_succ_self n)
      have hs := extra p hreq hF r (hrole.symm.trans hr)
      simp only [tableOrder, hp', ↓reduceDIte, ht]
      exact hs
    · have hnone := D.role_none_of_unassigned n p hnew
      rw [D.state_succ] at hr
      simp [Request.update, Request.nextRole, hreq, hnone] at hr

/-- A raw stage devoted to these calibration fibres requires no separate
screening input. -/
theorem mass_after_exact_freeze (D : Driver) (n : ℕ) (f G : ℤ[X]) (height : Bool → ℤ)
    (F : FreezeFibres (D.state n) ((chain D.requirements).approx n) f G)
    (used : (D.actualRequest n).toFreshFibres = F.toFreshFibres) (k : Bool) :
    D.provisionalMass (n+1) f height k = D.provisionalMass n f height k +
      correctionMass (F.correction k) := by
  apply D.mass_after_freeze n f G height F _ _ k
  · intro p hp
    rw [used]
    exact ⟨hp, rfl, rfl⟩
  · intro p hp hn
    exact False.elim (hn (congrArg (fun t => t.births.primes) used ▸ hp))

/-- Keep a calibrated mass at every later stage using the screening
condition only on the newly requested paired fibres of that stage. -/
theorem provisionalMass_persistent (D : Driver) {a b : ℕ} (hab : a ≤ b)
    (f : ℤ[X]) (height : Bool → ℤ)
    (screen : ∀ n, a ≤ n → n < b → ∀ p (hp : p ∈ (D.actualRequest n).births.primes) r,
      (D.actualRequest n).role p hp = some r →
        (aeval (((D.actualRequest n).births.site p hp).branch false) f).valuation =
            forecastOrder height (some r) ∧
          (aeval (((D.actualRequest n).births.site p hp).branch true) f).valuation = 0)
    (k : Bool) : D.provisionalMass b f height k = D.provisionalMass a f height k := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hprev := ih (fun j h₁ h₂ => screen j h₁ (h₂.trans (Nat.lt_succ_self _)))
    rw [← hprev]
    apply provisional_signedMass_persistent (assigned_mono D.requirements (Nat.le_succ n))
    · intro p hp
      have hp' := (assigned_mono D.requirements (Nat.le_succ n)) hp
      refine ⟨D.role_old n p hp, ?_, ?_⟩ <;>
        simp only [tableOrder, hp, hp', ↓reduceDIte, table_persistent D.requirements n p hp hp']
    · intro p hp hn' r hr
      by_cases hreq : p ∈ (D.actualRequest n).births.primes
      · have hrole := (D.permanent_role (n := n) p hreq).2 _ (Nat.lt_succ_self n)
        have h := screen n hn (Nat.lt_succ_self n) p hreq r (hrole.symm.trans hr)
        have ht := (table_eq_permanentSite D.requirements (n+1) p hp).trans
          (D.permanent_role (n := n) p hreq).1
        simpa only [tableOrder, hp, ↓reduceDIte, ht] using h
      · have hnone := D.role_none_of_unassigned n p hn'
        rw [D.state_succ] at hr
        simp [Request.update, Request.nextRole, hreq, hnone] at hr

end Driver

end UnconditionalCounterexample.Variations.DyadicLedger
