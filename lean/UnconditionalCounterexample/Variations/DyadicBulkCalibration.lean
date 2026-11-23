import UnconditionalCounterexample.Variations.DyadicLedgerCalibration
import UnconditionalCounterexample.Variations.DyadicFreshFibres

/-!
# Simultaneous calibration of finitely many horizontal factors

All discrepancies are read from the same pre-stage table. The auxiliary
primes for one factor screen the other pending factors and the previously
frozen product on both branches.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger
open Polynomial GuardSupport RecursivePrefix Univariate Calibration

variable {n : ℕ} {m : Ledger} {P : Prefix n}

namespace FreshFibres

/-- Preserve the labels and the actual branch evaluations of a subfamily. -/
def Included (a b : FreshFibres m P) : Prop :=
  ∀ p (hp : p ∈ a.births.primes), ∃ h : p ∈ b.births.primes,
    b.role p h = a.role p hp ∧ b.births.site p h = a.births.site p hp

theorem Included.trans {a b c : FreshFibres m P} (h : a.Included b) (j : b.Included c) :
    a.Included c := by
  intro p hp
  obtain ⟨hb, hrb, hsb⟩ := h p hp
  obtain ⟨hc, hrc, hsc⟩ := j p hb
  exact ⟨hc, hrc.trans hrb, hsc.trans hsb⟩

/-- Every label in an auxiliary batch is an auxiliary role. -/
def AuxiliaryOnly (a : FreshFibres m P) : Prop :=
  ∀ p hp, ∃ k j ε, a.role p hp = some (.auxiliary k j ε)

theorem AuxiliaryOnly.no_regular {a : FreshFibres m P} (ha : a.AuxiliaryOnly) :
    ∀ p hp c k i, a.role p hp ≠ some (.regular c k i) := by
  intro p hp c k i he
  obtain ⟨_, _, _, h⟩ := ha p hp
  rw [h] at he
  cases he

theorem included_union_left (a b : FreshFibres m P) (hd : Disjoint a.births.primes b.births.primes)
    (h : b.AuxiliaryOnly) : a.Included (a.unionAux b hd h.no_regular) := by
  intro p hp
  exact ⟨Finset.mem_union_left _ hp, a.unionAux_role_left b hd h.no_regular p hp,
    a.births.union_site_left b.births hd p hp⟩

theorem included_union_right (a b : FreshFibres m P) (hd : Disjoint a.births.primes b.births.primes)
    (h : b.AuxiliaryOnly) : b.Included (a.unionAux b hd h.no_regular) := by
  intro p hp
  exact ⟨Finset.mem_union_right _ hp, a.unionAux_role_right b hd h.no_regular p hp,
    a.births.union_site_right b.births hd p hp⟩

end FreshFibres

/-- An integral horizontal polynomial is a unit at both actual branches. -/
def ScreensAt {p : PrimeIndex} (s : Site p) (f : ℤ[X]) : Prop :=
  ∀ b, ‖aeval (s.branch b) f‖ = 1

theorem ScreensAt.order_zero {p : PrimeIndex} {s : Site p} {f : ℤ[X]}
    (h : ScreensAt s f) (b : Bool) : (aeval (s.branch b) f).valuation = 0 := by
  have hn := h b
  have hz : aeval (s.branch b) f ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
  simpa using EvaluationChoices.valuation_eq_of_norm_eq p.val hz (one_ne_zero : (1 : ℚ_[p.val]) ≠ 0)
    (hn.trans norm_one.symm)

namespace FreezeFibres
variable {f G g : ℤ[X]} (F : FreezeFibres m P f G)

theorem auxiliaryOnly : F.toFreshFibres.AuxiliaryOnly := by
  intro p hp
  obtain ⟨k, u, hu, rfl⟩ := F.covers p hp
  obtain ⟨_, h, _⟩ := F.at_site k u hu
  exact ⟨k, u.index, _, h⟩

theorem screens_dvd (hg : g ∣ G) (p : PrimeIndex) (hp : p ∈ F.births.primes) :
    ScreensAt (F.births.site p hp) g := by
  obtain ⟨k, u, hu, rfl⟩ := F.covers p hp
  obtain ⟨_, _, hs⟩ := F.at_site k u hu
  rw [hs]
  have unit_norm (x : ℤ_[u.site.prime.val]) (h : IsUnit (aeval x G)) :
      ‖aeval x.val g‖ = 1 := by
    have h' := isUnit_of_dvd_unit ((aeval x).toRingHom.map_dvd hg) h
    have he : aeval x.val g = ((aeval x g : ℤ_[u.site.prime.val]) : ℚ_[u.site.prime.val]) :=
      aeval_algebraMap_apply ℚ_[u.site.prime.val] x g
    rw [he]
    exact PadicInt.isUnit_iff.mp h'
  intro b
  cases b with
  | false => exact unit_norm _ u.site.frozen_primary
  | true => exact unit_norm _ u.site.frozen_guard

end FreezeFibres

namespace BulkCalibration

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The product screened when correcting the factor indexed by `i`. -/
def screenProduct (f : I → ℤ[X]) (G : ℤ[X]) (i : I) : ℤ[X] :=
  G * ∏ j ∈ Finset.univ.erase i, f j

theorem other_dvd (f : I → ℤ[X]) (G : ℤ[X]) {i j : I} (h : j ≠ i) :
    f j ∣ screenProduct f G i :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem f (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)) _

theorem old_dvd (f : I → ℤ[X]) (G : ℤ[X]) (i : I) : G ∣ screenProduct f G i :=
  dvd_mul_right _ _

/-- Finite polynomial input on the given immediate raw prefix. -/
structure Inputs (P : Prefix n) (f : I → ℤ[X]) (G : ℤ[X]) : Prop where
  degree : ∀ i, (f i).natDegree ≠ 0
  primitive : ∀ i, (f i).IsPrimitive
  irreducible : ∀ i, Irreducible (f i)
  old_nonzero : G ≠ 0
  old_coprime : ∀ i, IsCoprime ((f i).map (algebraMap ℤ ℚ)) (G.map (algebraMap ℤ ℚ))
  distinct : ∀ i j, j ≠ i → IsCoprime ((f i).map (algebraMap ℤ ℚ)) ((f j).map (algebraMap ℤ ℚ))
  raw_coprime : ∀ i (j : Fin n), IsCoprime ((f i).map (algebraMap ℤ ℚ)) (P.raw j)

theorem Inputs.screen_nonzero {f : I → ℤ[X]} {G : ℤ[X]} (h : Inputs P f G) (i : I) :
    screenProduct f G i ≠ 0 :=
  mul_ne_zero h.old_nonzero (Finset.prod_ne_zero_iff.mpr fun j _ => (h.irreducible j).ne_zero)

theorem Inputs.screen_coprime {f : I → ℤ[X]} {G : ℤ[X]} (h : Inputs P f G) (i : I) :
    IsCoprime ((f i).map (algebraMap ℤ ℚ)) ((screenProduct f G i).map (algebraMap ℤ ℚ)) := by
  rw [screenProduct, Polynomial.map_mul, Polynomial.map_prod]
  exact (h.old_coprime i).mul_right (IsCoprime.prod_right fun j hj =>
    h.distinct i j (Finset.ne_of_mem_erase hj))

/-- The two corrections for one selected factor, embedded in the final
request. All the request's remaining primes screen this factor. -/
structure Corrects (a : FreshFibres m P) (T : Table P.state.assignment.primes)
    (f G : ℤ[X]) (height : Bool → ℤ) (L : ℕ) where
  component : FreezeFibres m P f G
  included : component.toFreshFibres.Included a
  outside : ∀ p hp, p ∉ component.births.primes → ScreensAt (a.births.site p hp) f
  late : ∀ k u, component.correction k = some u → L ≤ u.index
  calibrated : ∀ k, (tableProfile T m.role f height (0 : Unit →₀ ℤ)).signedMass
    (auxWeight m.role) (auxSign m.role) k + correctionMass (component.correction k) = height k

/-- A full simultaneous request, including the empty family. -/
structure Batch (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes)
    (f : I → ℤ[X]) (G : ℤ[X]) (height : I → Bool → ℤ) (cutoff L : ℕ) where
  fibres : FreshFibres m P
  auxiliary : fibres.AuxiliaryOnly
  above : ∀ p ∈ fibres.births.primes, cutoff < p.val
  screens : ∀ p hp, ScreensAt (fibres.births.site p hp) G
  correction : ∀ i, Corrects fibres T (f i) (screenProduct f G i) (height i) L

private def emptyFibres (m : Ledger) (P : Prefix n) : FreshFibres m P where
  births := correctionBirths (none : Option (Correction P 1 1))
  role p hp := (Finset.notMem_empty p hp).elim
  paired p hp := (Finset.notMem_empty p hp).elim
  primary_before p hp := (Finset.notMem_empty p hp).elim
  new_regular p hp := (Finset.notMem_empty p hp).elim
  distinct_regular p hp := (Finset.notMem_empty p hp).elim

private structure Partial (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes)
    (f : I → ℤ[X]) (G : ℤ[X]) (height : I → Bool → ℤ) (cutoff L : ℕ) (s : Finset I) where
  fibres : FreshFibres m P
  auxiliary : fibres.AuxiliaryOnly
  above : ∀ p ∈ fibres.births.primes, cutoff < p.val
  screens : ∀ p hp, ScreensAt (fibres.births.site p hp) G
  unselected : ∀ j ∉ s, ∀ p hp, ScreensAt (fibres.births.site p hp) (f j)
  correction : ∀ j ∈ s, Corrects fibres T (f j) (screenProduct f G j) (height j) L

/-- Select all auxiliary sites on the current table. Each new component
lies beyond the largest prime already selected for this request. -/
theorem exists_batch (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes)
    (f : I → ℤ[X]) (G : ℤ[X]) (h : Inputs P f G) (height : I → Bool → ℤ) (cutoff L : ℕ) :
    Nonempty (Batch m P T f G height cutoff L) := by
  classical
  have go (s : Finset I) : Nonempty (Partial m P T f G height cutoff L s) := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨⟨emptyFibres m P, fun p hp => (Finset.notMem_empty p hp).elim,
        fun p hp => (Finset.notMem_empty p hp).elim,
        fun p hp => (Finset.notMem_empty p hp).elim,
        fun _ _ p hp => (Finset.notMem_empty p hp).elim,
        fun j hj => (Finset.notMem_empty j hj).elim⟩⟩
    | @insert i s hi ih =>
      obtain ⟨a⟩ := ih
      let bound := max cutoff (a.fibres.births.primes.sup Subtype.val)
      obtain ⟨F, hlate, hmass⟩ := exists_freeze_fibres m P T (f i) (screenProduct f G i)
        (h.degree i) (h.primitive i) (h.irreducible i) (h.screen_nonzero i) (h.screen_coprime i)
        (h.raw_coprime i) (height i) (0 : Unit →₀ ℤ) bound L
      have above (p : PrimeIndex) (hp : p ∈ F.births.primes) : bound < p.val := by
        obtain ⟨k, u, hu, rfl⟩ := F.covers p hp
        exact (hlate k u hu).2
      have hd : Disjoint a.fibres.births.primes F.births.primes := by
        refine Finset.disjoint_left.mpr fun p ha hf => ?_
        exact (above p hf).not_ge ((Finset.le_sup (f := Subtype.val) ha).trans (le_max_right cutoff _))
      let b := a.fibres.unionAux F.toFreshFibres hd F.auxiliaryOnly.no_regular
      have hl : a.fibres.Included b := a.fibres.included_union_left _ hd F.auxiliaryOnly
      have hr : F.toFreshFibres.Included b := a.fibres.included_union_right _ hd F.auxiliaryOnly
      have parts (p : PrimeIndex) (hp : p ∈ b.births.primes) :
          p ∈ a.fibres.births.primes ∨ p ∈ F.births.primes := Finset.mem_union.mp hp
      have combineScreen (g : ℤ[X])
          (h₁ : ∀ p hp, ScreensAt (a.fibres.births.site p hp) g)
          (h₂ : ∀ p hp, ScreensAt (F.births.site p hp) g) :
          ∀ p hp, ScreensAt (b.births.site p hp) g := by
        intro p hp
        rcases parts p hp with ha | hf
        · rw [(hl p ha).choose_spec.2]
          exact h₁ p ha
        · rw [(hr p hf).choose_spec.2]
          exact h₂ p hf
      refine ⟨⟨b, ?_, ?_, combineScreen G a.screens (F.screens_dvd (old_dvd f G i)), ?_, ?_⟩⟩
      · intro p hp
        rcases parts p hp with ha | hf
        · rw [(hl p ha).choose_spec.1]
          exact a.auxiliary p ha
        · rw [(hr p hf).choose_spec.1]
          exact F.auxiliaryOnly p hf
      · intro p hp
        rcases parts p hp with ha | hf
        · exact a.above p ha
        · exact (le_max_left cutoff _).trans_lt (above p hf)
      · intro j hj
        have hj' := not_or.mp (fun h => hj (Finset.mem_insert.mpr h))
        exact combineScreen (f j) (a.unselected j hj'.2) (F.screens_dvd (other_dvd f G hj'.1))
      · intro j hj
        by_cases he : j = i
        · subst j
          refine ⟨F, hr, ?_, fun k u hu => (hlate k u hu).1, hmass⟩
          intro p hp hf
          obtain ha := (parts p hp).resolve_right hf
          rw [(hl p ha).choose_spec.2]
          exact a.unselected _ hi p ha
        · let old := a.correction j ((Finset.mem_insert.mp hj).resolve_left he)
          refine ⟨old.component, old.included.trans hl, ?_, old.late, old.calibrated⟩
          intro p hp hout
          rcases parts p hp with ha | hf
          · rw [(hl p ha).choose_spec.2]
            exact old.outside p ha hout
          · rw [(hr p hf).choose_spec.2]
            exact F.screens_dvd (other_dvd f G he) p hf
  obtain ⟨a⟩ := go Finset.univ
  exact ⟨⟨a.fibres, a.auxiliary, a.above, a.screens, fun i => a.correction i (Finset.mem_univ i)⟩⟩

/-- In the actual successor table, the finite request attains every target.
Extra regular fibres may be installed in the same request when their genuine
branch orders match the centre forecast. -/
theorem Batch.mass_after_inclusion (D : Driver) (n : ℕ) {f : I → ℤ[X]} {G : ℤ[X]}
    {height : I → Bool → ℤ} {cutoff L : ℕ}
    (B : Batch (D.state n) ((chain D.requirements).approx n) (table D.requirements n)
      f G height cutoff L)
    (hin : B.fibres.Included (D.actualRequest n).toFreshFibres)
    (extra : ∀ i p (hp : p ∈ (D.actualRequest n).births.primes), p ∉ B.fibres.births.primes →
      ∀ r, (D.actualRequest n).role p hp = some r →
        (aeval (((D.actualRequest n).births.site p hp).branch false) (f i)).valuation =
            forecastOrder (height i) (some r) ∧
          (aeval (((D.actualRequest n).births.site p hp).branch true) (f i)).valuation = 0)
    (i : I) (k : Bool) : D.provisionalMass (n+1) (f i) (height i) k = height i k := by
  let c := B.correction i
  rw [D.mass_after_freeze n (f i) _ (height i) c.component (c.included.trans hin) _ k]
  · exact c.calibrated k
  · intro p hp hout r hr
    by_cases hb : p ∈ B.fibres.births.primes
    · have hs := c.outside p hb hout
      obtain ⟨_, hl, he⟩ := hin p hb
      obtain ⟨ch, j, ε, haux⟩ := B.auxiliary p hb
      have hrole := Option.some.inj (hr.symm.trans (hl.trans haux))
      rw [he, hrole]
      exact ⟨hs.order_zero false, hs.order_zero true⟩
    · exact extra i p hp hb r hr

/-- A calibration-only successor attains all targets without additional
screening hypotheses. -/
theorem Batch.mass_after_exact (D : Driver) (n : ℕ) {f : I → ℤ[X]} {G : ℤ[X]}
    {height : I → Bool → ℤ} {cutoff L : ℕ}
    (B : Batch (D.state n) ((chain D.requirements).approx n) (table D.requirements n)
      f G height cutoff L)
    (heq : (D.actualRequest n).toFreshFibres = B.fibres) (i : I) (k : Bool) :
    D.provisionalMass (n+1) (f i) (height i) k = height i k := by
  apply B.mass_after_inclusion D n _ _ i k
  · rw [heq]
    exact fun _ hp => ⟨hp, rfl, rfl⟩
  · intro _ p hp hnot
    exact False.elim (hnot (congrArg (fun t => t.births.primes) heq ▸ hp))

end BulkCalibration
end UnconditionalCounterexample.Variations.DyadicLedger
