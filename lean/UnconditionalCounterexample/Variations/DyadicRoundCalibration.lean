import UnconditionalCounterexample.Variations.DyadicBulkInputs
import UnconditionalCounterexample.Variations.DyadicModelMass
import UnconditionalCounterexample.Variations.DyadicRoundWork
import UnconditionalCounterexample.Variations.DyadicModulusFibres

/-!
# Auxiliary and regular fibres of one round opening

The old table determines all the corrections. Their actual primes and weights
determine the auxiliary columns of the block. With its support now known, all
missing regular sites can be selected above the model-scalar cutoff.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.OpeningCalibration

open Polynomial GuardSupport RecursivePrefix Univariate Calibration BulkInputs

variable {n : ℕ} {m : Ledger} {P : Prefix n} {T : Table P.state.assignment.primes}
    {A K : Finset ℚ[X]} {hA : HorizontalSet A} {hK : HorizontalSet K} {bound L : ℕ}

/-- The two horizontal orders of a monic irreducible. -/
def height (f : ℚ[X]) (c : Bool) : ℤ :=
  if f = RegularForecast.centreFactor (if c then 1 else 0) then 1 else 0

def limit (hA : HorizontalSet A) (hK : HorizontalSet K) (bound : ℕ) : ℕ :=
  max bound (max (cutoff hA) (cutoff hK))

abbrev Phase (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes)
    (hA : HorizontalSet A) (hK : HorizontalSet K) (bound L : ℕ) :=
  BulkCalibration.Batch m P T (models hA) (product hK) (fun i => height i.val)
    (limit hA hK bound) L

/-- Perform the auxiliary step on the actual calendar's pending set. -/
def select (m : Ledger) (P : Prefix n) (T : Table P.state.assignment.primes)
    (K C : Finset ℚ[X]) (hK : HorizontalSet K) (hC : HorizontalSet C) (bound L : ℕ) :
    Phase m P T (A := FreezingCalendar.pending P K C)
      (fun f h => hC f (Finset.mem_filter.mp h).1) hK bound L :=
  Classical.choice (BulkCalibration.exists_batch m P T _ _ (pending_inputs P K C hK hC)
    _ _ _)

variable (B : Phase m P T hA hK bound L)

/-- Each auxiliary prime receives exactly its own new column. -/
def columnAt (p : B.fibres.births.primes) : RawColumn :=
  match B.fibres.role p.val p.property with
  | some (.auxiliary k i e) => .auxiliary p.val k i e
  | _ => .balanced false 0

def columns : List RawColumn := B.fibres.births.primes.attach.toList.map (columnAt B)

theorem columnAt_eq (p : B.fibres.births.primes) :
    ∃ k i e, B.fibres.role p.val p.property = some (.auxiliary k i e) ∧
      columnAt B p = .auxiliary p.val k i e := by
  obtain ⟨k, i, e, h⟩ := B.auxiliary p.val p.property
  exact ⟨k, i, e, h, by simp [columnAt, h]⟩

theorem columns_nodup : (columns B).Nodup := by
  apply (Finset.nodup_toList _).map
  intro p q he
  obtain ⟨_, _, _, _, hp⟩ := columnAt_eq B p
  obtain ⟨_, _, _, _, hq⟩ := columnAt_eq B q
  rw [hp, hq] at he
  exact Subtype.ext (RawColumn.auxiliary.inj he).1

theorem mem_columns (c : RawColumn) :
    c ∈ columns B ↔ ∃ (p : B.fibres.births.primes) (k : Bool) (i : ℕ) (e : Bool),
      B.fibres.role p.val p.property = some (.auxiliary k i e) ∧ c = .auxiliary p.val k i e := by
  constructor
  · intro h
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    exact ⟨p, columnAt_eq B p⟩
  · rintro ⟨p,k,i,e,h,rfl⟩
    exact List.mem_map.mpr ⟨p,Finset.mem_toList.mpr (Finset.mem_attach _ p),by simp [columnAt,h]⟩

def Orders {p : PrimeIndex} (s : Site p) (r : FibreRole) (f : ℚ[X]) : Prop :=
  (aeval (s.branch false) f).valuation = forecastOrder (height f) (some r) ∧
    (aeval (s.branch true) f).valuation = 0

private theorem model_orders {p : PrimeIndex} {s : Site p} (hs : s.paired)
    (i : A) (r : FibreRole) (hp : cutoff hA < p.val) (h : Orders s r i.val) :
    (aeval (s.branch false) (models hA i)).valuation = forecastOrder (height i.val) (some r) ∧
      (aeval (s.branch true) (models hA i)).valuation = 0 := by
  have lim := (Finset.le_sup (f := fun j : A => scalarBound (member hA j)) (Finset.mem_univ i)).trans_lt hp
  have hu := unit_scalar (member hA i) p lim
  have hz := EvaluationChoices.valuation_eq_of_norm_eq p.val
    (Rat.cast_ne_zero.mpr (model (member hA i)).scalar_ne)
    (one_ne_zero : (1 : ℚ_[p.val]) ≠ 0) (hu.trans norm_one.symm)
  have he (b : Bool) (hb : MixedStageSelection.Active s.paired b) :
      (aeval (s.branch b) (models hA i)).valuation = (aeval (s.branch b) i.val).valuation := by
    have hne : aeval (s.branch b) i.val ≠ 0 :=
      mt (transcendental_iff.mp (s.branch_transcendental b hb) i.val) (hA i.val i.property).1.ne_zero
    rw [models, model_eval, show (member hA i).val = i.val from rfl,
      Padic.valuation_mul (Rat.cast_ne_zero.mpr (model (member hA i)).scalar_ne)
      hne, hz, Padic.valuation_one, zero_add]
  rw [he false (Or.inr hs), he true (Or.inl rfl)]
  exact h

/-- A complete opening. Every old factor is screened at every labelled
site, and new factors are screened on the regular part of the request. -/
structure Room (B : Phase m P T hA hK bound L) (s : Block) where
  fibres : FreshFibres m P
  used : B.fibres.Included fibres
  coverage : ∀ l ∈ s.required, (∃ p, m.role p = some l.role) ∨
    ∃ p, ∃ hp : p ∈ fibres.births.primes, fibres.role p hp = some l.role
  outside_regular : ∀ p (hp : p ∈ fibres.births.primes), p ∉ B.fibres.births.primes →
    ∃ l ∈ m.missing s.required, fibres.role p hp = some l.role
  pending_orders : ∀ p (hp : p ∈ fibres.births.primes), p ∉ B.fibres.births.primes →
    ∀ r, fibres.role p hp = some r → ∀ i : A, Orders (fibres.births.site p hp) r i.val
  old_orders : ∀ p (hp : p ∈ fibres.births.primes) r,
    fibres.role p hp = some r → ∀ i : K, Orders (fibres.births.site p hp) r i.val
  above : ∀ p ∈ fibres.births.primes, limit hA hK bound < p.val

theorem finish (s : Block) : Nonempty (Room B s) := by
  have hall : HorizontalSet (K ∪ A) := by
    intro f hf
    exact (Finset.mem_union.mp hf).elim (hK f) (hA f)
  obtain ⟨a, hd, ha, hcover⟩ := s.reserve_regular m P (K ∪ A) hall B.fibres.births.primes (limit hA hK bound)
  let u := a.unionAux B.fibres hd B.auxiliary.no_regular
  have hl : a.Included u := a.included_union_left _ hd B.auxiliary
  have hr : B.fibres.Included u := a.included_union_right _ hd B.auxiliary
  have regular (p : PrimeIndex) (hp : p ∈ a.births.primes) (r : FibreRole)
      (h : u.role p (hl p hp).choose = some r) (f : ℚ[X]) (hf : f ∈ K ∪ A) :
      Orders (u.births.site p (hl p hp).choose) r f := by
    obtain ⟨l, _, he, _, hs⟩ := ha p hp
    obtain hh := Option.some.inj (h.symm.trans ((hl p hp).choose_spec.1.trans he))
    rw [(hl p hp).choose_spec.2, hh]
    exact hs f hf
  refine ⟨⟨u, hr, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro l h
    rcases hcover l h with hold | ⟨p,hp,_,he,_⟩
    · exact Or.inl hold
    · exact Or.inr ⟨p,(hl p hp).choose,(hl p hp).choose_spec.1.trans he⟩
  · intro p hp hnew
    have hreg := (Finset.mem_union.mp hp).resolve_right hnew
    obtain ⟨l,hm,he,_,_⟩ := ha p hreg
    exact ⟨l,hm,(hl p hreg).choose_spec.1.trans he⟩
  · intro p hp hnew r h i
    exact regular p ((Finset.mem_union.mp hp).resolve_right hnew) r h i.val
      (Finset.mem_union_right _ i.property)
  · intro p hp r h i
    rcases Finset.mem_union.mp hp with hreg | haux
    · exact regular p hreg r h i.val (Finset.mem_union_left _ i.property)
    · obtain ⟨k,j,e,he⟩ := B.auxiliary p haux
      have heq := Option.some.inj (h.symm.trans ((hr p haux).choose_spec.1.trans he))
      rw [(hr p haux).choose_spec.2, heq]
      have hu (b : Bool) := screened_norm (B.fibres.births.site p haux) hK i (dvd_product hK i)
        (B.screens p haux) ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt (B.above p haux))) b
      have hz (b : Bool) := EvaluationChoices.valuation_eq_of_norm_eq p.val
        (norm_ne_zero_iff.mp (show ‖aeval ((B.fibres.births.site p haux).branch b) i.val‖ ≠ 0
          from (hu b) ▸ one_ne_zero)) (one_ne_zero : (1 : ℚ_[p.val]) ≠ 0) ((hu b).trans norm_one.symm)
      exact ⟨by simpa [forecastOrder] using hz false, by simpa using hz true⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hreg | haux
    · obtain ⟨_,_,_,h',_⟩ := ha p hreg
      exact h'
    · exact B.above p haux

/-- A request may add ordinary guard-only primes, for instance those
needed by the modulus at a reserved split. -/
structure Installed (a b : FreshFibres m P) : Prop where
  included : a.Included b
  unlabelled : ∀ p (hp : p ∈ b.births.primes), p ∉ a.births.primes → b.role p hp = none

theorem installed_self (a : FreshFibres m P) : Installed a a :=
  ⟨fun _ hp => ⟨hp,rfl,rfl⟩, fun _ hp h => (h hp).elim⟩

theorem installed_coverPrimes (a : FreshFibres m P) (needed : Finset PrimeIndex) :
    Installed a (a.coverPrimes needed) :=
  ⟨a.coverPrimes_old needed, fun p hp hn => (a.coverPrimes_extra needed p hp hn).1⟩

/-- A paired auxiliary birth occurs exactly when its explicit weighted
column occurs in the computed prefix list. -/
theorem Room.auxiliary_iff {B : Phase m P T hA hK bound L} {s : Block} (R : Room B s)
    (b : FreshFibres m P) (use : Installed R.fibres b) (p : PrimeIndex) (k : Bool) (i : ℕ) (e : Bool) :
    (∃ hp : p ∈ b.births.primes, b.role p hp = some (.auxiliary k i e)) ↔
      .auxiliary p k i e ∈ columns B := by
  constructor
  · rintro ⟨hp,hr⟩
    by_cases hc : p ∈ R.fibres.births.primes
    · have hl := (use.included p hc).choose_spec.1.symm.trans hr
      by_cases h : p ∈ B.fibres.births.primes
      · exact (mem_columns B _).mpr ⟨⟨p,h⟩,k,i,e,(R.used p h).choose_spec.1.symm.trans hl,rfl⟩
      · obtain ⟨l,_,he⟩ := R.outside_regular p hc h
        rw [he] at hl
        cases hl
    · rw [use.unlabelled p hp hc] at hr
      cases hr
  · intro h
    obtain ⟨q,ch,j,ε,hr,he⟩ := (mem_columns B _).mp h
    obtain ⟨h₁,h₂,h₃,h₄⟩ := RawColumn.auxiliary.inj he
    subst p ch j ε
    obtain ⟨hp,hl,_⟩ := (R.used.trans use.included) q.val q.property
    exact ⟨hp,hl.trans hr⟩

theorem Room.old_model_orders {B : Phase m P T hA hK bound L} {s : Block}
    (R : Room B s) (b : FreshFibres m P) (use : Installed R.fibres b)
    (p : PrimeIndex) (hp : p ∈ b.births.primes) (r : FibreRole) (hr : b.role p hp = some r)
    (i : K) :
    (aeval ((b.births.site p hp).branch false) (models hK i)).valuation =
        forecastOrder (height i.val) (some r) ∧
      (aeval ((b.births.site p hp).branch true) (models hK i)).valuation = 0 := by
  by_cases h : p ∈ R.fibres.births.primes
  · obtain ⟨_, he, hs⟩ := use.included p h
    have hl := he.symm.trans hr
    have hp' := (R.fibres.paired p h).mpr (by rw [hl]; rfl)
    rw [hs]
    exact model_orders hp' i r
      (((le_max_right _ _).trans (le_max_right _ _)).trans_lt (R.above p h))
      (R.old_orders p h r hl i)
  · rw [use.unlabelled p hp h] at hr
    cases hr

/-- On the actual Driver successor the monic rational polynomial has its
prescribed mass in both channels, including when guard-only primes are added. -/
theorem Room.mass_after (D : Driver) (n : ℕ)
    {B : Phase (D.state n) ((chain D.requirements).approx n) (table D.requirements n)
      hA hK bound L} {s : Block} (R : Room B s)
    (use : Installed R.fibres (D.actualRequest n).toFreshFibres) (i : A) (k : Bool) :
    D.rationalMass (n+1) i.val (height i.val) k = height i.val k := by
  rw [show i.val = (member hA i).val from rfl, D.rationalMass_eq_model]
  apply B.mass_after_inclusion D n (R.used.trans use.included) _ i k
  intro j p hp haux r hr
  by_cases h : p ∈ R.fibres.births.primes
  · obtain ⟨_, he, hs⟩ := use.included p h
    have hl := he.symm.trans hr
    have hp' := (R.fibres.paired p h).mpr (by rw [hl]; rfl)
    rw [hs]
    exact model_orders hp' j r
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt (R.above p h))
      (R.pending_orders p h haux r hl j)
  · rw [use.unlabelled p hp h] at hr
    cases hr

end UnconditionalCounterexample.Variations.DyadicLedger.OpeningCalibration
