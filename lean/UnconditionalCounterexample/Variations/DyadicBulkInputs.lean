import UnconditionalCounterexample.Variations.DyadicBulkCalibration
import UnconditionalCounterexample.Variations.FreezingCalendar

/-!
# Primitive models for a round of horizontal calibration

The pending set is disjoint from the previously frozen factors and excludes
every old raw. Choosing one primitive integral model per monic irreducible
therefore supplies every coprimality and degree condition for the simultaneous
correction. One scalar cutoff transfers the model's unit tests on all future
sites back to the original rational polynomials.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.BulkInputs

open Polynomial GuardSupport RecursivePrefix Univariate FreezingCalendar

abbrev HorizontalSet (A : Finset ℚ[X]) := ∀ f ∈ A, f.Monic ∧ Irreducible f

/-- Named endpoints, the fair enumeration, and the factors of the split
numerator and denominator are all monic irreducibles. -/
theorem candidates_horizontal (r : ℕ) {extra : Finset ℚ[X]} (h : HorizontalSet extra) :
    HorizontalSet (candidates r extra) := by
  intro f hf
  rcases Finset.mem_union.mp hf with ha | he
  · rcases Finset.mem_union.mp ha with hn | hfac
    · cases r with
      | zero =>
        rcases Finset.mem_insert.mp hn with h | h
        · exact h ▸ zeroPoint.property
        · exact (Finset.mem_singleton.mp h) ▸ onePoint.property
      | succ r => exact (Finset.mem_singleton.mp hn) ▸ (enumeration r).property
    · have typed (g : ℚ[X]) (hg : f ∈ UniqueFactorizationMonoid.normalizedFactors g) :
          f.Monic ∧ Irreducible f := by
        by_cases hz : g = 0
        · simp [hz] at hg
        · have hi := (Polynomial.mem_normalizedFactors_iff hz).mp hg
          exact ⟨hi.2.1,hi.1⟩
      rcases Finset.mem_union.mp hfac with hnum | hden
      · exact typed _ (Multiset.mem_toFinset.mp hnum)
      · exact typed _ (Multiset.mem_toFinset.mp hden)
  · exact h f he

structure IntegerModel (f : Horizontal) where
  poly : ℤ[X]
  scalar : ℚ
  primitive : poly.IsPrimitive
  irreducible : Irreducible poly
  positive_degree : poly.natDegree ≠ 0
  scalar_ne : scalar ≠ 0
  identity : poly.map (algebraMap ℤ ℚ) = C scalar * f.val

def model (f : Horizontal) : IntegerModel f := by
  choose F q hF hI hD hq he using primitive_representative f
  exact ⟨F,q,hF,hI,hD,hq,he⟩

def member {A : Finset ℚ[X]} (hA : HorizontalSet A) (i : A) : Horizontal :=
  ⟨i.val,hA i.val i.property⟩

def models {A : Finset ℚ[X]} (hA : HorizontalSet A) (i : A) : ℤ[X] := (model (member hA i)).poly

def product {A : Finset ℚ[X]} (hA : HorizontalSet A) : ℤ[X] := ∏ i : A, models hA i

private theorem monic_coprime {f g : ℚ[X]} (hf : f.Monic ∧ Irreducible f)
    (hg : g.Monic ∧ Irreducible g) (h : f ≠ g) : IsCoprime f g :=
  (hf.2.isCoprime_or_dvd g).resolve_right fun hd =>
    h (eq_of_monic_of_associated hf.1 hg.1 (hf.2.associated_of_dvd hg.2 hd))

private theorem map_coprime (f g : Horizontal) (h : f.val ≠ g.val) :
    IsCoprime ((model f).poly.map (algebraMap ℤ ℚ)) ((model g).poly.map (algebraMap ℤ ℚ)) := by
  rw [(model f).identity, (model g).identity,
    isCoprime_mul_unit_left_left (isUnit_C.mpr (model f).scalar_ne.isUnit),
    isCoprime_mul_unit_left_right (isUnit_C.mpr (model g).scalar_ne.isUnit)]
  exact monic_coprime f.property g.property h

/-- The raw prefix has its own certified monic irreducibles, so unequal
polynomials have coprime primitive models without an additional test. -/
theorem inputs {n : ℕ} (P : Prefix n) {A K : Finset ℚ[X]} (hA : HorizontalSet A)
    (hK : HorizontalSet K) (disj : Disjoint A K)
    (fresh : ∀ i : A, ∀ j : Fin n, P.raw j ≠ i.val) :
    BulkCalibration.Inputs P (models hA) (product hK) where
  degree i := (model (member hA i)).positive_degree
  primitive i := (model (member hA i)).primitive
  irreducible i := (model (member hA i)).irreducible
  old_nonzero := Finset.prod_ne_zero_iff.mpr fun j _ => (model (member hK j)).irreducible.ne_zero
  old_coprime i := by
    rw [product, Polynomial.map_prod]
    apply IsCoprime.prod_right
    intro j _
    apply map_coprime (member hA i) (member hK j)
    exact fun he => Finset.disjoint_left.mp disj i.property ((show i.val = j.val from he) ▸ j.property)
  distinct i j h := map_coprime _ _ fun he => h (Subtype.ext he.symm)
  raw_coprime i j := by
    change IsCoprime ((model (member hA i)).poly.map (algebraMap ℤ ℚ)) _
    rw [(model (member hA i)).identity,
      isCoprime_mul_unit_left_left (isUnit_C.mpr (model (member hA i)).scalar_ne.isUnit)]
    exact monic_coprime (member hA i).property ⟨P.monic j, P.irreducible j⟩ (Ne.symm (fresh i j))

def scalarBound (f : Horizontal) : ℕ := max (model f).scalar.den (model f).scalar⁻¹.den

def cutoff {A : Finset ℚ[X]} (hA : HorizontalSet A) : ℕ :=
  Finset.univ.sup fun i : A => scalarBound (member hA i)

theorem unit_scalar (f : Horizontal) (p : PrimeIndex) (hp : scalarBound f < p.val) :
    ‖((model f).scalar : ℚ_[p.val])‖ = 1 := by
  let q := (model f).scalar
  have h (x : ℚ) (hd : x.den ≤ scalarBound f) : ‖(x : ℚ_[p.val])‖ ≤ 1 :=
    Padic.norm_rat_le_one (fun hdiv => (not_le_of_gt (hd.trans_lt hp)) (Nat.le_of_dvd x.den_pos hdiv))
  have h₁ := h q (le_max_left _ _)
  have h₂ := h q⁻¹ (le_max_right _ _)
  rw [Rat.cast_inv, norm_inv] at h₂
  exact h₁.antisymm ((inv_le_one₀ (norm_pos_iff.mpr (Rat.cast_ne_zero.mpr (model f).scalar_ne))).mp h₂)

theorem model_eval (f : Horizontal) (p : PrimeIndex) (x : ℚ_[p.val]) :
    aeval x (model f).poly = ((model f).scalar : ℚ_[p.val]) * aeval x f.val := by
  have h := congrArg (Polynomial.aeval x) (model f).identity
  have hc : (algebraMap ℚ ℚ_[p.val]).comp (algebraMap ℤ ℚ) = algebraMap ℤ ℚ_[p.val] := Subsingleton.elim _ _
  simp only [map_mul, aeval_C] at h
  rw [aeval_def, eval₂_map, hc, ← aeval_def] at h
  exact h

theorem model_norm {A : Finset ℚ[X]} (hA : HorizontalSet A) (i : A) (p : PrimeIndex)
    (hp : cutoff hA < p.val) (x : ℚ_[p.val]) : ‖aeval x (models hA i)‖ = ‖aeval x i.val‖ := by
  have h := (Finset.le_sup (f := fun j : A => scalarBound (member hA j)) (Finset.mem_univ i)).trans_lt hp
  rw [models, model_eval, norm_mul, unit_scalar _ _ h, one_mul]
  rfl

/-- Each old primitive model divides the screened product. -/
theorem dvd_product {A : Finset ℚ[X]} (hA : HorizontalSet A) (i : A) : models hA i ∣ product hA :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- Clearing the old product and the other fresh factors gives unit norms
for the original rational polynomial on either branch. -/
theorem screened_norm {p : PrimeIndex} (s : Site p) {A : Finset ℚ[X]} (hA : HorizontalSet A)
    (i : A) {G : ℤ[X]} (hd : models hA i ∣ G) (hG : ScreensAt s G)
    (hp : cutoff hA < p.val) (b : Bool) : ‖aeval (s.branch b) i.val‖ = 1 := by
  let x : ℤ_[p.val] := ⟨s.branch b,s.branch_integral b⟩
  have coe_eval (H : ℤ[X]) : aeval x.val H = ((aeval x H : ℤ_[p.val]) : ℚ_[p.val]) :=
    aeval_algebraMap_apply ℚ_[p.val] x H
  have u : IsUnit (aeval x G) := by
    apply PadicInt.isUnit_iff.mpr
    change ‖((aeval x G : ℤ_[p.val]) : ℚ_[p.val])‖ = 1
    rw [← coe_eval]
    exact hG b
  have uf := isUnit_of_dvd_unit ((aeval x).toRingHom.map_dvd hd) u
  rw [← model_norm hA i p hp]
  change ‖aeval x.val (models hA i)‖ = 1
  rw [coe_eval]
  exact PadicInt.isUnit_iff.mp uf

/-- The fair calendar's pending filter automatically gives disjointness and
freshness against the literal raw prefix. -/
theorem pending_inputs {n : ℕ} (P : Prefix n) (K A : Finset ℚ[X]) (hK : HorizontalSet K)
    (hA : HorizontalSet A) :
    let hPending : HorizontalSet (pending P K A) := fun f h => hA f (Finset.mem_filter.mp h).1
    BulkCalibration.Inputs P (models hPending) (product hK) := by
  intro hPending
  apply inputs P hPending hK
  · exact Finset.disjoint_left.mpr fun _ h => (Finset.mem_filter.mp h).2.1
  · exact fun i => pending_fresh P K A i.val i.property

end UnconditionalCounterexample.Variations.DyadicLedger.BulkInputs
