import UnconditionalCounterexample.Variations.MultivariateSelectionFrozen
import UnconditionalCounterexample.Variations.MultiDomainFibreTargets
import UnconditionalCounterexample.Variations.DimensionRecoveryStage

/-!
# The simultaneous local and global multivariate stage construction

The local interpolation target uses the actual frozen places and preceding
normalized raw factors. Its analytic neighborhood imposes all scales and
all localized word gradients along the same permanent finite set of ideal
generators. At a protected rational point every earlier denominator survives.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain MultivariateInfinity
open scoped Topology

variable {r n : ℕ} {p : PrimeIndex}

namespace Fibre

variable (F : Fibre r p) (c : Fin (r+1) → ℚ) (extra : Bool)

abbrev generators := recoveryGenerators (K := ℚ_[p.val]) (F.guard.points (F.sidePoints c extra))

private theorem prime_ne : (p.val : ℚ_[p.val]) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero

def floor (n : ℕ) := (F.generators c extra).threshold p.val prime_ne Padic.norm_p_lt_one
  (F.guard.points_generate (F.sidePoints c extra)) (F.points_injective c extra) n

def localDen (h : SiteHistory r n) (w : triangularWords n h) : MvPolynomial (Fin (r+1)) ℚ_[p.val] :=
  MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) w.val.2

/-- The numerical tests on the full local polynomial, as returned by the
local schedule theorem with the single exponent N. -/
structure Tests (h : SiteHistory r n) (N : ℕ) (f : MvPolynomial (Fin (r+1)) ℚ_[p.val]) : Prop where
  values : ∀ i : F.Component extra, aeval (F.guard.points (F.sidePoints c extra) i) f ∈ F.targetSet h c extra i
  denominator : ∀ s ≤ n, ∀ w : triangularWords n h,
    RecoveryGenerators.denScale (p.val : ℚ_[p.val]) Padic.norm_p_lt_one s (localDen (p := p) h w) + n*n ≤
      ((F.generators c extra).genScale p.val Padic.norm_p_lt_one s + N) * w.val.1
  coefficients : ∀ s ≤ n, ∀ m,
    ‖(p.val : ℚ_[p.val]) ^ N * scaledCoefficient ((p.val : ℚ_[p.val])^s)
        ((p.val : ℚ_[p.val]) ^ ((F.generators c extra).genScale p.val Padic.norm_p_lt_one s)) m f -
      scaledCoefficient ((p.val : ℚ_[p.val])^s)
        ((p.val : ℚ_[p.val]) ^ ((F.generators c extra).genScale p.val Padic.norm_p_lt_one s)) m
          ((F.generators c extra).direction p.val n)‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n)
  gradients : ∀ i : F.Component extra, ∀ w : triangularWords n h, ∃ α : F.guard.Field i,
    α ≠ 0 ∧ ‖α⁻¹‖ ≤ ‖(p.val : ℚ_[p.val])‖^(n*n) ∧
    ‖α⁻¹ • residueWordGradient (F.guard.points (F.sidePoints c extra) i) f (localDen h w) w.val.1 -
      ∑ j : Fin (F.generators c extra).count,
        (algebraMap ℚ_[p.val] (F.guard.Field i) (p.val : ℚ_[p.val]) ^ n)^j.val •
          (fun l => aeval (F.guard.points (F.sidePoints c extra) i) (pderiv l ((F.generators c extra).gen j)))‖ ≤
          ‖(p.val : ℚ_[p.val])‖^(n*n)

abbrev Clean (c : Fin (r+1) → ℚ) (h : SiteHistory r n) := ∀ j : Fin n, eval c ((h j).raw j.val) ≠ 0

/-- A local target and its neighborhood are selected before the new rational
polynomial. All productive prefixes are precisely the ones supported at the
permanently reserved rational point. -/
structure Choice (h : SiteHistory r n) (d : ℕ) where
  N : ℕ
  target : MvPolynomial (Fin (r+1)) ℚ_[p.val]
  degree_lt : target.totalDegree < d
  U : Set (((Fin (r+1)) →₀ ℕ) → ℚ_[p.val])
  mem_nhds : U ∈ 𝓝 (fun m => target.coeff m)
  tests : Clean c h → ∀ x : MvPolynomial (Fin (r+1)) ℚ_[p.val], x.totalDegree < d → (fun m => x.coeff m) ∈ U →
    F.Tests c extra h N (vandermondeForm (r+1) n ^ d + x)

def choose (h : SiteHistory r n) (d : ℕ) (hd : F.floor c extra n ≤ d) (hd0 : 0 < d) : F.Choice c extra h d := by
  classical
  by_cases hc : Clean c h
  · let g := F.generators c extra
    let u := F.guard.points (F.sidePoints c extra)
    let H := localDen (p := p) h
    have hj (i : F.Component extra) (j : Fin n) : F.componentEval c extra i ((h j).raw j.val) ≠ 0 :=
      F.componentEval_ne_zero c extra i _ (fun he => hc j (he ▸ map_zero _)) (hc j)
    have hden (i : F.Component extra) (w : triangularWords n h) : aeval (u i) (H w) ≠ 0 := by
      change eval₂Hom _ _ (MvPolynomial.map _ _) ≠ 0
      rw [eval₂Hom_map_hom, ← IsScalarTower.algebraMap_eq ℚ ℚ_[p.val] (F.guard.Field i)]
      exact triangular_denominator_ne_zero _ h (hj i) _ w.property
    have ht : (vandermondeForm (k := ℚ_[p.val]) (r+1) n ^ d).totalDegree ≤ d := by
      apply (totalDegree_pow _ _).trans
      have hlin : (vandermondeForm (k := ℚ_[p.val]) (r+1) n).totalDegree ≤ 1 := by
        apply totalDegree_finsetSum_le
        intro j _
        exact (totalDegree_mul _ _).trans (by rw [totalDegree_C,totalDegree_X])
      simpa using Nat.mul_le_mul_left d hlin
    have h := g.exists_recovery_stage p.val prime_ne Padic.norm_p_lt_one (F.guard.points_generate _) (F.points_injective c extra)
      n d hd _ ht (F.target h c extra) (fun i => F.target_ne_zero h c extra i (hj i))
      (F.targetSet h c extra) (fun i => F.targetSet_mem h c extra i (hj i))
      H (fun w => w.val.1) (fun w => triangularWords_pos n _ _ w.property) hden
    let N := h.choose
    let Y := h.choose_spec.choose
    have hy := h.choose_spec.choose_spec
    let U := hy.2.choose
    have hu := hy.2.choose_spec
    refine ⟨N,Y,hy.1,U,hu.1,fun _ x hx hxU => ?_⟩
    obtain ⟨hvalues,hdenom,hcoeff,hgrad⟩ := hu.2 x hx hxU
    exact ⟨hvalues,hdenom,hcoeff,hgrad⟩
  · exact ⟨0,0,by simpa using hd0,Set.univ,Filter.univ_mem,fun h => (hc h).elim⟩

end Fibre

def batchFibre {n : ℕ} (B : Batch r n) (p : B.processed) : Fibre r p.val :=
  B.table.fibre p.val (B.covered_eq ▸ Finset.mem_insert_of_mem p.property)

/-- The ordinary and the upper-dimensional variants use separate schedules;
only the reserved prime receives the optional rational point. -/
def withPoint (upper : Bool) (q p : PrimeIndex) : Bool :=
  upper && decide (p = q)

def actualFloor (q : PrimeIndex) (c : Fin (r+1) → ℚ) (upper : Bool) (n : ℕ) (h : SiteHistory r n) : ℕ :=
  let B := allocate q n h
  max 1 (Finset.univ.sup (fun v : B.processed => (batchFibre B v).floor c (withPoint upper q v.val) n))

def actualChoice (q : PrimeIndex) (c : Fin (r+1) → ℚ) (upper : Bool) (n : ℕ) (h : SiteHistory r n)
    (d : ℕ) (hd : actualFloor q c upper n h ≤ d) (v : (allocate q n h).processed) :=
  (batchFibre _ v).choose c (withPoint upper q v.val) h d
    (((Finset.le_sup (f := fun z : (allocate q n h).processed =>
      (batchFibre _ z).floor c (withPoint upper q z.val) n) (Finset.mem_univ v)).trans (le_max_right _ _)).trans hd)
    ((le_max_left _ _).trans hd)

def actualPrescription (q : PrimeIndex) (c : Fin (r+1) → ℚ) (upper : Bool) : LocalPrescription r q where
  floor := actualFloor q c upper
  input n h d hd :=
    ⟨fun v => (actualChoice q c upper n h d hd v).target,fun v => (actualChoice q c upper n h d hd v).degree_lt,
     fun v => (actualChoice q c upper n h d hd v).U,fun v => (actualChoice q c upper n h d hd v).mem_nhds⟩

variable {q : PrimeIndex} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem clean_actual (L : LocalPrescription r q) (G : Geometry r K) (c : Fin (r+1) → ℚ)
    (hc : (fun i => algebraMap ℚ K (c i)) ∈ G.fixed) (n : ℕ) :
    Fibre.Clean c (fun j : Fin n => siteChain L G j.val) := by
  intro j hz
  apply fixed_survives (requirements L G) j.val _ hc
  change eval (fun i => algebraMap ℚ K (c i)) (MvPolynomial.map (algebraMap ℚ K) (siteRaw L G j.val)) = 0
  exact (map_eval (algebraMap ℚ K) c (siteRaw L G j.val)).symm.trans ((congrArg (algebraMap ℚ K) hz).trans (map_zero _))

theorem allocated_frozen (L : LocalPrescription r q) (G : Geometry r K) {n : ℕ}
    (v : (allocate q n (fun j : Fin n => siteChain L G j.val)).processed) :
    batchFibre _ v = permanentFibre L G v.val := by
  obtain ⟨p,hp⟩ := v
  have he (B : Batch r n) (hb : B = permanentBatch L G n) (hm : p ∈ B.table.covered) :
      B.table.fibre p hm = permanentFibre L G p := by
    subst B
    exact frozen L G _
  exact he _ (actual_batch L G n).symm _

set_option maxHeartbeats 450000 in
/-- Actual stage tests at every ordinary processed prime. All word and gradient
tests use the one saved exponent at that prime and stage. -/
theorem selected_tests (q : PrimeIndex) (c : Fin (r+1) → ℚ) (upper : Bool) (G : Geometry r K)
    (hc : (fun i => algebraMap ℚ K (c i)) ∈ G.fixed) (n : ℕ) :
    let L := actualPrescription q c upper
    let h := (fun j : Fin n => siteChain L G j.val)
    ∀ v : (allocate q n h).processed, ∃ N : ℕ,
      (permanentFibre L G v.val).Tests c (withPoint upper q v.val) h N
        (MvPolynomial.map (algebraMap ℚ ℚ_[v.val.val]) (siteRaw L G n)) := by
  intro L h v
  let R := requirements L G
  let d := chosenDegree R h
  let a := actualChoice q c upper n h d (threshold_le R h) v
  let Q := MvPolynomial.map (algebraMap ℚ ℚ_[v.val.val]) (chain R n).lower
  have acc := chain_accepted R n
  have hlt : Q.totalDegree < d := by
    apply lt_of_le_of_lt (b := (chain R n).lower.totalDegree)
    · exact Finset.sup_mono (f := fun e => e.sum fun (_ : Fin (r+1)) (n : ℕ) => n) (support_map_subset (algebraMap ℚ ℚ_[v.val.val]) (chain R n).lower)
    · exact (chain R n).lower_lt.trans_eq acc.degree_eq
  have hmem : (fun m => Q.coeff m) ∈ a.U := by
    have he : (fun m => Q.coeff m) = fun m => ((chain R n).lower.coeff m : ℚ_[v.val.val]) := by funext m; exact coeff_map _ _ _
    rw [he]
    exact acc.local_mem v
  have htest := a.tests (clean_actual L G c hc n) Q hlt hmem
  have hpoly : MvPolynomial.map (algebraMap ℚ ℚ_[v.val.val]) (siteRaw L G n) =
      vandermondeForm (r+1) n ^ d + Q := by
    change MvPolynomial.map _ (vandermondeForm (r+1) n ^ (chain R n).degree + (chain R n).lower) = _
    rw [map_add,map_pow,map_vandermonde,acc.degree_eq]
  exact ⟨a.N,((congrArg₂ (fun (F : Fibre r v.val) (f : MvPolynomial (Fin (r+1)) ℚ_[v.val.val]) =>
    F.Tests c (withPoint upper q v.val) h a.N f) (allocated_frozen L G v) hpoly.symm).mp htest)⟩

end UnconditionalCounterexample.MultivariateSelection
