import UnconditionalCounterexample.Variations.MultivariateSelectionWords
import UnconditionalCounterexample.Variations.GuardTupleLifts
import UnconditionalCounterexample.Variations.MultiDomainPlaces
import UnconditionalCounterexample.Variations.MultiDomainPrimaryBirths
import UnconditionalCounterexample.PrimaryChoices

/-!
# Frozen multivariate sites for a finite prefix

New guards use the full finite unramified residue field; a new primary is
rational p-adic. The reserved prime never receives a primary. Each stage
adds two independent primaries and processes the next enumerated guard.
At the auxiliary prime the guard also avoids the new leading form.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations
open scoped Topology

structure ScreenedGuard (r : ℕ) (p : PrimeIndex) where
  degree : ℕ
  degree_prime : degree.Prime
  w : Fin (r+1) → WittVector p.val (GaloisField p.val degree)
  independent : AlgebraicIndependent ℚ (fun j => algebraMap _ (GuardUnramified.LocalField p.val (GaloisField p.val degree)) (w j))
  generates : Algebra.adjoin ℤ_[p.val] ({w 0} : Set (WittVector p.val (GaloisField p.val degree))) = ⊤
  outside : (w 0).coeff 0 ∉ Set.range (algebraMap (ZMod p.val) (GaloisField p.val degree))

variable {r : ℕ} {p : PrimeIndex}
abbrev ResiduePolys (r : ℕ) (p : PrimeIndex) := MvPolynomial (Fin (r+1)) (ZMod p.val)

def ScreenedGuard.avoids (G : ScreenedGuard r p) (f : ResiduePolys r p) :=
  aeval (fun j => (G.w j).coeff 0) f ≠ 0

def ScreenedGuard.tuple (G : ScreenedGuard r p) : MultiDomain.LocalTuple (r+1)
    (GuardUnramified.valuation p.val (GaloisField p.val G.degree)) :=
  ⟨_,G.independent,fun i => (GuardUnramified.integral_iff _ _ _).mpr ⟨G.w i,rfl⟩⟩

theorem exists_screened_guard (r : ℕ) (p : PrimeIndex) (S : Finset (ResiduePolys r p)) :
    ∃ G : ScreenedGuard r p, ∀ f ∈ S, f ≠ 0 → G.avoids f := by
  classical
  let S' := S.filter (· ≠ 0)
  obtain ⟨e,_,hp,a,_,hgen,hout,ha⟩ := GuardResidueTuples.exists_guard p.val r 1 S'
    (fun _ hf => (Finset.mem_filter.mp hf).2)
  let k := GaloisField p.val e
  obtain ⟨w,hw,hI⟩ := GuardUnramified.exists_lifts p.val k (r+1) a
  refine ⟨⟨e,hp,w,hI,GuardUnramified.adjoin_lift_eq_top p.val k _ ((hw 0) ▸ hgen),(hw 0) ▸ hout⟩,?_⟩
  intro f hf hzero
  change aeval (fun i => (w i).coeff 0) f ≠ 0
  rw [funext hw]
  exact ha f (Finset.mem_filter.mpr ⟨hf,hzero⟩)

/-- The reduction of any integral p-adic model; uniqueness makes it independent
of the choice of model. -/
def reduction (p : PrimeIndex) (f : Poly r) : ResiduePolys r p := by
  classical
  let φ := MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) (σ := Fin (r+1))
  let ψ := MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (σ := Fin (r+1))
  exact if h : ∃ Q, φ Q = ψ f then MvPolynomial.map PadicInt.toZMod h.choose else 0

theorem reduction_of_model {Q : MvPolynomial (Fin (r+1)) ℤ_[p.val]} {f : Poly r}
    (h : MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) f) :
    reduction p f = MvPolynomial.map PadicInt.toZMod Q := by
  classical
  have h' : ∃ Q, MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) Q = MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) f := ⟨Q,h⟩
  dsimp only [reduction]
  rw [dite_eq_left h']
  exact congrArg _ (map_injective _ (IsFractionRing.injective ℤ_[p.val] ℚ_[p.val]) (h'.choose_spec.trans h.symm))

/-- Growing guard tests independent of later subalgebras. -/
def guardTests (r n : ℕ) (p : PrimeIndex) : Finset (ResiduePolys r p) := by
  classical
  let e : ℕ → MultiDomain.IntPolys (r+1) := (exists_surjective_nat _).choose
  exact ((Finset.range (n+1)).image e).image (MvPolynomial.map (Int.castRingHom (ZMod p.val)))

theorem guardTests_cover (F : MultiDomain.IntPolys (r+1)) :
    ∃ N, ∀ n ≥ N, ∀ p : PrimeIndex, MvPolynomial.map (Int.castRingHom (ZMod p.val)) F ∈ guardTests r n p := by
  obtain ⟨i,hi⟩ := (exists_surjective_nat (MultiDomain.IntPolys (r+1))).choose_spec F
  exact ⟨i,fun n hn p => Finset.mem_image.mpr ⟨F, Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),hi⟩,rfl⟩⟩

structure Fibre (r : ℕ) (p : PrimeIndex) where
  guard : ScreenedGuard r p
  primary : Option (ℕ × MultiDomain.LocalTuple (r+1) (Padic.mulValuation (p := p.val)))

structure SiteTable (r : ℕ) where
  covered : Finset PrimeIndex
  fibre : (p : PrimeIndex) → p ∈ covered → Fibre r p

def SiteTable.empty (r : ℕ) : SiteTable r := ⟨∅,fun _ h => (Finset.notMem_empty _ h).elim⟩

def SiteTable.Extends (S T : SiteTable r) : Prop :=
  ∃ h : S.covered ⊆ T.covered, ∀ p (hp : p ∈ S.covered), T.fibre p (h hp) = S.fibre p hp

theorem SiteTable.Extends.trans {A B C : SiteTable r} (h : A.Extends B) (g : B.Extends C) : A.Extends C := by
  obtain ⟨hab,he⟩ := h
  obtain ⟨hbc,hf⟩ := g
  exact ⟨fun _ hp => hbc (hab hp), fun p hp => (hf p (hab hp)).trans (he p hp)⟩

def firstOrder (j : ℕ) : ℕ := if j = 0 then 2 else 1

/-- The new primaries are installed at labels 2n and 2n+1. Indexing by
the birth stage keeps their dependent field types throughout the recursion. -/
structure Batch (r n : ℕ) where
  previous : Finset (Poly r)
  first : MultiDomain.PrimaryBirth r (2*n) (firstOrder (2*n)) previous
  second : MultiDomain.PrimaryBirth r (2*n+1) (firstOrder (2*n+1)) previous
  processed : Finset PrimeIndex
  aux : PrimeIndex
  table : SiteTable r
  covered_eq : table.covered = insert aux processed

def screen (n : ℕ) (p : PrimeIndex) (old : Finset (Poly r)) (isAux : Bool) : Finset (ResiduePolys r p) := by
  classical
  let L : ResiduePolys r p := ∑ i : Fin (r+1), C ((n : ZMod p.val) ^ i.val) * X i
  exact guardTests r n p ∪ old.image (reduction p) ∪ (if isAux then {L} else ∅)

private def mark (p : PrimeIndex) {j k : ℕ} {old : Finset (Poly r)} (B : MultiDomain.PrimaryBirth r j k old)
    (h : B.prime = p) : ℕ × MultiDomain.LocalTuple (r+1) (Padic.mulValuation (p := p.val)) :=
  ⟨j, h ▸ B.tuple⟩

open scoped Classical in
structure Batch.Valid {n : ℕ} (B : Batch r n) (q : PrimeIndex) (S : SiteTable r) (old : Finset (Poly r)) : Prop where
  previous_eq : B.previous = old.filter (fun f => ¬ X 0 ∣ f)
  extends_old : S.Extends B.table
  copied : S.covered ⊆ B.processed
  reserved : q ∈ B.processed
  enumerated : PrimaryChoices.primes n ∈ B.processed
  aux_fresh : B.aux ∉ B.processed
  first_mem : B.first.prime ∈ B.processed
  second_mem : B.second.prime ∈ B.processed
  first_new : B.first.prime ∉ insert q S.covered
  second_new : B.second.prime ∉ insert B.first.prime (insert q S.covered)
  first_at : ∀ h, (B.table.fibre B.first.prime h).primary = some (mark _ B.first rfl)
  second_at : ∀ h, (B.table.fibre B.second.prime h).primary = some (mark _ B.second rfl)
  other_at : ∀ p h, p ∉ S.covered → p ≠ B.first.prime → p ≠ B.second.prime → (B.table.fibre p h).primary = none
  guards : ∀ p h, p ∉ S.covered → ∀ f ∈ screen n p old (decide (p = B.aux)), f ≠ 0 → (B.table.fibre p h).guard.avoids f

/-- The full finite table, including the auxiliary guard, is chosen before the
stage polynomial. All old fibres are copied as elements of their dependent
types. -/
private def makeBatch (q : PrimeIndex) (n : ℕ) (S : SiteTable r) (old : Finset (Poly r)) (extra : Finset PrimeIndex) :
    {B : Batch r n // B.Valid q S old ∧ extra ⊆ B.processed ∧ B.first.prime ∉ extra ∧ B.second.prime ∉ extra} := by
  classical
  let old' := old.filter (fun f => ¬ X 0 ∣ f)
  have good (f : Poly r) (hf : f ∈ old') : ¬ X 0 ∣ f := (Finset.mem_filter.mp hf).2
  let used := insert q (insert (PrimaryChoices.primes n) (S.covered ∪ extra))
  have new (j : ℕ) (u : Finset PrimeIndex) := MultiDomain.exists_primary j (firstOrder j)
    (by dsimp [firstOrder]; split <;> decide) old' good u n
  let b := (new (2*n) used).choose
  let c := (new (2*n+1) (insert b.prime used)).choose
  let processed := insert c.prime (insert b.prime used)
  let ell := (GuardStages.exists_fresh_prime processed n).choose
  let covered := insert ell processed
  let guards (p : PrimeIndex) := (exists_screened_guard r p (screen n p old (decide (p = ell)))).choose
  let atPrime (p : PrimeIndex) : Fibre r p :=
    ⟨guards p, if hb : b.prime = p then some (mark p b hb) else
      if hc : c.prime = p then some (mark p c hc) else none⟩
  let T : SiteTable r := ⟨covered, fun p _ => if hp : p ∈ S.covered then S.fibre p hp else atPrime p⟩
  let B : Batch r n := ⟨old',b,c,processed,ell,T,rfl⟩
  have hb := (new (2*n) used).choose_spec.2
  have hc := (new (2*n+1) (insert b.prime used)).choose_spec.2
  change b.prime ∉ used at hb
  change c.prime ∉ insert b.prime used at hc
  have hb0 : b.prime ∉ S.covered := fun hp => hb (by simp [used,hp])
  have hc0 : c.prime ∉ S.covered := fun hp => hc (by simp [used,hp])
  have hcb : c.prime ≠ b.prime := fun he => hc (he ▸ Finset.mem_insert_self _ _)
  have hsub : S.covered ⊆ insert (PrimaryChoices.primes n) (S.covered ∪ extra) :=
    fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
  refine ⟨B,?_, fun p hp => ?_, fun hp => hb ?_, fun hp => hc ?_⟩
  rotate_left
  · simp [B,processed,used,hp]
  · change b.prime ∈ extra at hp
    simp [used,hp]
  · change c.prime ∈ extra at hp
    simp [used,hp]
  refine ⟨rfl,⟨fun p hp => ?_,fun p hp => ?_⟩,fun p hp => ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [B,T,covered,processed,used, hp]
  · simp [B,T,hp]
  · simp [B,processed,used, hp]
  · simp [B,processed,used]
  · simp [B,processed,used]
  · exact (GuardStages.exists_fresh_prime processed n).choose_spec.2
  · simp [B,processed]
  · simp [B,processed]
  · change b.prime ∉ insert q S.covered
    intro h
    exact hb (Finset.insert_subset_insert q hsub h)
  · change c.prime ∉ insert b.prime (insert q S.covered)
    intro h
    exact hc (Finset.insert_subset_insert b.prime
      (Finset.insert_subset_insert q hsub) h)
  · intro h
    simp [B,T,hb0,atPrime]
  · intro h
    simp [B,T,hc0,atPrime,Ne.symm hcb]
  · intro p h hp hbp hcp
    simp [B,T,atPrime,hp,Ne.symm hbp,Ne.symm hcp]
  · intro p _ hp f hf hne
    change (if h : p ∈ S.covered then S.fibre p h else atPrime p).guard.avoids f
    rw [dite_eq_right hp]
    exact (exists_screened_guard r p _).choose_spec f hf hne

def batchWithExtra (q : PrimeIndex) (n : ℕ) (S : SiteTable r) (old : Finset (Poly r)) (extra : Finset PrimeIndex) : Batch r n :=
  (makeBatch q n S old extra).val

theorem batchWithExtra_spec (q : PrimeIndex) (n : ℕ) (S : SiteTable r) (old : Finset (Poly r)) (extra : Finset PrimeIndex) :
    let B := batchWithExtra q n S old extra
    B.Valid q S old ∧ extra ⊆ B.processed ∧ B.first.prime ∉ extra ∧ B.second.prime ∉ extra :=
  (makeBatch q n S old extra).property

def batch (q : PrimeIndex) (n : ℕ) (S : SiteTable r) (old : Finset (Poly r)) : Batch r n :=
  batchWithExtra q n S old ∅

theorem batch_valid (q : PrimeIndex) (n : ℕ) (S : SiteTable r) (old : Finset (Poly r)) :
    (batch q n S old).Valid q S old := (batchWithExtra_spec q n S old ∅).1

end UnconditionalCounterexample.MultivariateSelection
