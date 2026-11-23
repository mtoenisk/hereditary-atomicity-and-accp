import UnconditionalCounterexample.Variations.MultivariateSelectionOpen
import UnconditionalCounterexample.Variations.MultivariateListedWords
import UnconditionalCounterexample.GuardSupport

/-!
# Chronological choice of multivariate polynomials

The next word list and local neighborhoods may depend on the whole previous
prefix, including its frozen local data. The degree is chosen after its word
denominators. The accepted geometric tests are subsequently identified with the
tests of the permanent sequence.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport MultivariateListedWords MultivariateInfinity Filter
open scoped Topology

abbrev Poly (r : ℕ) := MvPolynomial (Fin (r+1)) ℚ

/-- A selected lower polynomial and its prescribed degree, together with
the local construction state stored at this stage. -/
structure Entry (r : ℕ) (M : Type*) where
  degree : ℕ
  lower : Poly r
  lower_lt : lower.totalDegree < degree
  memory : M

def Entry.raw {r : ℕ} {M : Type*} (x : Entry r M) (n : ℕ) : Poly r :=
  vandermondeForm (r+1) n ^ x.degree + x.lower

/-- Local, open input supplied after the chronological degree has been fixed. -/
structure LocalInput (r d : ℕ) where
  primes : Finset PrimeIndex
  aux : PrimeIndex
  fresh : aux ∉ primes
  target : ∀ v : primes, MvPolynomial (Fin (r+1)) ℚ_[v.val.val]
  target_lt : ∀ v, (target v).totalDegree < d
  neighborhood : ∀ v : primes, Set (((Fin (r+1)) →₀ ℕ) → ℚ_[v.val.val])
  mem_nhds : ∀ v, neighborhood v ∈ 𝓝 (fun m => (target v).coeff m)

variable (r : ℕ) (M : ℕ → Type*) (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]

abbrev History (n : ℕ) := (i : Fin n) → Entry r (M i.val)

/-- The data for local interpolation, words and finite geometry, with arbitrary
stagewise memory. Word denominators and the interpolation threshold are fixed
from the proper prefix. -/
structure Requirements where
  point : ℕ → Fin (r+1) → K
  primesEnumeration : ℕ → Ideal (MvPolynomial (Fin (r+1)) K)
  fixed : Finset (Fin (r+1) → K)
  words : ∀ n, History r M n → Finset (ℕ × Poly r)
  word_pos : ∀ n h w, w ∈ words n h → 0 < w.1
  threshold : ∀ n, History r M n → ℕ
  sites : ∀ n (h : History r M n) (d : ℕ), threshold n h ≤ d → LocalInput r d
  nextMemory : ∀ n (h : History r M n) (d : ℕ), threshold n h ≤ d → M n

variable {r M K}
variable (R : Requirements r M K)

def chosenDegree {n : ℕ} (h : History r M n) : ℕ :=
  max 2 (max (R.threshold n h) (1 + max
    (Finset.univ.sup (fun j : Fin n => (h j).degree)) ((R.words n h).sup (fun w => w.2.totalDegree))))

omit [CharZero K] [IsAlgClosed K] in
theorem threshold_le {n : ℕ} (h : History r M n) : R.threshold n h ≤ chosenDegree R h :=
  le_sup_of_le_right le_sup_left

private def fillDegree {n : ℕ} (h : History r M n) (i : ℕ) := if hi : i<n then (h ⟨i,hi⟩).degree else 2

private def fillLower {n : ℕ} (h : History r M n) (i : ℕ) : Poly r := if hi : i<n then (h ⟨i,hi⟩).lower else 0

private theorem fill_lt {n : ℕ} (h : History r M n) (i : ℕ) : (fillLower h i).totalDegree < fillDegree h i := by
  by_cases hi : i < n
  · simpa [fillDegree, fillLower, hi] using (h ⟨i,hi⟩).lower_lt
  · simp [fillDegree, fillLower, hi]

private def fillRaw {n : ℕ} (h : History r M n) (i : ℕ) : Poly r :=
  vandermondeForm (r+1) i ^ fillDegree h i + fillLower h i

private theorem spans (s : Finset ℕ) (hs : s.card = Fintype.card (Fin (r+1))) (j : Fin (r+1)) :
    ∃ c : ℕ → ℚ, X j = ∑ i ∈ s, C (c i) * vandermondeForm (r+1) i :=
  vandermondeForm_spans (r+1) s (by simpa using hs) j

omit [IsAlgClosed K] in
private theorem crossings_finite {n : ℕ} (h : History r M n) :
    (MultivariateSchedule.crossings (fun i => extend (K := K) (fillRaw h i)) (Fintype.card (Fin (r+1))) n).Finite :=
  finite_geometric_crossings _ _ (fillDegree h) (vandermonde_degree r)
    (fun i => ⟨_,fill_lt h i,rfl⟩) spans n

private def prefixTests {n : ℕ} (h : History r M n) :=
  stageTests R.point R.primesEnumeration R.fixed (fillRaw h) (fun _ => R.words n h) n (crossings_finite h)

/-- All constraints verified by a selected successor. -/
structure Accepted {n : ℕ} (h : History r M n) (x : Entry r (M n)) : Prop where
  degree_eq : x.degree = chosenDegree R h
  memory_eq : x.memory = R.nextMemory n h _ (threshold_le R h)
  irreducible : Irreducible (x.raw n)
  raw_degree : (x.raw n).totalDegree = x.degree
  supported : ∀ m, ∀ p : ℕ, p.Prime → p ∣ (x.lower.coeff m).den →
    ∃ v : (R.sites n h _ (threshold_le R h)).primes, p = v.val.val
  local_mem : ∀ v, (fun m => ((x.lower.coeff m : ℚ) : ℚ_[v.val.val])) ∈
    (R.sites n h _ (threshold_le R h)).neighborhood v
  residue : ∀ m, let ell := (R.sites n h _ (threshold_le R h)).aux
    HasAuxiliaryResidue ell.val (x.lower.coeff m) (if m = 0 then (ell.val : ZMod (ell.val ^ 2)) else 0)
  geometry : ∀ t ∈ prefixTests R h, t.Holds (extend (x.raw n))

theorem exists_successor {n : ℕ} (h : History r M n) : ∃ x, Accepted R h x := by
  classical
  let d := chosenDegree R h
  let L := R.sites n h d (threshold_le R h)
  let primes (v : L.primes) := v.val.val
  have hinj : Function.Injective primes := fun _ _ he => Subtype.ext (Subtype.ext he)
  have hfresh (v : L.primes) : primes v ≠ L.aux.val := fun he => L.fresh ((Subtype.ext he : v.val = L.aux) ▸ v.property)
  obtain ⟨q,hq,hi,hd,hs,hU,hr,hT⟩ := exists_vandermonde_stage r n primes hinj L.aux.val hfresh d
    (Nat.le_max_left ..) L.target L.target_lt L.neighborhood L.mem_nhds (prefixTests R h)
    (fun _ ht => stageTests_valid _ _ _ _ _ _ _ ht)
  exact ⟨⟨d,q,hq,R.nextMemory n h d (threshold_le R h)⟩,rfl,rfl,hi,hd,hs,hU,hr,hT⟩

def chain (n : ℕ) : Entry r (M n) :=
  Nat.strongRecOn n (fun _ rec => (exists_successor R (fun j => rec j.val j.isLt)).choose)

theorem chain_accepted (n : ℕ) : Accepted R (fun j : Fin n => chain R j.val) (chain R n) := by
  have he : chain R n = (exists_successor R (fun j : Fin n => chain R j.val)).choose :=
    Nat.strongRecOn_eq _ _
  rw [he]
  exact (exists_successor R _).choose_spec

def raw (n : ℕ) : Poly r := (chain R n).raw n

def words (n : ℕ) := R.words n (fun j : Fin n => chain R j.val)

theorem raw_irreducible (n : ℕ) : Irreducible (raw R n) := (chain_accepted R n).irreducible

theorem degree_strictMono : StrictMono (fun n => (raw R n).totalDegree) := by
  intro i j hij
  change ((chain R i).raw i).totalDegree < ((chain R j).raw j).totalDegree
  rw [(chain_accepted R i).raw_degree,(chain_accepted R j).raw_degree,(chain_accepted R j).degree_eq]
  let a := Finset.univ.sup (fun z : Fin j => (chain R z.val).degree)
  let b := (words R j).sup (fun w => w.2.totalDegree)
  have hi : (chain R i).degree ≤ a := Finset.le_sup (f := fun z : Fin j => (chain R z.val).degree)
    (Finset.mem_univ (⟨i,hij⟩ : Fin j))
  change (chain R i).degree < max 2 (max _ (1 + max a b))
  omega

theorem word_degree (n : ℕ) {w : ℕ × Poly r} (hw : w ∈ words R n) :
    w.2.totalDegree < w.1 * (chain R n).degree := by
  rw [(chain_accepted R n).degree_eq]
  apply lt_of_lt_of_le _ (Nat.le_mul_of_pos_left _ (R.word_pos n _ w hw))
  let a := Finset.univ.sup (fun z : Fin n => (chain R z.val).degree)
  let b := (words R n).sup (fun w => w.2.totalDegree)
  have hs : w.2.totalDegree ≤ b := Finset.le_sup (f := fun w : ℕ × Poly r => w.2.totalDegree) hw
  change w.2.totalDegree < max 2 (max _ (1 + max a b))
  omega

theorem raw_shape (n : ℕ) : ∃ q : Poly r, q.totalDegree < (chain R n).degree ∧
    raw R n = vandermondeForm (r+1) n ^ (chain R n).degree + q :=
  ⟨_,(chain R n).lower_lt,rfl⟩

theorem stage_tests (n : ℕ) :
    ∀ t ∈ stageTests R.point R.primesEnumeration R.fixed (raw R) (words R) n
      (finite_geometric_crossings _ _ _ (vandermonde_degree r) (raw_shape R) spans n),
      t.Holds (extend (raw R n)) := by
  have h := (chain_accepted R n).geometry
  have eq := stageTests_congr R.point R.primesEnumeration R.fixed (fillRaw (fun j : Fin n => chain R j.val))
    (raw R) (fun _ => words R n) (words R) n (fun i hi => by simp [fillRaw,fillDegree,fillLower,raw,Entry.raw,hi])
    rfl (crossings_finite _) (finite_geometric_crossings _ _ _ (vandermonde_degree r) (raw_shape R) spans n)
  exact eq ▸ h

end UnconditionalCounterexample.MultivariateSelection
