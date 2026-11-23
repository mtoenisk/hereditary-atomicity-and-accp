import UnconditionalCounterexample.Variations.PrivateGuardsLive
import UnconditionalCounterexample.Variations.MultivariateSelectionFrozen
import UnconditionalCounterexample.Variations.MultivariateSelectionBadPrimes

/-!
# Public-prime allocation on the chronological punctured history

The public table inherits each old site. New primaries screen every earlier
main and puncture. Private primes and exceptional primes of all preceding
puncture polynomials enter the ordinary table before the next main choice.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection

variable {r n : ℕ} {M : ℕ → Type*}

def oldPolys (h : History r M n) : Finset (Poly r) := by
  classical
  exact Finset.univ.image (fun i => (h i).entry.raw i.val) ∪ Finset.univ.image (fun i => (h i).puncture)

def extraPrimes (h : History r M n) : Finset PrimeIndex := by
  classical
  exact Finset.univ.image (fun i => (h i).prime) ∪ Finset.univ.biUnion (fun i => badPrimes (h i).puncture)

theorem extra_private (h : History r M n) (i : Fin n) : (h i).prime ∈ extraPrimes h :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem extra_bad (h : History r M n) (i : Fin n) {p : PrimeIndex} (hp : p ∈ badPrimes (h i).puncture) :
    p ∈ extraPrimes h :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hp⟩)

def liveBatch (q : PrimeIndex) (n : ℕ) (h : History r (Batch r) n) : Batch r n :=
  batchWithExtra q n (priorTable n (fun i => (h i).entry)) (oldPolys h) (extraPrimes h)

theorem liveBatch_valid (q : PrimeIndex) (n : ℕ) (h : History r (Batch r) n) :
    (liveBatch q n h).Valid q (priorTable n (fun i => (h i).entry)) (oldPolys h) :=
  (batchWithExtra_spec ..).1

theorem liveBatch_extra (q : PrimeIndex) (n : ℕ) (h : History r (Batch r) n) :
    extraPrimes h ⊆ (liveBatch q n h).processed ∧ (liveBatch q n h).first.prime ∉ extraPrimes h ∧
      (liveBatch q n h).second.prime ∉ extraPrimes h :=
  (batchWithExtra_spec ..).2

end UnconditionalCounterexample.Variations.PrivateGuards.Live
