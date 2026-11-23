import UnconditionalCounterexample.Variations.MultivariateSelectionActual
import UnconditionalCounterexample.Variations.MultivariateGeometry

/-!
# The two concrete arithmetic schedules in positive transcendence degree

The rational point is the first coordinate vector, and the reserved prime
is two. Both schedules protect that point and the origin. Only the upper
schedule imposes its extra rational evaluation over the reserved prime.
-/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain

def reservedPrime : PrimeIndex := ⟨2,Nat.prime_two⟩

abbrev actualLocal (r : ℕ) (upper : Bool) := actualPrescription reservedPrime (flagPoint r) upper

abbrev actualRaw (r : ℕ) (upper : Bool) := siteRaw (actualLocal r upper) (standardGeometry r)

abbrev actualPlaces (r : ℕ) (upper : Bool) := places (actualLocal r upper) (standardGeometry r)

def actualData (r : ℕ) (upper : Bool) : Data (r+1) :=
  (actualPlaces r upper).data (actualRaw r upper) (fun i => (raw_irreducible _ i).ne_zero)

theorem actual_regular_origin (r : ℕ) (upper : Bool) (n : ℕ) : ¬ X 0 ∣ actualRaw r upper n :=
  raw_not_divisible_first _ n

theorem actual_regular_point (r : ℕ) (upper : Bool) (n : ℕ) :
    eval (flagPoint r) (actualRaw r upper n) ≠ 0 :=
  raw_at_flagPoint _ n

theorem actual_stage (r : ℕ) (upper : Bool) (n : ℕ) :
    let L := actualLocal r upper
    let G := standardGeometry r
    let h := (fun j : Fin n => siteChain L G j.val)
    ∀ v : (allocate reservedPrime n h).processed, ∃ N : ℕ,
      (permanentFibre L G v.val).Tests (flagPoint r) (withPoint upper reservedPrime v.val) h N
        (MvPolynomial.map (algebraMap ℚ ℚ_[v.val.val]) (actualRaw r upper n)) :=
  selected_tests reservedPrime (flagPoint r) upper (standardGeometry r) (by classical exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) n

end UnconditionalCounterexample.MultivariateSelection
