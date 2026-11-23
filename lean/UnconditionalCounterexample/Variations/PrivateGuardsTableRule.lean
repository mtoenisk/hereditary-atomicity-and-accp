import UnconditionalCounterexample.Variations.PrivateGuardsMainRule

/-!
# A main-selection rule on one combined table of processed primes

A previously installed private pair may share its prime with another local
component. The caller supplies one coefficient neighborhood per prime,
including all components, and the Eisenstein prime already allocated by the
table. The selected entry satisfies those same neighborhoods.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial Filter GuardSupport MultivariateSelection MultivariateInfinity
open scoped Topology

variable {r n : ℕ} {M : ℕ → Type*} {k : Type*} [Field k] [CharZero k]

structure TablePrescription (k : Type*) [Field k] (h : History r M n) where
  memory : M n
  degree : ℕ
  degree_two : 2 ≤ degree
  primes : Finset PrimeIndex
  reserved : Finset PrimeIndex
  aux : PrimeIndex
  fresh : aux ∉ primes
  old_private : ∀ j, (h j).prime ∈ primes
  opens : (v : primes) → OpenLower r degree v.val
  private_units : ∀ (j : Fin n) (u : Poly r), u.totalDegree < degree →
    (fun m => ((u.coeff m : ℚ) : ℚ_[(h j).prime.val])) ∈ (opens ⟨_,old_private j⟩).neighborhood →
    ∀ b, ‖aeval ((h j).pair.point b) (vandermondeForm (k := ℚ) (r+1) n ^ degree + u) /
      aeval ((h j).pair.point b) (oldDenominator h)‖ = 1
  geometry : Finset (MultivariateStage.Test k (Fin (r+1)))
  valid : ∀ t ∈ geometry, t.Valid

namespace TablePrescription
variable {h : History r M n}

def Satisfied (P : TablePrescription k h) (x : MainChoice r n (M n)) : Prop :=
  x.entry.degree = P.degree ∧ x.entry.memory = P.memory ∧ (x.entry.raw n).totalDegree = P.degree ∧
  x.reserved = insert P.aux (P.reserved ∪ P.primes) ∧
  (∀ v : P.primes, (fun m => ((x.entry.lower.coeff m : ℚ) : ℚ_[v.val.val])) ∈ (P.opens v).neighborhood) ∧
  (∀ t ∈ P.geometry, t.Holds (MvPolynomial.map (algebraMap ℚ k) (x.entry.raw n))) ∧
  (∀ m, HasAuxiliaryResidue P.aux.val (x.entry.lower.coeff m)
    (if m = 0 then (P.aux.val : ZMod (P.aux.val^2)) else 0)) ∧
  ∀ m p, p.Prime → p ∣ (x.entry.lower.coeff m).den → ∃ v : P.primes, p = v.val.val

end TablePrescription

def ruleOfTable (c : Fin (r+1) → ℚ) (P : ∀ n (h : History r M n)
    (_ : Function.Injective (fun j => (h j).prime.val)), TablePrescription k h) : Rule r M c where
  Accepts n h x := ∃ hinj, (P n h hinj).Satisfied x
  produces n h hinj := by
    classical
    let u := P n h hinj
    let τ := MultivariateStage.Test.point ((algebraMap ℚ k) ∘ c)
    let tests := insert τ u.geometry
    have valid (t) (ht : t ∈ tests) : t.Valid := (Finset.mem_insert.mp ht).elim
      (fun he ↦ he ▸ (show τ.Valid from trivial)) (u.valid t)
    let vals (i : u.primes) := i.val.val
    have hi : Function.Injective vals := fun _ _ he ↦ Subtype.ext (Subtype.ext he)
    have hf (i : u.primes) : vals i ≠ u.aux.val := fun e ↦
      u.fresh ((Subtype.ext e : i.val = u.aux) ▸ i.property)
    obtain ⟨q,hq,hIr,hdeg,hs,hU,hres,hGeo⟩ := exists_vandermonde_stage r n vals hi u.aux.val hf
      u.degree u.degree_two (fun i ↦ (u.opens i).target) (fun i ↦ (u.opens i).lower_lt)
      (fun i ↦ (u.opens i).neighborhood) (fun i ↦ (u.opens i).mem_nhds) tests valid
    let x : MainChoice r n (M n) := ⟨⟨u.degree,q,hq,u.memory⟩,hIr,insert u.aux (u.reserved ∪ u.primes)⟩
    refine ⟨x,?_,fun j ↦ u.private_units j q hq (hU ⟨_,u.old_private j⟩),hinj,rfl,rfl,hdeg,rfl,hU,
      fun t ht ↦ hGeo t (Finset.mem_insert_of_mem ht),hres,hs⟩
    have hn := hGeo τ (Finset.mem_insert_self _ _)
    change eval ((algebraMap ℚ k) ∘ c) (MvPolynomial.map (algebraMap ℚ k) (x.entry.raw n)) ≠ 0 at hn
    rw [← map_eval] at hn
    exact fun he ↦ hn (by rw [he,map_zero])

end UnconditionalCounterexample.Variations.PrivateGuards.Live
