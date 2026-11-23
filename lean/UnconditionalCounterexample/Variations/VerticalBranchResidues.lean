import UnconditionalCounterexample.Variations.FiniteVerticalFibres
import UnconditionalCounterexample.Variations.MultivariateSelectionGuards
import UnconditionalCounterexample.Variations.PrivateGuardsPair

/-! # Residue tests distinguishing the actual branches of a rational-prime fibre

Subtracting an integer from the first coordinate distinguishes two rational
residues and separates each rational branch from the screened unramified one.
These tests take place on the common rational function field.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.FiniteVerticalFibres

open WithZero GuardSupport MultiDomain MultivariateSelection IntersectionStalks IntersectionDomain

variable {r : ℕ} {p : PrimeIndex}

/-- The two kinds of branches appearing over a rational prime. -/
inductive Branch (r : ℕ) (p : PrimeIndex)
  | rational (x : Fin (r+1) → ℤ_[p.val]) (independent : AlgebraicIndependent ℚ (fun i => (x i).val))
  | guard (g : ScreenedGuard r p)

namespace Branch

def valuation : Branch r p → Valuation (FunctionField (r+1)) ℤᵐ⁰
  | .rational x h => PrivateGuards.place p x h
  | .guard g => g.tuple.valuation

/-- The guard has first coordinate outside the rational residue field. -/
def residue : Branch r p → Option (ZMod p.val)
  | .rational x _ => some (PadicInt.toZMod (x 0))
  | .guard _ => none

theorem normalized (b : Branch r p) : b.valuation (p.val : FunctionField (r+1)) = WithZero.exp (-1) := by
  cases b with
  | rational x h => exact EvaluationDVR.valuation_prime _ _
  | guard g => exact (g.tuple.valuation_natCast p.val).trans (GuardUnramified.valuation_prime _ _)

theorem finite_residue (b : Branch r p) : Finite (IsLocalRing.ResidueField b.valuation.valuationSubring) := by
  cases b with
  | rational x h => exact Finite.of_injective _ (EvaluationDVR.residueEquiv p.val (IndependentTuples.evaluation _ h)).injective
  | guard g =>
    let := MultiDomain.finite_witt_residue p.val (GaloisField p.val g.degree)
    exact MultiDomain.finite_residue_comap (GuardUnramified.valuation p.val (GaloisField p.val g.degree)) (IndependentTuples.evaluation _ g.independent)

/-- The center contains the first coordinate minus an integer precisely on the
rational branches with that residue. -/
theorem translate_lt_one (b : Branch r p) (n : ℕ) :
    b.valuation (coordinate (r := r+1) 0 - (n : FunctionField (r+1))) < 1 ↔ b.residue = some (n : ZMod p.val) := by
  cases b with
  | rational x h =>
    change Padic.mulValuation (IndependentTuples.evaluation _ h (coordinate (r := r+1) 0 - (n : FunctionField (r+1)))) < 1 ↔
      some (PadicInt.toZMod (x 0)) = some (n : ZMod p.val)
    rw [map_sub,map_natCast,coordinate,IndependentTuples.evaluation_variable,Option.some.injEq]
    have e := Padic.norm_lt_norm_iff_mulValuation_lt (x := (x 0).val - (n : ℚ_[p.val])) (y := 1)
    rw [norm_one,map_one] at e
    rw [← e]
    change ‖x 0 - (n : ℤ_[p.val])‖ < 1 ↔ _
    rw [← PadicInt.not_isUnit_iff,padicInt_isUnit_iff_toZMod_ne_zero,not_not,map_sub,map_natCast,sub_eq_zero]
  | guard g =>
    let f : Poly r := MvPolynomial.X 0 - (n : Poly r)
    let Q : MvPolynomial (Fin (r+1)) ℤ_[p.val] := MvPolynomial.X 0 - (n : MvPolynomial (Fin (r+1)) ℤ_[p.val])
    have hQ : MvPolynomial.map (algebraMap ℤ_[p.val] ℚ_[p.val]) Q =
        MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) f := by simp [Q,f]
    have hf := g.unit_of_model f Q hQ (by
      rw [reduction_of_model hQ]
      change MvPolynomial.aeval (fun j => (g.w j).coeff 0) (MvPolynomial.map PadicInt.toZMod Q) ≠ 0
      simp only [Q,map_sub,MvPolynomial.map_X,map_natCast,MvPolynomial.aeval_X,sub_ne_zero]
      exact fun e => g.outside ⟨(n : ZMod p.val), (map_natCast _ _).trans e.symm⟩)
    simp only [f,map_sub,map_natCast] at hf
    simp only [residue,reduceCtorEq,iff_false]
    change ¬ g.tuple.valuation (coordinate (r := r+1) 0 - (n : FunctionField (r+1))) < 1
    exact (by rw [show g.tuple.valuation (coordinate (r := r+1) 0 - (n : FunctionField (r+1))) = 1 from hf]; exact lt_irrefl _)

theorem center_ne_of_residue_ne {ι : Type*} {B : Subring (FunctionField (r+1))}
    {v : ι → Valuation (FunctionField (r+1)) ℤᵐ⁰} (i j : ι)
    (a b : Branch r p) (ha : v i = a.valuation) (hb : v j = b.valuation)
    (hx : coordinate (r := r+1) 0 ∈ intersection B v) (hne : a.residue ≠ b.residue) :
    center B v i ≠ center B v j := by
  intro hc
  have he (n : ℕ) : a.residue = some (n : ZMod p.val) ↔ b.residue = some (n : ZMod p.val) := by
    let z : intersection B v := ⟨coordinate (r := r+1) 0 - (n : FunctionField (r+1)),(intersection B v).sub_mem hx (show (n : FunctionField (r+1)) ∈ intersection B v from natCast_mem _ _)⟩
    rw [← a.translate_lt_one,← b.translate_lt_one,← ha,← hb]
    have h := (mem_center B v i z).symm.trans ((congrArg (fun I : Ideal (intersection B v) => z ∈ I) hc).to_iff.trans (mem_center B v j z))
    exact h
  apply hne
  cases ea : a.residue with
  | some y =>
    have h := he y.val
    rw [ZMod.natCast_zmod_val] at h
    exact (h.mp ea).symm
  | none =>
    cases eb : b.residue with
    | none => rfl
    | some y =>
      have h := he y.val
      rw [ZMod.natCast_zmod_val] at h
      simp [ea] at h
      exact (h eb).elim

private theorem valuation_cast {p q : PrimeIndex} (e : p = q) (a : Branch r p) :
    (e ▸ a : Branch r q).valuation = a.valuation := by cases e; rfl

def key (a : Branch r p) : Σ q : PrimeIndex, Option (ZMod q.val) := ⟨p,a.residue⟩

private theorem key_cast {p q : PrimeIndex} (e : p = q) (a : Branch r p) :
    (e ▸ a : Branch r q).key = a.key := by cases e; rfl

end Branch

/-- A family of actual rational and unramified branches gives a DVR at every
vertical prime if the first-coordinate residues distinguish its branches. -/
theorem vertical_height_of_branches {ι : Type*} (B : Subring (FunctionField (r+1)))
    (v : ι → Valuation (FunctionField (r+1)) ℤᵐ⁰)
    [IsFractionRing (intersection B v) (FunctionField (r+1))]
    (prime : ι → PrimeIndex) (b : ∀ i, Branch r (prime i))
    (hv : ∀ i, v i = (b i).valuation)
    (hinj : Function.Injective (fun i => (b i).key))
    (hx : coordinate (r := r+1) 0 ∈ intersection B v)
    (hinv : ∀ p : PrimeIndex, (p.val : FunctionField (r+1))⁻¹ ∈ B)
    (t : PrimeSpectrum (intersection B v))
    (ht : ¬ Disjoint (integerDenominators (intersection B v) : Set (intersection B v)) t.asIdeal) :
    Order.height t = 1 := by
  classical
  have hf (p : PrimeIndex) : Set.Finite {i | prime i = p} := by
    apply ((Set.finite_range (fun z : Option (ZMod p.val) => (⟨p,z⟩ : Σ q : PrimeIndex, Option (ZMod q.val)))).preimage hinj.injOn).subset
    intro i hi
    change prime i = p at hi
    subst p
    exact ⟨(b i).residue,rfl⟩
  let F : Fibres B v := {
    prime := prime
    fibre := fun p => (hf p).toFinset
    mem := by simp
    normalized := fun i => hv i ▸ (b i).normalized
    inv_mem := hinv }
  apply F.vertical_height_one _ _ t ht
  · intro i
    have he : Finite (IsLocalRing.ResidueField (v i).valuationSubring) := hv i ▸ (b i).finite_residue
    exact MultiDomain.maximal_center_of_finite_residue _ _ _
  · intro i j hij hc
    change prime j = prime i at hij
    let c : Branch r (prime i) := hij ▸ b j
    have haj : v j = c.valuation := (hv j).trans (Branch.valuation_cast hij (b j)).symm
    have e : c.residue = (b i).residue := by
      by_contra hn
      exact Branch.center_ne_of_residue_ne j i c (b i) haj (hv i) hx hn hc
    apply hinj
    exact (Branch.key_cast hij (b j)).symm.trans (congrArg (fun z => (⟨prime i,z⟩ : Σ q : PrimeIndex, Option (ZMod q.val))) e)

end UnconditionalCounterexample.Variations.FiniteVerticalFibres
