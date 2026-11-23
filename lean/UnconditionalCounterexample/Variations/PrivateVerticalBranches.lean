import UnconditionalCounterexample.Variations.VerticalBranchResidues
import UnconditionalCounterexample.Variations.PrivateGuardsRealized

/-! # Vertical height on the mixed ordinary and private intersection -/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MultiDomain MultivariateSelection GuardSupport FiniteVerticalFibres IntersectionDomain WithZero

variable {r d : ℕ} {c : Fin (r+1) → ℚ} {M : ℕ → Type*} (C : Config r d) (L : Rule r M c)
variable (primaryPrime : ℕ → PrimeIndex)
    (primary : ∀ n, LocalTuple (r+1) (Padic.mulValuation (p := (primaryPrime n).val)))
    (guard : ∀ p : PrimeIndex, ScreenedGuard r p)

private abbrev MixedIndex := (ℕ ⊕ PrimeIndex) ⊕ (ℕ × Bool)

private def mixedPrime : MixedIndex → PrimeIndex
  | .inl (.inl j) => primaryPrime j
  | .inl (.inr p) => p
  | .inr i => (family C L).prime i.1

/-- An integral tuple in the rational local field defines a rational branch. -/
private def rationalBranch {p : PrimeIndex} (x : LocalTuple (r+1) (Padic.mulValuation (p := p.val))) :
    FiniteVerticalFibres.Branch r p :=
  .rational (fun i => ⟨x.x i, by
    have equiv := Padic.norm_lt_norm_iff_mulValuation_lt (x := 1) (y := x.x i)
    simpa only [not_lt,norm_one,map_one] using (not_congr equiv).mpr (by simpa using x.integral i)⟩) x.independent

private def mixedBranch (i : MixedIndex) : FiniteVerticalFibres.Branch r (mixedPrime C L primaryPrime i) :=
  match i with
  | .inl (.inl j) => rationalBranch (primary j)
  | .inl (.inr p) => .guard (guard p)
  | .inr (n,false) => .rational _ ((family C L).sites n).private_independent
  | .inr (n,true) => .rational _ ((family C L).sites n).ordinary_independent

private theorem keys_injective (hinj : Function.Injective primaryPrime)
    (hdis : ∀ j n, primaryPrime j ≠ (family C L).prime n) :
    Function.Injective fun i => (mixedBranch C L primaryPrime primary guard i).key := by
  intro i j he
  have hp := congrArg Sigma.fst he
  have private_inj : Function.Injective (family C L).prime := fun _ _ e =>
    (family C L).prime_increasing.injective (congrArg Subtype.val e)
  rcases i with (i | p) | ⟨n,b⟩ <;> rcases j with (j | q) | ⟨m,e⟩
  · exact congrArg (fun j : ℕ => (Sum.inl (Sum.inl j) : MixedIndex)) (hinj hp)
  · change primaryPrime i = q at hp
    subst q
    simp [mixedPrime,mixedBranch,FiniteVerticalFibres.Branch.key,FiniteVerticalFibres.Branch.residue,rationalBranch] at he
  · exact (hdis i m hp).elim
  · change p = primaryPrime j at hp
    subst p
    simp [mixedPrime,mixedBranch,FiniteVerticalFibres.Branch.key,FiniteVerticalFibres.Branch.residue,rationalBranch] at he
  · exact congrArg (fun p : PrimeIndex => (Sum.inl (Sum.inr p) : MixedIndex)) hp
  · change p = (family C L).prime m at hp
    subst p
    cases e <;> simp [mixedPrime,mixedBranch,FiniteVerticalFibres.Branch.key,FiniteVerticalFibres.Branch.residue] at he
  · exact (hdis j n hp.symm).elim
  · change (family C L).prime n = q at hp
    subst q
    cases b <;> simp [mixedPrime,mixedBranch,FiniteVerticalFibres.Branch.key,FiniteVerticalFibres.Branch.residue] at he
  · have en : n = m := private_inj hp
    subst m
    cases b <;> cases e
    · rfl
    · have hn := ((family C L).sites n).distinct
      simp [mixedPrime,mixedBranch,FiniteVerticalFibres.Branch.key,FiniteVerticalFibres.Branch.residue] at he
      exact False.elim (hn (by exact he))
    · have hn := ((family C L).sites n).distinct.symm
      simp [mixedPrime,mixedBranch,FiniteVerticalFibres.Branch.key,FiniteVerticalFibres.Branch.residue] at he
      exact False.elim (hn (by exact he))
    · rfl

/-- The enlarged intersection has height one at every prime meeting the integers.
The public primary primes and the private primes are disjoint by their scheduling. -/
theorem mixed_vertical_height_one (B : Subring (FunctionField (r+1)))
    (v : ((ℕ ⊕ PrimeIndex) ⊕ (ℕ × Bool)) → Valuation (FunctionField (r+1)) ℤᵐ⁰)
    [IsFractionRing (intersection B v) (FunctionField (r+1))]
    (hp : ∀ j, v (.inl (.inl j)) = (primary j).valuation)
    (hg : ∀ p, v (.inl (.inr p)) = (guard p).tuple.valuation)
    (ha : ∀ j, v (.inr (j,false)) = (family C L).places.auxiliary j)
    (ho : ∀ j, v (.inr (j,true)) = (family C L).places.ordinary j)
    (hinj : Function.Injective primaryPrime) (hdis : ∀ j n, primaryPrime j ≠ (family C L).prime n)
    (hx : coordinate (r := r+1) 0 ∈ intersection B v)
    (hinv : ∀ p : PrimeIndex, (p.val : FunctionField (r+1))⁻¹ ∈ B)
    (t : PrimeSpectrum (intersection B v))
    (ht : ¬ Disjoint (integerDenominators (intersection B v) : Set (intersection B v)) t.asIdeal) :
    Order.height t = 1 := by
  apply vertical_height_of_branches B v (mixedPrime C L primaryPrime) (mixedBranch C L primaryPrime primary guard)
    _ (keys_injective C L primaryPrime primary guard hinj hdis) hx hinv t ht
  rintro ((j | p) | ⟨n,b⟩)
  · exact hp j
  · exact hg p
  · cases b with
    | false => exact ha n
    | true => exact ho n

end UnconditionalCounterexample.Variations.PrivateGuards.Live
