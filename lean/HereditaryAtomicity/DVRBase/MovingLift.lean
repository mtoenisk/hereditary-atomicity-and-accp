import HereditaryAtomicity.DVRBase.MovingTower
import HereditaryAtomicity.DVRBase.Laurent
import HereditaryAtomicity.DVRBase.MovingWindows
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Linear Laurent lifts in the actual moving basis

A basis lift is coefficient-linear, not multiplicative. It is a section of
actual Laurent evaluation and fixes precisely the represented window monomials.
No algebraic independence of the evaluated generators is assumed.
-/

noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators

section Evaluation
variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- The existing Laurent evaluation, bundled with its coefficient linearity. -/
def evalAlgHom (y : Fin n → Fˣ) : Laurent K n →ₐ[K] F :=
  AddMonoidAlgebra.lift K F (Fin n → ℤ) (monomial y)

@[simp] theorem evalAlgHom_apply (y : Fin n → Fˣ) (f : Laurent K n) :
    evalAlgHom K y f = eval (algebraMap K F) y f := rfl

@[simp] theorem evalAlgHom_single (y : Fin n → Fˣ) (β : Fin n → ℤ) (c : K) :
    evalAlgHom K y (AddMonoidAlgebra.single β c) = c • monomial y (.ofAdd β) :=
  AddMonoidAlgebra.lift_single _ _ _
end Evaluation

section GenericLift
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
variable {D : Fin n → ℕ}

/-- The linear map sending each actual basis vector to its literal formal monomial. -/
def windowBasisLift (b : Module.Basis (WindowExponent D) K F) : F →ₗ[K] Laurent K n :=
  b.constr K (fun β => AddMonoidAlgebra.single β.val 1)

@[simp] theorem windowBasisLift_basis (b : Module.Basis (WindowExponent D) K F)
    (β : WindowExponent D) :
    windowBasisLift b (b β) = AddMonoidAlgebra.single β.val 1 :=
  b.constr_basis K _ β

@[simp] theorem windowBasisLift_smul_basis (b : Module.Basis (WindowExponent D) K F)
    (β : WindowExponent D) (c : K) :
    windowBasisLift b (c • b β) = AddMonoidAlgebra.single β.val c := by
  simp only [map_smul, windowBasisLift_basis, AddMonoidAlgebra.smul_single,
    smul_eq_mul, mul_one]

/-- The lift is the finite sum with the actual collected basis coordinates. -/
theorem windowBasisLift_eq_sum (b : Module.Basis (WindowExponent D) K F) (x : F) :
    windowBasisLift b x =
      ∑ β ∈ (b.repr x).support, AddMonoidAlgebra.single β.val (b.repr x β) := by
  simp only [windowBasisLift, Module.Basis.constr_apply, Finsupp.sum,
    AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- Evaluation of the linear basis lift recovers the original field element. -/
theorem eval_windowBasisLift (b : Module.Basis (WindowExponent D) K F)
    (y : Fin n → Fˣ) (hb : ∀ β, b β = monomial y (.ofAdd β.val)) (x : F) :
    evalAlgHom K y (windowBasisLift b x) = x := by
  have hmap : (evalAlgHom K y).toLinearMap.comp (windowBasisLift b) = LinearMap.id := by
    apply b.ext
    intro β
    change evalAlgHom K y (windowBasisLift b (b β)) = b β
    rw [windowBasisLift_basis, evalAlgHom_single, one_smul, hb]
  exact congrArg (fun f : F →ₗ[K] F => f x) hmap

/-- A literal window monomial is fixed by evaluation followed by the lift. -/
theorem windowBasisLift_eval_single (b : Module.Basis (WindowExponent D) K F)
    (y : Fin n → Fˣ) (hb : ∀ β, b β = monomial y (.ofAdd β.val))
    (β : Fin n → ℤ) (hβ : IsWindowExponent D β) (c : K) :
    windowBasisLift b (evalAlgHom K y (AddMonoidAlgebra.single β c)) =
      AddMonoidAlgebra.single β c := by
  rw [evalAlgHom_single, ← hb ⟨β, hβ⟩]
  exact windowBasisLift_smul_basis b ⟨β, hβ⟩ c

/-- Every Laurent polynomial supported on the window is fixed by lift-evaluation. -/
theorem windowBasisLift_eval_of_support (b : Module.Basis (WindowExponent D) K F)
    (y : Fin n → Fˣ) (hb : ∀ β, b β = monomial y (.ofAdd β.val))
    (f : Laurent K n) (hf : ∀ β, f.coeff β ≠ 0 → IsWindowExponent D β) :
    windowBasisLift b (evalAlgHom K y f) = f := by
  conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum]
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f, Finsupp.sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  exact windowBasisLift_eval_single b y hb β (hf β (Finsupp.mem_support_iff.mp hβ)) _

/-- The literal finite support of terms whose exponents fail the window. -/
def badWindowSupport (D : Fin n → ℕ) (f : Laurent K n) : Finset (Fin n → ℤ) := by
  classical
  exact f.coeff.support.filter (fun β => ¬ IsWindowExponent D β)

/-- The residual is the sum of residuals of precisely the terms outside the window. -/
theorem sub_windowBasisLift_eval_eq_sum (b : Module.Basis (WindowExponent D) K F)
    (y : Fin n → Fˣ) (hb : ∀ β, b β = monomial y (.ofAdd β.val)) (f : Laurent K n) :
    f - windowBasisLift b (evalAlgHom K y f) =
      ∑ β ∈ badWindowSupport D f,
        (AddMonoidAlgebra.single β (f.coeff β) -
          windowBasisLift b (evalAlgHom K y (AddMonoidAlgebra.single β (f.coeff β)))) := by
  classical
  have hsum : f - windowBasisLift b (evalAlgHom K y f) =
      ∑ β ∈ f.coeff.support, (AddMonoidAlgebra.single β (f.coeff β) -
        windowBasisLift b (evalAlgHom K y (AddMonoidAlgebra.single β (f.coeff β)))) := by
    have hf : (∑ β ∈ f.coeff.support, AddMonoidAlgebra.single β (f.coeff β)) = f :=
      AddMonoidAlgebra.sum_coeff_single f
    rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, hf]
  rw [hsum]
  symm
  unfold badWindowSupport
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro β hβ hnot
  have hw : IsWindowExponent D β := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hβ, hn⟩)
  rw [windowBasisLift_eval_single b y hb β hw, sub_self]

/-- An actual kernel element is a finite sum of bad-term residuals. -/
theorem kernel_eq_sum_sub_windowBasisLift_eval (b : Module.Basis (WindowExponent D) K F)
    (y : Fin n → Fˣ) (hb : ∀ β, b β = monomial y (.ofAdd β.val))
    (f : Laurent K n) (hf : evalAlgHom K y f = 0) :
    f = ∑ β ∈ badWindowSupport D f,
      (AddMonoidAlgebra.single β (f.coeff β) -
        windowBasisLift b (evalAlgHom K y (AddMonoidAlgebra.single β (f.coeff β)))) := by
  simpa only [hf, map_zero, sub_zero] using sub_windowBasisLift_eval_eq_sum b y hb f

/-- The literal coefficient at a window exponent is its basis coordinate. -/
@[simp] theorem windowBasisLift_coeff (b : Module.Basis (WindowExponent D) K F)
    (x : F) (β : WindowExponent D) :
    (windowBasisLift b x).coeff β.val = b.repr x β := by
  classical
  rw [windowBasisLift_eq_sum]
  simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply, Subtype.val_inj]
  exact Eq.symm

/-- Every nonzero collected coefficient of a lift has an exponent in the window. -/
theorem windowBasisLift_support (b : Module.Basis (WindowExponent D) K F)
    (x : F) (β : Fin n → ℤ) (hβ : (windowBasisLift b x).coeff β ≠ 0) :
    IsWindowExponent D β := by
  classical
  by_contra hn
  apply hβ
  rw [windowBasisLift_eq_sum]
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro γ _hγ
  have hne : γ.val ≠ β := by
    intro he
    exact hn (he ▸ γ.property)
  simp [hne]

end GenericLift

section PrefixExponents
variable {N l : ℕ}

/-- Embed a prefix exponent into the full list by putting zero on the suffix. -/
def extendPrefixExponent (_h : l ≤ N) : (Fin l → ℤ) →+ (Fin N → ℤ) where
  toFun γ i := if hi : i.val < l then γ ⟨i.val, hi⟩ else 0
  map_zero' := by funext i; simp
  map_add' γ δ := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> rfl

/-- The exponent of the peeling multiplier: negative tail pole on the prefix,
and the original fixed exponent on the suffix. -/
def peelingExponent (_h : l ≤ N) (β : Fin N → ℤ) : Fin N → ℤ :=
  fun i => if i.val < l then -poleTail β l else β i

/-- Multiplying an embedded prefix monomial by the peeling multiplier splices it. -/
theorem extendPrefix_add_peeling (h : l ≤ N) (β : Fin N → ℤ) (γ : Fin l → ℤ) :
    extendPrefixExponent h γ + peelingExponent h β = splicePrefix h β γ := by
  funext i
  simp only [extendPrefixExponent, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    peelingExponent, splicePrefix, Pi.add_apply]
  split_ifs <;> simp [sub_eq_add_neg]

/-- Different prefix exponents remain different after the common peeling shift. -/
theorem splicePrefix_injective (h : l ≤ N) (β : Fin N → ℤ) :
    Function.Injective (splicePrefix h β) := by
  intro γ δ he
  have hh := congrArg (shiftedPrefix h) he
  simpa only [shiftedPrefix_splicePrefix] using hh

/-- A valid suffix turns every smaller-window exponent into a literal full-window index. -/
def spliceWindowExponent (h : l ≤ N) (D : Fin N → ℕ) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (D i))
    (γ : WindowExponent (fun i => D (Fin.castLE h i))) : WindowExponent D :=
  ⟨splicePrefix h β γ.val, isWindowExponent_splicePrefix h D β γ.val htail γ.property⟩

@[simp] theorem spliceWindowExponent_val (h : l ≤ N) (D : Fin N → ℕ)
    (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (D i))
    (γ : WindowExponent (fun i => D (Fin.castLE h i))) :
    (spliceWindowExponent h D β htail γ).val = splicePrefix h β γ.val := rfl

/-- Prefix embedding is compatible with the literal product of generator powers. -/
theorem monomial_extendPrefix {F : Type*} [Field F] (h : l ≤ N)
    (y : Fin N → Fˣ) (γ : Fin l → ℤ) :
    monomial y (.ofAdd (extendPrefixExponent h γ)) =
      monomial (fun i => y (Fin.castLE h i)) (.ofAdd γ) := by
  classical
  apply congrArg Units.val
  symm
  apply Fintype.prod_of_injective (Fin.castLE h) (Fin.castLE_injective h)
  · intro i hi
    have hn : ¬ i.val < l := by
      intro hil
      apply hi
      exact ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
    simp [extendPrefixExponent, hn]
  · intro i
    simp [extendPrefixExponent, i.isLt]

/-- Exponent addition is literal multiplication of the evaluated monomials. -/
theorem monomial_add {F : Type*} [Field F] (y : Fin N → Fˣ)
    (β γ : Fin N → ℤ) :
    monomial y (.ofAdd (β + γ)) = monomial y (.ofAdd β) * monomial y (.ofAdd γ) :=
  (monomial y).map_mul (.ofAdd β) (.ofAdd γ)

/-- The actual algebra map inserting a smaller formal Laurent ring as the prefix variables. -/
def prefixLaurentMap (K : Type*) [Field K] (h : l ≤ N) : Laurent K l →ₐ[K] Laurent K N :=
  AddMonoidAlgebra.mapDomainAlgHom K K (extendPrefixExponent h)

@[simp] theorem prefixLaurentMap_single {K : Type*} [Field K] (h : l ≤ N)
    (γ : Fin l → ℤ) (c : K) :
    prefixLaurentMap K h (AddMonoidAlgebra.single γ c) =
      AddMonoidAlgebra.single (extendPrefixExponent h γ) c :=
  AddMonoidAlgebra.mapDomain_single

/-- The formal multiplier has exactly the spliced exponent and multiplied coefficient. -/
theorem prefixLaurentMap_single_mul_peeling {K : Type*} [Field K] (h : l ≤ N)
    (β : Fin N → ℤ) (γ : Fin l → ℤ) (c a : K) :
    prefixLaurentMap K h (AddMonoidAlgebra.single γ c) *
        AddMonoidAlgebra.single (peelingExponent h β) a =
      AddMonoidAlgebra.single (splicePrefix h β γ) (c * a) := by
  rw [prefixLaurentMap_single, AddMonoidAlgebra.single_mul_single, extendPrefix_add_peeling]

/-- The original single monomial is the corrected prefix quotient times its peeling multiplier. -/
theorem single_peeling_factorization {K : Type*} [Field K] (h : l ≤ N)
    (β : Fin N → ℤ) (c a : K) (ha : a ≠ 0) :
    prefixLaurentMap K h (AddMonoidAlgebra.single (shiftedPrefix h β) (c / a)) *
        AddMonoidAlgebra.single (peelingExponent h β) a =
      AddMonoidAlgebra.single β c := by
  rw [prefixLaurentMap_single_mul_peeling, splicePrefix_shiftedPrefix, div_mul_cancel₀ _ ha]

/-- Prefix insertion commutes with actual Laurent evaluation. -/
theorem evalAlgHom_prefixLaurentMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h : l ≤ N) (y : Fin N → Fˣ) (f : Laurent K l) :
    evalAlgHom K y (prefixLaurentMap K h f) =
      evalAlgHom K (fun i => y (Fin.castLE h i)) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single γ c =>
      rw [prefixLaurentMap_single, evalAlgHom_single, evalAlgHom_single, monomial_extendPrefix]

end PrefixExponents

section ActualMovingFields
variable (K : Type*) {E : Type*} [NormedField K] [NormedField E] [NormedAlgebra K E]

/-- The constructed basis vectors, as literal monomials in their actual finite field. -/
theorem movingTowerBasis_eq_movingMonomial (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ)
    (β : WindowExponent (fun i : Fin n => movingDegree K y i.val)) :
    movingTowerBasis K y hy n β = movingMonomial K y n β.val := by
  apply Subtype.ext
  rw [movingTowerBasis_apply, movingMonomial_coe]

/-- Laurent evaluation into the actual field generated by the finite prefix. -/
def movingTowerEval (y : ℕ → Eˣ) (n : ℕ) : Laurent K n →ₐ[K] movingField K y n :=
  evalAlgHom K (movingFieldUnits K y n)

/-- The canonical coefficient-linear moving-basis lift into formal Laurent polynomials. -/
def movingTowerLift (y : ℕ → Eˣ) (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ) :
    movingField K y n →ₗ[K] Laurent K n :=
  windowBasisLift (movingTowerBasis K y hy n)

@[simp] theorem movingTowerEval_single (y : ℕ → Eˣ) (n : ℕ)
    (β : Fin n → ℤ) (c : K) :
    movingTowerEval K y n (AddMonoidAlgebra.single β c) = c • movingMonomial K y n β :=
  evalAlgHom_single K (movingFieldUnits K y n) β c

/-- The finite-field evaluation agrees with the original ambient evaluation. -/
theorem movingTowerEval_coe (y : ℕ → Eˣ) (n : ℕ) (f : Laurent K n) :
    ((movingTowerEval K y n f : movingField K y n) : E) =
      eval (algebraMap K E) (fun i : Fin n => y i.val) f := by
  change (algebraMap (movingField K y n) E)
    (eval (algebraMap K (movingField K y n)) (movingFieldUnits K y n) f) = _
  rw [eval_eq_sum, eval_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro β _hβ
  rw [map_mul, ← IsScalarTower.algebraMap_apply K (movingField K y n) E]
  congr 1
  exact movingFieldUnits_monomial_coe K y n β

@[simp] theorem movingTowerEval_lift (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ) (x : movingField K y n) :
    movingTowerEval K y n (movingTowerLift K y hy n x) = x :=
  eval_windowBasisLift (movingTowerBasis K y hy n) (movingFieldUnits K y n)
    (movingTowerBasis_eq_movingMonomial K y hy n) x

/-- Evaluation of the canonical lift is the same actual ambient field element. -/
theorem eval_movingTowerLift (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ) (x : movingField K y n) :
    eval (algebraMap K E) (fun i : Fin n => y i.val) (movingTowerLift K y hy n x) = (x : E) := by
  rw [← movingTowerEval_coe, movingTowerEval_lift]

/-- The canonical lift is exactly the finite moving-basis expansion. -/
theorem movingTowerLift_eq_sum (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ) (x : movingField K y n) :
    movingTowerLift K y hy n x =
      ∑ β ∈ ((movingTowerBasis K y hy n).repr x).support,
        AddMonoidAlgebra.single β.val ((movingTowerBasis K y hy n).repr x β) :=
  windowBasisLift_eq_sum _ x

/-- Canonical evaluation-lift fixes every literal window monomial, including its coefficient. -/
theorem movingTowerLift_eval_single (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ) (β : Fin n → ℤ)
    (hβ : IsWindowExponent (fun i : Fin n => movingDegree K y i.val) β) (c : K) :
    movingTowerLift K y hy n (movingTowerEval K y n (AddMonoidAlgebra.single β c)) =
      AddMonoidAlgebra.single β c :=
  windowBasisLift_eval_single _ _ (movingTowerBasis_eq_movingMonomial K y hy n) β hβ c

/-- An ambient evaluation-kernel element is a finite sum of actual bad-term residuals. -/
theorem movingTower_kernel_decomposition (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ) (f : Laurent K n)
    (hf : eval (algebraMap K E) (fun i : Fin n => y i.val) f = 0) :
    f = ∑ β ∈ badWindowSupport (fun i : Fin n => movingDegree K y i.val) f,
      (AddMonoidAlgebra.single β (f.coeff β) - movingTowerLift K y hy n
        (movingTowerEval K y n (AddMonoidAlgebra.single β (f.coeff β)))) := by
  have hz : movingTowerEval K y n f = 0 := by
    apply Subtype.ext
    rw [movingTowerEval_coe, hf]
    rfl
  exact kernel_eq_sum_sub_windowBasisLift_eval _ _
    (movingTowerBasis_eq_movingMonomial K y hy n) f hz

/-- The genuine inclusion of a prefix field into a later finite stage. -/
def movingFieldInclusion (y : ℕ → Eˣ) {l N : ℕ} (h : l ≤ N) :
    movingField K y l →ₐ[K] movingField K y N :=
  IntermediateField.inclusion (movingField_monotone K y h)

@[simp] theorem movingFieldInclusion_coe (y : ℕ → Eˣ) {l N : ℕ} (h : l ≤ N)
    (x : movingField K y l) : (movingFieldInclusion K y h x : E) = (x : E) := rfl

/-- Embedding a prefix monomial and multiplying by the peeling monomial gives the spliced monomial. -/
theorem movingMonomial_splice (y : ℕ → Eˣ) {l N : ℕ} (h : l ≤ N)
    (β : Fin N → ℤ) (γ : Fin l → ℤ) :
    movingFieldInclusion K y h (movingMonomial K y l γ) *
        movingMonomial K y N (peelingExponent h β) =
      movingMonomial K y N (splicePrefix h β γ) := by
  apply Subtype.ext
  change (movingMonomial K y l γ : E) * (movingMonomial K y N (peelingExponent h β) : E) =
    (movingMonomial K y N (splicePrefix h β γ) : E)
  rw [movingMonomial_coe, movingMonomial_coe, movingMonomial_coe]
  change monomial (fun i : Fin l => y i.val) (.ofAdd γ) *
    monomial (fun i : Fin N => y i.val) (.ofAdd (peelingExponent h β)) =
      monomial (fun i : Fin N => y i.val) (.ofAdd (splicePrefix h β γ))
  have hp : monomial (fun i : Fin N => y i.val) (.ofAdd (extendPrefixExponent h γ)) =
      monomial (fun i : Fin l => y i.val) (.ofAdd γ) := by
    simpa only [Fin.val_castLE] using monomial_extendPrefix h (fun i : Fin N => y i.val) γ
  rw [← hp, ← monomial_add, extendPrefix_add_peeling]

/-- Exact multiplication identity for the actual lower and upper canonical basis vectors. -/
theorem movingTowerBasis_splice (y : ℕ → Eˣ) (hy : ∀ i, IsAlgebraic K (y i : E))
    {l N : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree K y i.val))
    (γ : WindowExponent (fun i : Fin l => movingDegree K y i.val)) :
    movingFieldInclusion K y h (movingTowerBasis K y hy l γ) *
        movingMonomial K y N (peelingExponent h β) =
      movingTowerBasis K y hy N
        (spliceWindowExponent h (fun i : Fin N => movingDegree K y i.val) β htail γ) := by
  rw [movingTowerBasis_eq_movingMonomial, movingTowerBasis_eq_movingMonomial]
  exact movingMonomial_splice K y h β γ.val

/-- Peeling identifies the lift with the actual smaller-field expansion at the spliced exponents. -/
theorem movingTowerLift_peeling (y : ℕ → Eˣ) (hy : ∀ i, IsAlgebraic K (y i : E))
    {l N : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree K y i.val))
    (x : movingField K y l) (c : K) :
    movingTowerLift K y hy N
      (c • (movingFieldInclusion K y h x * movingMonomial K y N (peelingExponent h β))) =
      ∑ γ ∈ ((movingTowerBasis K y hy l).repr x).support,
        AddMonoidAlgebra.single (splicePrefix h β γ.val)
          (c * (movingTowerBasis K y hy l).repr x γ) := by
  nth_rw 1 [← (movingTowerBasis K y hy l).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    Finset.sum_mul, Finset.smul_sum, Algebra.smul_mul_assoc, smul_smul]
  apply Finset.sum_congr rfl
  intro γ _hγ
  rw [movingTowerBasis_splice K y hy h β htail γ]
  simpa only [map_smul, movingTowerLift, spliceWindowExponent_val] using
    windowBasisLift_smul_basis (movingTowerBasis K y hy N)
      (spliceWindowExponent h (fun i : Fin N => movingDegree K y i.val) β htail γ)
      (c * (movingTowerBasis K y hy l).repr x γ)

/-- Formal prefix insertion evaluates through the genuine inclusion of the prefix field. -/
theorem movingTowerEval_prefixLaurentMap (y : ℕ → Eˣ) {l N : ℕ}
    (h : l ≤ N) (f : Laurent K l) :
    movingTowerEval K y N (prefixLaurentMap K h f) =
      movingFieldInclusion K y h (movingTowerEval K y l f) := by
  apply Subtype.ext
  rw [movingTowerEval_coe, movingFieldInclusion_coe, movingTowerEval_coe]
  change evalAlgHom K (fun i : Fin N => y i.val) (prefixLaurentMap K h f) =
    evalAlgHom K (fun i : Fin l => y i.val) f
  simpa only [Fin.val_castLE] using evalAlgHom_prefixLaurentMap h (fun i : Fin N => y i.val) f

/-- The peeling lift is the embedded smaller lift times the literal formal multiplier. -/
theorem movingTowerLift_peeling_factor (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) {l N : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree K y i.val))
    (x : movingField K y l) (c : K) :
    movingTowerLift K y hy N
      (c • (movingFieldInclusion K y h x * movingMonomial K y N (peelingExponent h β))) =
      prefixLaurentMap K h (movingTowerLift K y hy l x) *
        AddMonoidAlgebra.single (peelingExponent h β) c := by
  rw [movingTowerLift_peeling K y hy h β htail, movingTowerLift_eq_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ _hγ
  rw [prefixLaurentMap_single_mul_peeling, mul_comm]

/-- Evaluation and lifting of a peeled formal product uses the actual smaller-field lift. -/
theorem movingTowerLift_eval_peeling (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) {l N : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree K y i.val))
    (p : Laurent K l) (c : K) :
    movingTowerLift K y hy N (movingTowerEval K y N
      (prefixLaurentMap K h p * AddMonoidAlgebra.single (peelingExponent h β) c)) =
      prefixLaurentMap K h (movingTowerLift K y hy l (movingTowerEval K y l p)) *
        AddMonoidAlgebra.single (peelingExponent h β) c := by
  rw [map_mul, movingTowerEval_prefixLaurentMap, movingTowerEval_single, Algebra.mul_smul_comm]
  exact movingTowerLift_peeling_factor K y hy h β htail _ c

/-- The formal residual identity obtained by removing a moving window. -/
theorem movingTower_peeling_residual (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) {l N : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree K y i.val))
    (p : Laurent K l) (c : K) :
    (prefixLaurentMap K h p * AddMonoidAlgebra.single (peelingExponent h β) c) -
      movingTowerLift K y hy N (movingTowerEval K y N
        (prefixLaurentMap K h p * AddMonoidAlgebra.single (peelingExponent h β) c)) =
      prefixLaurentMap K h (p - movingTowerLift K y hy l (movingTowerEval K y l p)) *
        AddMonoidAlgebra.single (peelingExponent h β) c := by
  rw [movingTowerLift_eval_peeling K y hy h β htail, map_sub, sub_mul]

/-- A single monomial uses the corrected prefix coefficient c/a and the common factor a. -/
theorem movingTowerLift_eval_single_peeling (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) {l N : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree K y i.val))
    (c a : K) (ha : a ≠ 0) :
    movingTowerLift K y hy N (movingTowerEval K y N (AddMonoidAlgebra.single β c)) =
      prefixLaurentMap K h (movingTowerLift K y hy l (movingTowerEval K y l
        (AddMonoidAlgebra.single (shiftedPrefix h β) (c / a)))) *
          AddMonoidAlgebra.single (peelingExponent h β) a := by
  rw [← single_peeling_factorization h β c a ha]
  exact movingTowerLift_eval_peeling K y hy h β htail _ a

/-- Linearity also decomposes arbitrary finite presentations, before collecting equal exponents. -/
theorem movingTower_kernel_decomposition_sum (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) (n : ℕ)
    {ι : Type*} (s : Finset ι) (f : ι → Laurent K n)
    (hf : eval (algebraMap K E) (fun i : Fin n => y i.val) (∑ i ∈ s, f i) = 0) :
    (∑ i ∈ s, f i) = ∑ i ∈ s,
      (f i - movingTowerLift K y hy n (movingTowerEval K y n (f i))) := by
  have hz : movingTowerEval K y n (∑ i ∈ s, f i) = 0 := by
    apply Subtype.ext
    rw [movingTowerEval_coe, hf]
    rfl
  rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, hz, map_zero, sub_zero]

/-- Distinct smaller-window coordinates are the actual collected coefficients after peeling. -/
theorem movingTowerLift_peeling_coeff (y : ℕ → Eˣ)
    (hy : ∀ i, IsAlgebraic K (y i : E)) {l N : ℕ} (h : l ≤ N) (β : Fin N → ℤ)
    (htail : ∀ i : Fin N, l ≤ i.val → correctedDigit β i ∈ digitInterval (movingDegree K y i.val))
    (x : movingField K y l) (c : K)
    (γ : WindowExponent (fun i : Fin l => movingDegree K y i.val)) :
    (movingTowerLift K y hy N
      (c • (movingFieldInclusion K y h x * movingMonomial K y N (peelingExponent h β)))).coeff
        (splicePrefix h β γ.val) = c * (movingTowerBasis K y hy l).repr x γ := by
  classical
  have hinj : Function.Injective
      (fun γ : WindowExponent (fun i : Fin l => movingDegree K y i.val) => splicePrefix h β γ.val) :=
    (splicePrefix_injective h β).comp Subtype.val_injective
  rw [movingTowerLift_peeling K y hy h β htail]
  by_cases hz : (movingTowerBasis K y hy l).repr x γ = 0
  · simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply, hinj.eq_iff, hz]
  · simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply, hinj.eq_iff, hz]

end ActualMovingFields

end HereditaryAtomicity.DVRBase
