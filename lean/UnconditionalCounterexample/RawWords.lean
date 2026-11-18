import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Finite raw-stage words and denominator choices

Earlier normalized generators have a triangular denominator expression in the raw
factors. Signed words in a finite exponent box admit a common new normalization
exponent, after which a fresh polynomial degree can be chosen.

The construction has a zero-based prefix length n and uses the paper's stage
budget n+1. The new degree exceeds all preceding raw degrees. No fresh
polynomial, arithmetic interpolation, valuation estimate, or irreducibility
is asserted here: the final identity is universal in the fresh polynomial.
-/

namespace UnconditionalCounterexample.RawWords

open scoped BigOperators

/-- Earlier normalized generator: its raw numerator divided by a common power
of all strictly earlier raw factors. -/
def normalizedFactor {K : Type*} [Field K] (P : ℕ → K) (E : ℕ → ℕ) (i : ℕ) : K :=
  P i / ∏ j ∈ Finset.range i, P j ^ E i

/-- Triangular expansion of a word in the first n normalized generators.
At the next stage its signed exponent is added at the fresh numerator and
subtracted, times the normalization power, at every previous raw factor. -/
def earlierRawExponent (E : ℕ → ℕ) (c : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | n + 1, j => if j = n then c n else earlierRawExponent E c n j - (E n : ℤ) * c n

/-- The concrete finite list of words with n earlier generators, their signed
exponents in [-r,r], and latest exponent in [1,r]. For r=0 this list is empty. -/
abbrev StageWord (n r : ℕ) := (Fin n → Fin (2 * r + 1)) × Fin r

def StageWord.oldExponent {n r : ℕ} (w : StageWord n r) (j : ℕ) : ℤ :=
  if h : j < n then (w.1 ⟨j, h⟩ : ℤ) - r else 0

def StageWord.latestExponent {n r : ℕ} (w : StageWord n r) : ℕ := w.2.val + 1

theorem StageWord.oldExponent_bounds {n r : ℕ} (w : StageWord n r) (j : ℕ) :
    -(r : ℤ) ≤ w.oldExponent j ∧ w.oldExponent j ≤ r := by
  unfold StageWord.oldExponent
  split_ifs with hj
  · have h := (w.1 ⟨j, hj⟩).isLt
    omega
  · omega

theorem StageWord.latestExponent_bounds {n r : ℕ} (w : StageWord n r) :
    0 < w.latestExponent ∧ w.latestExponent ≤ r := by
  have h := w.2.isLt
  unfold StageWord.latestExponent
  omega

/-- Every signed exponent vector in the stated finite box and every positive
latest exponent at most r occur in the concrete stage list. -/
theorem stageWord_covers {n r : ℕ} (c : ℕ → ℤ)
    (hc : ∀ j < n, -(r : ℤ) ≤ c j ∧ c j ≤ r) (a : ℕ) (ha : 0 < a ∧ a ≤ r) :
    ∃ w : StageWord n r, (∀ j < n, w.oldExponent j = c j) ∧ w.latestExponent = a := by
  let v : Fin n → Fin (2 * r + 1) := fun j =>
    ⟨(c j + r).toNat, by have h := hc j j.isLt; omega⟩
  let w : StageWord n r := (v, ⟨a - 1, by omega⟩)
  refine ⟨w, ?_, ?_⟩
  · intro j hj
    have h := hc j hj
    simp only [StageWord.oldExponent, hj, dite_true, w, v]
    omega
  · dsimp [StageWord.latestExponent, w]
    omega

/-- One common old-factor power dominates every finite listed signed exponent,
even after multiplication by an arbitrary positive latest exponent. -/
theorem exists_common_denominator_power {W J : Type*}
    (words : Finset W) (old : Finset J) (e : W → J → ℤ) (a : W → ℕ)
    (ha : ∀ w ∈ words, 0 < a w) :
    ∃ E : ℕ, 0 < E ∧ ∀ w ∈ words, ∀ j ∈ old, e w j < (E * a w : ℕ) := by
  classical
  let B := words.sup (fun w => old.sup (fun j => (e w j).toNat))
  let E := B + 1
  refine ⟨E, by dsimp [E]; omega, ?_⟩
  intro w hw j hj
  have hjB : (e w j).toNat ≤ B :=
    (Finset.le_sup (f := fun j => (e w j).toNat) hj).trans
      (Finset.le_sup (f := fun w => old.sup (fun j => (e w j).toNat)) hw)
  have hmul : E ≤ E * a w := by
    have hap : 1 ≤ a w := ha w hw
    simpa using Nat.mul_le_mul_left E hap
  have heB : e w j ≤ (B : ℤ) := by omega
  have hltE : e w j < (E : ℤ) := by dsimp [E]; omega
  exact hltE.trans_le (Int.ofNat_le.mpr hmul)

/-- The positive natural exponent left in the old polynomial denominator. -/
def denominatorExponent (E a : ℕ) (e : ℤ) : ℕ := ((E * a : ℕ) - e).toNat

theorem denominatorExponent_pos {E a : ℕ} {e : ℤ}
    (h : e < (E * a : ℕ)) : 0 < denominatorExponent E a e := by
  unfold denominatorExponent
  omega

theorem denominatorExponent_cast {E a : ℕ} {e : ℤ}
    (h : e ≤ (E * a : ℕ)) :
    (denominatorExponent E a e : ℤ) = (E * a : ℕ) - e := by
  unfold denominatorExponent
  apply Int.toNat_of_nonneg
  omega

section Field

variable {K : Type*} [Field K]

/-- The actual triangular raw-denominator normalization expands every finite
signed normalized word into integer powers of earlier raw factors. -/
theorem normalized_factors_expand (P : ℕ → K) (E : ℕ → ℕ) (c : ℕ → ℤ)
    (n : ℕ) (hP : ∀ j < n, P j ≠ 0) :
    (∏ j ∈ Finset.range n, normalizedFactor P E j ^ c j) =
      ∏ j ∈ Finset.range n, P j ^ earlierRawExponent E c n j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hPn : ∀ j < n, P j ≠ 0 := fun j hj => hP j (by omega)
    have hden : (∏ j ∈ Finset.range n, P j ^ E n) ^ c n =
        ∏ j ∈ Finset.range n, P j ^ ((E n : ℤ) * c n) := by
      rw [← Finset.prod_zpow]
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_natCast, ← zpow_mul]
    have hshift :
        (∏ j ∈ Finset.range n, P j ^ earlierRawExponent E c n j) /
          (∏ j ∈ Finset.range n, P j ^ ((E n : ℤ) * c n)) =
        ∏ j ∈ Finset.range n,
          P j ^ (earlierRawExponent E c n j - (E n : ℤ) * c n) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      exact (zpow_sub₀ (hPn j (Finset.mem_range.mp hj)) _ _).symm
    rw [Finset.prod_range_succ, ih hPn, normalizedFactor, div_zpow, hden,
      Finset.prod_range_succ]
    have hprefix :
        (∏ j ∈ Finset.range n, P j ^ earlierRawExponent E c (n + 1) j) =
        ∏ j ∈ Finset.range n,
          P j ^ (earlierRawExponent E c n j - (E n : ℤ) * c n) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [earlierRawExponent, Nat.ne_of_lt (Finset.mem_range.mp hj)]
    rw [hprefix]
    simp only [earlierRawExponent, ite_true]
    rw [← hshift]
    simp only [div_eq_mul_inv]
    ring

theorem shifted_old_factor (x : K) (hx : x ≠ 0) (E a : ℕ) (e : ℤ)
    (h : e ≤ (E * a : ℕ)) :
    x ^ e / x ^ (E * a) = (x ^ denominatorExponent E a e)⁻¹ := by
  have hd := denominatorExponent_cast h
  have heq : e - (E * a : ℕ) = -(denominatorExponent E a e : ℤ) := by omega
  rw [← zpow_natCast x (E * a), ← zpow_sub₀ hx, heq, zpow_neg, zpow_natCast]

/-- Exact single-numerator normal form, with the old denominator independent
of the fresh factor F. Nonzero hypotheses concern only the old factors. -/
theorem normalized_word_eq_single_numerator {J : Type*}
    (old : Finset J) (P : J → K) (hP : ∀ j ∈ old, P j ≠ 0)
    (E a : ℕ) (e : J → ℤ) (h : ∀ j ∈ old, e j ≤ (E * a : ℕ)) (F : K) :
    (F / (∏ j ∈ old, P j ^ E)) ^ a * (∏ j ∈ old, P j ^ e j) =
      F ^ a / (∏ j ∈ old, P j ^ denominatorExponent E a (e j)) := by
  have hden : (∏ j ∈ old, P j ^ E) ^ a = ∏ j ∈ old, P j ^ (E * a) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j _
    exact (pow_mul _ _ _).symm
  have hshift : (∏ j ∈ old, P j ^ e j) / (∏ j ∈ old, P j ^ (E * a)) =
      (∏ j ∈ old, P j ^ denominatorExponent E a (e j))⁻¹ := by
    rw [← Finset.prod_div_distrib, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    exact shifted_old_factor (P j) (hP j hj) E a (e j) (h j hj)
  rw [div_pow, hden]
  calc
    F ^ a / (∏ j ∈ old, P j ^ (E * a)) * (∏ j ∈ old, P j ^ e j) =
      F ^ a * ((∏ j ∈ old, P j ^ e j) / (∏ j ∈ old, P j ^ (E * a))) := by
        simp only [div_eq_mul_inv]
        ring
    _ = _ := by rw [hshift, div_eq_mul_inv]

end Field

/-- A finite collection of words admits one normalization exponent and actual
old-factor denominators in the coefficient ring, all chosen before the fresh
factor. Specializing the coefficient ring to rational polynomials gives the
polynomial denominators used at a raw construction stage. -/
theorem choose_raw_word_denominators {R K W J : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (words : Finset W) (old : Finset J) (P : J → R)
    (hP : ∀ j ∈ old, φ (P j) ≠ 0) (e : W → J → ℤ) (a : W → ℕ)
    (ha : ∀ w ∈ words, 0 < a w) :
    ∃ E : ℕ, 0 < E ∧ ∃ d : W → J → ℕ,
      (∀ w ∈ words, ∀ j ∈ old, 0 < d w j) ∧
      (∀ w ∈ words, φ (∏ j ∈ old, P j ^ d w j) ≠ 0) ∧
      ∀ F : R, ∀ w ∈ words,
        (φ F / φ (∏ j ∈ old, P j ^ E)) ^ a w *
            (∏ j ∈ old, φ (P j) ^ e w j) =
          φ (F ^ a w) / φ (∏ j ∈ old, P j ^ d w j) := by
  classical
  obtain ⟨E, hE, hbound⟩ := exists_common_denominator_power words old e a ha
  let d := fun w j => denominatorExponent E (a w) (e w j)
  refine ⟨E, hE, d, ?_, ?_, ?_⟩
  · intro w hw j hj
    exact denominatorExponent_pos (hbound w hw j hj)
  · intro w _
    simp only [map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun j hj => pow_ne_zero _ (hP j hj)
  · intro F w hw
    simpa only [map_prod, map_pow] using
      normalized_word_eq_single_numerator old (fun j => φ (P j)) hP E (a w)
        (e w) (fun j hj => (hbound w hw j hj).le) (φ F)

/-- At a raw stage, first expand each actual word in the earlier normalized
generators. One common normalization power then makes every earlier raw factor
occur with positive exponent in its polynomial denominator. All these choices
precede the fresh factor F. -/
theorem choose_normalized_word_denominators {R K W : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (words : Finset W) (n : ℕ) (P : ℕ → R) (priorE : ℕ → ℕ)
    (hP : ∀ j < n, φ (P j) ≠ 0) (c : W → ℕ → ℤ) (a : W → ℕ)
    (ha : ∀ w ∈ words, 0 < a w) :
    ∃ E : ℕ, 0 < E ∧ ∃ d : W → ℕ → ℕ,
      (∀ w ∈ words, ∀ j < n, 0 < d w j) ∧
      (∀ w ∈ words, φ (∏ j ∈ Finset.range n, P j ^ d w j) ≠ 0) ∧
      ∀ F : R, ∀ w ∈ words,
        (φ F / φ (∏ j ∈ Finset.range n, P j ^ E)) ^ a w *
            (∏ j ∈ Finset.range n, normalizedFactor (fun k => φ (P k)) priorE j ^ c w j) =
          φ (F ^ a w) / φ (∏ j ∈ Finset.range n, P j ^ d w j) := by
  obtain ⟨E, hE, d, hd, hnz, heq⟩ := choose_raw_word_denominators φ words
    (Finset.range n) P (fun j hj => hP j (Finset.mem_range.mp hj))
    (fun w => earlierRawExponent priorE (c w) n) a ha
  refine ⟨E, hE, d, fun w hw j hj => hd w hw j (Finset.mem_range.mpr hj), hnz, ?_⟩
  intro F w hw
  rw [normalized_factors_expand (fun k => φ (P k)) priorE (c w) n hP]
  exact heq F w hw

/-- After fixing the finite polynomial denominator list, one may choose the
fresh degree above any requested lower bound and force every listed numerator
power to have degree strictly larger than its denominator. -/
theorem choose_degree_after_denominators {R W : Type*} [CommRing R] [IsDomain R]
    (words : Finset W) (H : W → Polynomial R) (a : W → ℕ)
    (ha : ∀ w ∈ words, 0 < a w) (minimum : ℕ) :
    ∃ degree : ℕ, minimum ≤ degree ∧ 5 ≤ degree ∧
      (∀ w ∈ words, (H w).natDegree < a w * degree) ∧
      ∀ F : Polynomial R, F.natDegree = degree →
        ∀ w ∈ words, (H w).natDegree < (F ^ a w).natDegree := by
  classical
  let degree := max (max minimum 5) (words.sup (fun w => (H w).natDegree) + 1)
  have hminimum : minimum ≤ degree := (le_max_left _ _).trans (le_max_left _ _)
  have hfive : 5 ≤ degree := (le_max_right _ _).trans (le_max_left _ _)
  have hbound : ∀ w ∈ words, (H w).natDegree < a w * degree := by
    intro w hw
    have hsup := Finset.le_sup (f := fun w => (H w).natDegree) hw
    have hdeg : words.sup (fun w => (H w).natDegree) + 1 ≤ degree := le_max_right _ _
    have hamul : degree ≤ a w * degree := by
      simpa using Nat.mul_le_mul_right degree (ha w hw)
    omega
  refine ⟨degree, hminimum, hfive, hbound, ?_⟩
  intro F hF w hw
  rw [Polynomial.natDegree_pow, hF]
  exact hbound w hw

/-- The complete finite bounded-word list for a raw polynomial stage has
simultaneously chosen old-factor denominators and a sufficiently large fresh
degree. Both choices are made before universally quantifying over the fresh
polynomial. The normalization uses exactly the prior raw construction factors. -/
theorem choose_stage_denominators_and_degree {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] (φ : Polynomial R →+* K) (n r minimum : ℕ)
    (P : ℕ → Polynomial R) (priorE : ℕ → ℕ) (hP : ∀ j < n, φ (P j) ≠ 0) :
    ∃ E : ℕ, ∃ d : StageWord n r → ℕ → ℕ, ∃ degree : ℕ,
      0 < E ∧
      (∀ w : StageWord n r, ∀ j < n, 0 < d w j) ∧
      (∀ w : StageWord n r, φ (∏ j ∈ Finset.range n, P j ^ d w j) ≠ 0) ∧
      minimum ≤ degree ∧ 5 ≤ degree ∧
      (∀ w : StageWord n r,
        (∏ j ∈ Finset.range n, P j ^ d w j).natDegree < w.latestExponent * degree) ∧
      ∀ F : Polynomial R, ∀ w : StageWord n r,
        (φ F / φ (∏ j ∈ Finset.range n, P j ^ E)) ^ w.latestExponent *
            (∏ j ∈ Finset.range n,
              normalizedFactor (fun k => φ (P k)) priorE j ^ w.oldExponent j) =
          φ (F ^ w.latestExponent) / φ (∏ j ∈ Finset.range n, P j ^ d w j) := by
  classical
  obtain ⟨E, hE, d, hd, hnz, heq⟩ := choose_normalized_word_denominators φ
    (Finset.univ : Finset (StageWord n r)) n P priorE hP StageWord.oldExponent
    StageWord.latestExponent (fun w _ => w.latestExponent_bounds.1)
  obtain ⟨degree, hmin, hfive, hdegree, _⟩ := choose_degree_after_denominators
    (Finset.univ : Finset (StageWord n r))
    (fun w => ∏ j ∈ Finset.range n, P j ^ d w j) StageWord.latestExponent
    (fun w _ => w.latestExponent_bounds.1) minimum
  exact ⟨E, d, degree, hE, fun w => hd w (Finset.mem_univ w),
    fun w => hnz w (Finset.mem_univ w), hmin, hfive,
    fun w => hdegree w (Finset.mem_univ w), fun F w => heq F w (Finset.mem_univ w)⟩

/-- The paper numbers its first raw stage by 1, whereas a prefix of length n is
zero-based here. Thus the construction's exponent budget is n+1. Its new degree
also strictly exceeds every earlier raw degree. -/
theorem choose_construction_stage {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] (φ : Polynomial R →+* K) (n minimum : ℕ)
    (P : ℕ → Polynomial R) (priorE : ℕ → ℕ) (hP : ∀ j < n, φ (P j) ≠ 0) :
    ∃ E : ℕ, ∃ d : StageWord n (n + 1) → ℕ → ℕ, ∃ degree : ℕ,
      0 < E ∧
      (∀ w : StageWord n (n + 1), ∀ j < n, 0 < d w j) ∧
      (∀ w : StageWord n (n + 1), φ (∏ j ∈ Finset.range n, P j ^ d w j) ≠ 0) ∧
      minimum ≤ degree ∧ 5 ≤ degree ∧
      (∀ j < n, (P j).natDegree < degree) ∧
      (∀ w : StageWord n (n + 1),
        (∏ j ∈ Finset.range n, P j ^ d w j).natDegree < w.latestExponent * degree) ∧
      ∀ F : Polynomial R, ∀ w : StageWord n (n + 1),
        (φ F / φ (∏ j ∈ Finset.range n, P j ^ E)) ^ w.latestExponent *
            (∏ j ∈ Finset.range n,
              normalizedFactor (fun k => φ (P k)) priorE j ^ w.oldExponent j) =
          φ (F ^ w.latestExponent) / φ (∏ j ∈ Finset.range n, P j ^ d w j) := by
  let minimum' := max minimum ((Finset.range n).sup (fun j => (P j).natDegree) + 1)
  obtain ⟨E, d, degree, hE, hd, hnz, hmin, hfive, hbound, heq⟩ :=
    choose_stage_denominators_and_degree φ n (n + 1) minimum' P priorE hP
  have hmin' : minimum ≤ degree := (le_max_left _ _).trans hmin
  have hprior : ∀ j < n, (P j).natDegree < degree := by
    intro j hj
    have hsup := Finset.le_sup (f := fun j => (P j).natDegree) (Finset.mem_range.mpr hj)
    have hdeg : (Finset.range n).sup (fun j => (P j).natDegree) + 1 ≤ degree :=
      (le_max_right _ _).trans hmin
    omega
  exact ⟨E, d, degree, hE, hd, hnz, hmin', hfive, hprior, hbound, heq⟩

end UnconditionalCounterexample.RawWords
