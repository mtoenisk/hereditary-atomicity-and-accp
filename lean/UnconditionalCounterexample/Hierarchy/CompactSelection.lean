import UnconditionalCounterexample.Hierarchy.CompactApproximation
import UnconditionalCounterexample.ShiftedEisenstein

/-!
# Monic irreducible polynomials with prescribed values on compact fibres

For each prescribed prime first approximate the target function on its fibre.
Add the same monic falling factorial to each approximant. The falling factorial
has uniformly small values, since it is a large factorial times a Mahler basis
function, and its degree can exceed every local approximant. The local
polynomials are now monic of the same degree. Weak approximation on their
lower coefficients and Eisenstein at a fresh prime produce the result.
-/

noncomputable section
namespace UnconditionalCounterexample.Hierarchy
open Polynomial Finset GuardSupport ShiftedEisenstein
open scoped Polynomial

variable {ι : Type*} [Fintype ι] (p : ι → PrimeIndex) (hinj : Function.Injective p)

include hinj in
private theorem exists_monic_near_coeff (n : ℕ) (hn : 1 ≤ n) (T : ι → ℚ[X])
    (hm : ∀ i, (T i).Monic) (hd : ∀ i, (T i).natDegree = n+1) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ F : ℚ[X], F.Monic ∧ Irreducible F ∧ F.natDegree = n+1 ∧
      ∀ i k, ‖((F.coeff k : ℚ) : ℚ_[(p i).val]) - ((T i).coeff k : ℚ_[(p i).val])‖ ≤ δ i := by
  classical
  let v (i : ι) := (p i).val
  let (i : ι) : Fact (v i).Prime := ⟨(p i).property⟩
  have hv : Function.Injective v := Subtype.val_injective.comp hinj
  obtain ⟨ell,hℓ,hprime⟩ := Nat.exists_infinite_primes (univ.sup v + 1)
  let : Fact ell.Prime := ⟨hprime⟩
  have hfresh (i : ι) : v i ≠ ell := (lt_of_le_of_lt (le_sup (f := v) (mem_univ i)) hℓ).ne
  let target (k : ℕ) (i : ι) : ℚ_[v i] := (T i).coeff k
  let r : ZMod (ell ^ 1) := (-1) ^ (n+1)
  obtain ⟨D,hD,hSupp,z,M,_,hg⟩ := CoefficientApproximation.exists_supported_rational_progression
    v hv (target 0) δ hδ ell hprime hfresh 1 r
  let C₀ : ℚ := (z : ℚ) / D
  have h0 : C₀.den ∣ D ∧ (∀ i, ‖(C₀ : ℚ_[v i]) - target 0 i‖ < δ i) ∧
      (z : ZMod (ell ^ 1)) = (D : ZMod (ell ^ 1)) * r := by simpa [C₀] using hg 0
  have supp (q : ℕ) (hq : q.Prime) (h : q ∣ C₀.den) := hSupp q hq (h.trans h0.1)
  obtain ⟨c,hc⟩ := CoefficientApproximation.exists_padicInt_of_denominator_support v C₀ supp ell hfresh
  have hDℓ : ¬ell ∣ D := fun he ↦ (hSupp ell hprime he).elim fun i hi ↦ hfresh i hi.symm
  have hres := toZModPow_eq_of_cleared c C₀ hc D z hD hDℓ rfl 1 r h0.2.2
  obtain ⟨a,ha,hd',h0',hI,_,hnear,_,_⟩ := exists_irreducible_approximating_family
    v hv n hn C₀ supp (fun j i ↦ target (j.val+1) i) (fun _ ↦ δ) (fun _ ↦ hδ) ell hfresh c hc hres
    (∅ : Finset Unit) (fun _ ↦ (1 : MvPolynomial (Fin n) ℚ)) (by simp)
  let F := monicFamily n C₀ a
  refine ⟨F,ha,hI,hd',fun i k ↦ ?_⟩
  rcases lt_trichotomy k (n+1) with hlt | rfl | hgt
  · cases k with
    | zero => simpa only [F,h0'] using (h0.2.1 i).le
    | succ k =>
      let j : Fin n := ⟨k, by omega⟩
      change ‖(((monicFamily n C₀ a).coeff (j.val+1)) : ℚ_[v i]) - target (j.val+1) i‖ ≤ _
      rw [monicFamily_coeff_succ]
      exact (hnear j i).le
  · rw [show F.coeff (n+1) = 1 from hd' ▸ ha.coeff_natDegree,
        show (T i).coeff (n+1) = 1 from hd i ▸ (hm i).coeff_natDegree, sub_self, norm_zero]
    exact (hδ i).le
  · rw [coeff_eq_zero_of_natDegree_lt (show F.natDegree < k from hd' ▸ hgt),
        coeff_eq_zero_of_natDegree_lt (show (T i).natDegree < k from hd i ▸ hgt),sub_self,norm_zero]
    exact (hδ i).le

private theorem norm_aeval_le_of_coeff {q : PrimeIndex} (F : ℚ[X]) (x : ℤ_[q.val]) (δ : ℝ)
    (hδ : 0 ≤ δ) (hF : ∀ k, ‖(F.coeff k : ℚ_[q.val])‖ ≤ δ) : ‖aeval (x : ℚ_[q.val]) F‖ ≤ δ := by
  rw [aeval_def, eval₂_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hδ
  intro k _
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) x.norm_le_one)).trans (hF k)

private theorem tiny_falling_factorial (q : PrimeIndex) (d k : ℕ) (hk : q.val^k ≤ d) (x : ℤ_[q.val]) :
    ‖aeval (x : ℚ_[q.val]) (descPochhammer ℚ d)‖ ≤ ‖(q.val : ℚ_[q.val])‖^k := by
  have hm := aeval_mahlerPolynomial d x
  rw [mahlerPolynomial, map_mul, aeval_C, eq_ratCast, Rat.cast_inv, Rat.cast_natCast] at hm
  have h0 : (d.factorial : ℚ_[q.val]) ≠ 0 := Nat.cast_ne_zero.mpr d.factorial_ne_zero
  have h := (eq_div_iff h0).mp (show (mahler d x : ℚ_[q.val]) = aeval (x : ℚ_[q.val]) (descPochhammer ℚ d) / d.factorial
    by rw [div_eq_mul_inv,hm])
  obtain ⟨b,hb⟩ := Nat.dvd_factorial (pow_pos q.property.pos k) hk
  rw [← h, norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (mahler d x).norm_le_one).trans
  rw [hb,Nat.cast_mul,Nat.cast_pow,norm_mul,norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one (b : ℤ_[q.val]))

include hinj in
/-- A single monic irreducible of arbitrarily high degree approximates the
prescribed data on each of finitely many compact p-adic fibres. -/
theorem exists_monic_irreducible_approx (E : ∀ i, Set ℤ_[(p i).val]) (hE : ∀ i, IsCompact (E i))
    (f : ∀ i, LocallyConstant (E i) ℚ_[(p i).val]) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (floor : ℕ) :
    ∃ F : ℚ[X], F.Monic ∧ Irreducible F ∧ floor ≤ F.natDegree ∧
      ∀ i (x : E i), ‖aeval (x.val : ℚ_[(p i).val]) F - f i x‖ < ε i := by
  classical
  let δ (i : ι) := ε i / 3
  have hδ (i : ι) : 0 < δ i := div_pos (hε i) (by norm_num)
  choose H hH using fun i ↦ exists_rational_polynomial_approx (p i).val (E i) (hE i) (f i) (δ i) (hδ i)
  choose k hk using fun i ↦ exists_pow_lt_of_lt_one (hδ i) (Padic.norm_p_lt_one (p := (p i).val))
  let n := max floor (univ.sup (fun i ↦ max ((H i).natDegree) ((p i).val ^ k i))) + 1
  have bounds (i : ι) : max ((H i).natDegree) ((p i).val ^ k i) < n :=
    Nat.lt_succ_of_le ((le_sup (f := fun j ↦ max (H j).natDegree ((p j).val ^ k j)) (mem_univ i)).trans (le_max_right ..))
  let Z := descPochhammer ℚ (n+1)
  let T (i : ι) := Z + H i
  have hdeg (i : ι) : (H i).natDegree < Z.natDegree := by
    rw [show Z.natDegree = n+1 from descPochhammer_natDegree ..]
    exact (le_max_left ..).trans_lt ((bounds i).trans (Nat.lt_succ_self _))
  have hT (i : ι) : (T i).Monic := (monic_descPochhammer ℚ _).add_of_left (degree_lt_degree (hdeg i))
  have hTd (i : ι) : (T i).natDegree = n+1 :=
    (natDegree_add_eq_left_of_natDegree_lt (hdeg i)).trans (descPochhammer_natDegree ..)
  obtain ⟨F,hm,hI,hfd,hs⟩ := exists_monic_near_coeff p hinj n (Nat.le_add_left 1 _) T hT hTd δ hδ
  have hfloor : floor ≤ n+1 := by dsimp [n]; omega
  refine ⟨F,hm,hI, hfd ▸ hfloor,fun i x ↦ ?_⟩
  let e := aeval (R := ℚ) (x.val : ℚ_[(p i).val])
  have h1 : ‖e F - e (T i)‖ ≤ δ i := by
    rw [← map_sub]
    exact norm_aeval_le_of_coeff (F - T i) x.val _ (hδ i).le (fun j ↦ by simpa using hs i j)
  have h2 : ‖e (T i) - e (H i)‖ < δ i := by
    rw [show T i = Z + H i from rfl, map_add,add_sub_cancel_right]
    exact (tiny_falling_factorial (p i) _ _ ((le_max_right ..).trans (bounds i).le |>.trans (Nat.le_succ ..)) x.val).trans_lt (hk i)
  calc ‖e F - f i x‖ ≤ ‖e F - e (T i)‖ + ‖e (T i) - f i x‖ := norm_sub_le_norm_sub_add_norm_sub ..
       _ ≤ δ i + (‖e (T i) - e (H i)‖ + ‖e (H i) - f i x‖) :=
         add_le_add h1 (norm_sub_le_norm_sub_add_norm_sub ..)
       _ < ε i := by
         have h3 : ‖e (H i) - f i x‖ < δ i := hH i x
         dsimp only [δ] at h1 h2 h3 ⊢
         linarith

/-- Single-prime specialization of the simultaneous compact selection theorem. -/
theorem exists_monic_irreducible_approx_one (p₀ : PrimeIndex) (E : Set ℤ_[p₀.val]) (hE : IsCompact E)
    (f : LocallyConstant E ℚ_[p₀.val]) (ε : ℝ) (hε : 0 < ε) (floor : ℕ) :
    ∃ F : ℚ[X], F.Monic ∧ Irreducible F ∧ floor ≤ F.natDegree ∧
      ∀ x : E, ‖aeval (x.val : ℚ_[p₀.val]) F - f x‖ < ε := by
  obtain ⟨F,hm,hI,hd,ha⟩ := exists_monic_irreducible_approx (fun _ : Unit ↦ p₀)
    (fun _ _ _ ↦ Subsingleton.elim ..) (fun _ ↦ E) (fun _ ↦ hE) (fun _ ↦ f)
    (fun _ ↦ ε) (fun _ ↦ hε) floor
  exact ⟨F,hm,hI,hd,ha ()⟩

end UnconditionalCounterexample.Hierarchy
