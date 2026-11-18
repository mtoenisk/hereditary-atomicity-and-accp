import UnconditionalCounterexample.CoefficientApproximation
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Shifted Eisenstein coefficient selection

Modifying the constant and linear terms of (X−1)^d preserves its reduction modulo p
and arranges a value at 1 congruent to p modulo p². The remaining intermediate
coefficients are free for approximation. The shifted Eisenstein criterion gives
irreducibility over ℚ for d ≥ 2.
-/

noncomputable section
open Polynomial
namespace UnconditionalCounterexample.ShiftedEisenstein

/-- Correct only the constant and linear terms of `(X-1)^d`. -/
def residueTemplate {R : Type*} [CommRing R] (d : ℕ) (c e : R) : R[X] :=
  (X - C 1) ^ d + (C (c - (-1) ^ d) + C (e - (c - (-1) ^ d)) * X)

@[simp] theorem residueTemplate_coeff_zero {R : Type*} [CommRing R]
    (d : ℕ) (c e : R) : (residueTemplate d c e).coeff 0 = c := by
  simp [residueTemplate, coeff_zero_eq_eval_zero]

@[simp] theorem residueTemplate_eval_one {R : Type*} [CommRing R]
    (d : ℕ) (hd : 0 < d) (c e : R) : (residueTemplate d c e).eval 1 = e := by
  simp [residueTemplate, ne_of_gt hd]

theorem residueTemplate_monic_degree {R : Type*} [CommRing R] [Nontrivial R]
    (d : ℕ) (hd : 2 ≤ d) (c e : R) :
    (residueTemplate d c e).Monic ∧ (residueTemplate d c e).natDegree = d := by
  have hb : ((X - C 1 : R[X]) ^ d).Monic := (monic_X_sub_C 1).pow d
  have hbd : ((X - C 1 : R[X]) ^ d).natDegree = d := by
    rw [(monic_X_sub_C (1 : R)).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hsmall : (C (c - (-1) ^ d) + C (e - (c - (-1) ^ d)) * X).degree <
      ((X - C 1 : R[X]) ^ d).degree := by
    rw [degree_eq_natDegree hb.ne_zero, hbd]
    apply lt_of_le_of_lt (degree_add_le_of_degree_le
      (degree_C_le.trans (by exact_mod_cast Nat.zero_le 1)) (degree_C_mul_X_le _))
    exact_mod_cast (show 1 < d by omega)
  exact ⟨hb.add_of_left hsmall, (natDegree_add_eq_left_of_degree_lt hsmall).trans hbd⟩

/-- Modulo any quotient killing the correction terms, the template is `(X-1)^d`. -/
theorem residueTemplate_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (c e : R)
    (hc : φ c = (-1) ^ d) (he : φ e = 0) :
    (residueTemplate d c e).map φ = (X - C 1) ^ d := by
  simp [residueTemplate, hc, he]

/-- A monic polynomial with a prescribed constant and all remaining coefficients free. -/
def monicFamily {R : Type*} [CommRing R] (n : ℕ) (c : R) (a : Fin n → R) : R[X] := by
  classical
  exact X ^ (n + 1) + ofFn (n + 1) (Fin.cases c a)

theorem monicFamily_monic_degree {R : Type*} [CommRing R] [Nontrivial R]
    (n : ℕ) (c : R) (a : Fin n → R) :
    (monicFamily n c a).Monic ∧ (monicFamily n c a).natDegree = n + 1 := by
  classical
  unfold monicFamily
  constructor
  · exact monic_X_pow_add (ofFn_degree_lt _)
  · rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact ofFn_degree_lt _

@[simp] theorem monicFamily_coeff_zero {R : Type*} [CommRing R]
    (n : ℕ) (c : R) (a : Fin n → R) : (monicFamily n c a).coeff 0 = c := by
  classical
  simp [monicFamily, ofFn_coeff_eq_val_of_lt _ (Nat.zero_lt_succ n)]

@[simp] theorem monicFamily_coeff_succ {R : Type*} [CommRing R]
    (n : ℕ) (c : R) (a : Fin n → R) (j : Fin n) :
    (monicFamily n c a).coeff (j.val + 1) = a j := by
  classical
  have hj : j.val + 1 < n + 1 := Nat.add_lt_add_right j.is_lt 1
  simp only [monicFamily, coeff_add, coeff_X_pow,
    ite_eq_right (ne_of_lt hj), zero_add, ofFn_coeff_eq_val_of_lt _ hj]
  rfl

/-- Matching the constant and free coefficients determines a monic degree-`n+1` polynomial. -/
theorem monicFamily_eq {R : Type*} [CommRing R] [Nontrivial R]
    (n : ℕ) (c : R) (a : Fin n → R) (f : R[X])
    (hf : f.Monic) (hd : f.natDegree = n + 1)
    (hc : f.coeff 0 = c) (ha : ∀ j : Fin n, f.coeff (j.val + 1) = a j) :
    monicFamily n c a = f := by
  classical
  ext i
  rcases lt_trichotomy i (n + 1) with hi | hi | hi
  · cases i with
    | zero => simpa using hc.symm
    | succ i =>
      rw [monicFamily_coeff_succ n c a ⟨i, by omega⟩]
      exact (ha ⟨i, by omega⟩).symm
  · subst i
    rw [← (monicFamily_monic_degree n c a).2, (monicFamily_monic_degree n c a).1.coeff_natDegree]
    rw [(monicFamily_monic_degree n c a).2, ← hd, hf.coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa [(monicFamily_monic_degree n c a).2] using hi),
      coeff_eq_zero_of_natDegree_lt (by simpa [hd] using hi)]

theorem monicFamily_map {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial R] [Nontrivial S] (φ : R →+* S)
    (n : ℕ) (c : R) (a : Fin n → R) :
    (monicFamily n c a).map φ = monicFamily n (φ c) (fun j => φ (a j)) := by
  obtain ⟨hm, hd⟩ := monicFamily_monic_degree n c a
  symm
  apply monicFamily_eq _ _ _ _ (hm.map φ) ((hm.natDegree_map φ).trans hd)
  · simp
  · intro j
    simp

/-- A cleared rational congruence is the actual residue of its integral p-adic model. -/
theorem toZModPow_eq_of_cleared {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) (q : ℚ) (hx : (x : ℚ_[p]) = q)
    (D : ℕ) (z : ℤ) (hD : D ≠ 0) (hpD : ¬p ∣ D)
    (hq : q = (z : ℚ) / D) (s : ℕ) (r : ZMod (p ^ s))
    (hr : (z : ZMod (p ^ s)) = (D : ZMod (p ^ s)) * r) :
    PadicInt.toZModPow s x = r := by
  have hmul : (D : ℤ_[p]) * x = z := by
    apply Subtype.ext
    change (D : ℚ_[p]) * (x : ℚ_[p]) = (z : ℚ_[p])
    rw [hx, hq, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hD)
  have hm := congrArg (PadicInt.toZModPow s) hmul
  simp only [map_mul, map_natCast, map_intCast] at hm
  have hu : IsUnit (D : ZMod (p ^ s)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      (((show p.Prime from Fact.out).coprime_iff_not_dvd.mpr hpD).symm.pow_right s)
  exact hu.mul_left_cancel (hm.trans hr)

/-- The prime itself is nonzero modulo its square. -/
theorem prime_ne_zero_mod_square (p : ℕ) (hp : p.Prime) : (p : ZMod (p ^ 2)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  apply Nat.not_dvd_of_pos_of_lt hp.pos
  simpa only [pow_two, mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos

/-- The two source congruences imply an actual shifted Eisenstein polynomial. -/
theorem isEisensteinAt_shift_of_congruences (p : ℕ) [Fact p.Prime]
    (f : ℤ_[p][X]) (hf : f.Monic)
    (hred : f.map (PadicInt.toZModPow 1) = (X - C 1) ^ f.natDegree)
    (hval : PadicInt.toZModPow 2 (f.eval 1) = (p : ZMod (p ^ 2))) :
    (f.comp (X + C 1)).IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p]) := by
  have hg := hf.comp_X_add_C 1
  have hdeg : (f.comp (X + C 1)).natDegree = f.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hmap : (f.comp (X + C 1)).map (PadicInt.toZModPow 1) = X ^ f.natDegree := by
    rw [map_comp, hred]
    simp
  apply hg.isEisensteinAt_of_mem_of_notMem (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top
  · intro n hn
    rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (p : ℤ_[p]),
      ← PadicInt.ker_toZModPow 1, RingHom.mem_ker]
    have hn' : n ≠ f.natDegree := ne_of_lt (hdeg ▸ hn)
    have hc := congrArg (fun g : (ZMod (p ^ 1))[X] => g.coeff n) hmap
    simpa only [coeff_map, coeff_X_pow, ite_eq_right hn'] using hc
  · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      ← PadicInt.ker_toZModPow 2, RingHom.mem_ker]
    have hc : PadicInt.toZModPow 2 ((f.comp (X + C 1)).coeff 0) = p := by
      simpa only [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C,
        zero_add] using hval
    rw [hc]
    exact prime_ne_zero_mod_square p Fact.out

/-- Shifted Eisenstein irreducibility over the actual p-adic fraction field. -/
theorem irreducible_map_of_shift_congruences (p : ℕ) [Fact p.Prime]
    (f : ℤ_[p][X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    (hred : f.map (PadicInt.toZModPow 1) = (X - C 1) ^ f.natDegree)
    (hval : PadicInt.toZModPow 2 (f.eval 1) = (p : ZMod (p ^ 2))) :
    Irreducible (f.map (algebraMap ℤ_[p] ℚ_[p])) := by
  have hE := isEisensteinAt_shift_of_congruences p f hf hred hval
  have hg := hf.comp_X_add_C 1
  have hdeg : 0 < (f.comp (X + C 1)).natDegree := by
    simpa only [natDegree_comp, natDegree_X_add_C, mul_one] using hd
  have hi := hE.irreducible (inferInstance : (IsLocalRing.maximalIdeal ℤ_[p]).IsPrime) hg.isPrimitive hdeg
  have hfi : Irreducible f := by
    apply (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : ℤ_[p]))).mp
    simpa only [algEquivAevalXAddC_apply, ← comp_eq_aeval] using hi
  exact (hf.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp hfi

/-- Coefficientwise template agreement gives both exact polynomial congruences. -/
theorem family_congruences_of_template (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : 1 ≤ n) (c : ℤ_[p]) (a : Fin n → ℤ_[p])
    (hc : PadicInt.toZModPow 1 c = (-1) ^ (n + 1))
    (ha : ∀ j : Fin n, PadicInt.toZModPow 2 (a j) =
      (residueTemplate (n + 1) (PadicInt.toZModPow 2 c) (p : ZMod (p ^ 2))).coeff (j.val + 1)) :
    (monicFamily n c a).map (PadicInt.toZModPow 1) = (X - C 1) ^ (n + 1) ∧
      PadicInt.toZModPow 2 ((monicFamily n c a).eval 1) = (p : ZMod (p ^ 2)) := by
  have : Nontrivial (ZMod (p ^ 2)) :=
    ⟨⟨p, 0, prime_ne_zero_mod_square p Fact.out⟩⟩
  let φ := ZMod.castHom (pow_dvd_pow p (show 1 ≤ 2 by decide)) (ZMod (p ^ 1))
  let T := residueTemplate (n + 1) (PadicInt.toZModPow 2 c) (p : ZMod (p ^ 2))
  obtain ⟨hT, hdT⟩ := residueTemplate_monic_degree (n + 1) (by omega)
    (PadicInt.toZModPow 2 c) (p : ZMod (p ^ 2))
  have hmap : (monicFamily n c a).map (PadicInt.toZModPow 2) = T := by
    rw [monicFamily_map]
    apply monicFamily_eq _ _ _ _ hT hdT
    · exact residueTemplate_coeff_zero _ _ _
    · intro j
      exact (ha j).symm
  constructor
  · have hφ : φ.comp (PadicInt.toZModPow 2) = PadicInt.toZModPow 1 :=
      PadicInt.zmod_cast_comp_toZModPow 1 2 (by decide)
    rw [← hφ, ← map_map, hmap]
    apply residueTemplate_map
    · exact (congrArg (fun h : ℤ_[p] →+* ZMod (p ^ 1) => h c) hφ).trans hc
    · rw [map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (by simp)
  · have he := congrArg (fun g : (ZMod (p ^ 2))[X] => g.eval 1) hmap
    simpa only [eval_map, ← eval₂_at_apply, map_one, T,
      residueTemplate_eval_one _ (Nat.zero_lt_succ n)] using he

/-- Coefficientwise agreement with the template suffices for local irreducibility. -/
theorem irreducible_family_map_of_template (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : 1 ≤ n) (c : ℤ_[p]) (a : Fin n → ℤ_[p])
    (hc : PadicInt.toZModPow 1 c = (-1) ^ (n + 1))
    (ha : ∀ j : Fin n, PadicInt.toZModPow 2 (a j) =
      (residueTemplate (n + 1) (PadicInt.toZModPow 2 c) (p : ZMod (p ^ 2))).coeff (j.val + 1)) :
    Irreducible ((monicFamily n c a).map (algebraMap ℤ_[p] ℚ_[p])) := by
  obtain ⟨hred, hval⟩ := family_congruences_of_template p n hn c a hc ha
  obtain ⟨hf, hdeg⟩ := monicFamily_monic_degree n c a
  apply irreducible_map_of_shift_congruences p _ hf (by omega) _ hval
  simpa only [hdeg] using hred

/-- Local irreducibility of an integral model implies rational irreducibility. -/
theorem irreducible_of_padic_model (p : ℕ) [Fact p.Prime]
    (f : ℚ[X]) (hf : f.Monic) (g : ℤ_[p][X])
    (hmodel : g.map (algebraMap ℤ_[p] ℚ_[p]) = f.map (algebraMap ℚ ℚ_[p]))
    (hg : Irreducible (g.map (algebraMap ℤ_[p] ℚ_[p]))) : Irreducible f := by
  apply hf.isPrimitive.irreducible_of_irreducible_map_of_injective
    (algebraMap ℚ ℚ_[p]).injective
  rwa [← hmodel]

/-- Denominator support of the fixed constant and free coefficients controls the
entire monic polynomial, including its leading coefficient and zero tail. -/
theorem monicFamily_denominator_support {ι : Type*} (p : ι → ℕ)
    (n : ℕ) (c : ℚ) (a : Fin n → ℚ)
    (hc : ∀ prime : ℕ, prime.Prime → prime ∣ c.den → ∃ i, prime = p i)
    (ha : ∀ j prime, prime.Prime → prime ∣ (a j).den → ∃ i, prime = p i) :
    ∀ k prime, prime.Prime → prime ∣ ((monicFamily n c a).coeff k).den → ∃ i, prime = p i := by
  intro k prime hprime hdiv
  rcases lt_trichotomy k (n + 1) with hk | hk | hk
  · cases k with
    | zero => exact hc prime hprime (by simpa using hdiv)
    | succ k =>
      apply ha ⟨k, by omega⟩ prime hprime
      simpa only [monicFamily_coeff_succ n c a ⟨k, by omega⟩] using hdiv
  · subst k
    have hc1 : (monicFamily n c a).coeff (n + 1) = 1 := by
      rw [← (monicFamily_monic_degree n c a).2,
        (monicFamily_monic_degree n c a).1.coeff_natDegree]
    simp only [hc1, Rat.den_one, Nat.dvd_one] at hdiv
    exact False.elim (hprime.ne_one hdiv)
  · have hc0 : (monicFamily n c a).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by simpa only [(monicFamily_monic_degree n c a).2] using hk)
    simp only [hc0, Rat.den_zero, Nat.dvd_one] at hdiv
    exact False.elim (hprime.ne_one hdiv)

/-- All middle coefficients can simultaneously meet actual local approximation,
finite algebraic avoidance, and shifted Eisenstein irreducibility. The fixed
constant has only the explicitly stated denominator and auxiliary residue conditions. -/
theorem exists_irreducible_approximating_family
    {ι η K : Type*} [Fintype ι] [Field K] [CharZero K]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
    (n : ℕ) (hn : 1 ≤ n) (C0 : ℚ)
    (hCsupp : ∀ prime : ℕ, prime.Prime → prime ∣ C0.den → ∃ i, prime = p i)
    (x : Fin n → ∀ i, ℚ_[p i]) (ε : Fin n → ι → ℝ) (hε : ∀ c i, 0 < ε c i)
    (ell : ℕ) [Fact ell.Prime] (hfresh : ∀ i, p i ≠ ell)
    (c0 : ℤ_[ell]) (hc0 : (c0 : ℚ_[ell]) = C0)
    (hc : PadicInt.toZModPow 1 c0 = (-1) ^ (n + 1))
    (I : Finset η) (P : η → MvPolynomial (Fin n) K) (hP : ∀ j ∈ I, P j ≠ 0) :
    ∃ q : Fin n → ℚ,
      (monicFamily n C0 q).Monic ∧ (monicFamily n C0 q).natDegree = n + 1 ∧
      (monicFamily n C0 q).coeff 0 = C0 ∧ Irreducible (monicFamily n C0 q) ∧
      (∀ k prime, prime.Prime → prime ∣ ((monicFamily n C0 q).coeff k).den → ∃ i, prime = p i) ∧
      (∀ j i, ‖(q j : ℚ_[p i]) - x j i‖ < ε j i) ∧
      (∀ j ∈ I, MvPolynomial.eval (fun c => algebraMap ℚ K (q c)) (P j) ≠ 0) ∧
      ∃ g : ℤ_[ell][X], g.Monic ∧
        g.map (algebraMap ℤ_[ell] ℚ_[ell]) = (monicFamily n C0 q).map (algebraMap ℚ ℚ_[ell]) ∧
        g.map (PadicInt.toZModPow 1) = (X - C 1) ^ (n + 1) ∧
        PadicInt.toZModPow 2 (g.eval 1) = (ell : ZMod (ell ^ 2)) := by
  classical
  let r : Fin n → ZMod (ell ^ 2) := fun j =>
    (residueTemplate (n + 1) (PadicInt.toZModPow 2 c0) (ell : ZMod (ell ^ 2))).coeff (j.val + 1)
  obtain ⟨q, hq, havoid⟩ := CoefficientApproximation.exists_approximating_coefficients_avoiding
    p hinj x ε hε ell Fact.out hfresh 2 r I P hP
  choose a ha using fun j => CoefficientApproximation.exists_padicInt_of_denominator_support
    p (q j) (hq j).1 ell hfresh
  have hres (j : Fin n) : PadicInt.toZModPow 2 (a j) = r j := by
    obtain ⟨D, z, hD, hellD, hquot, hres⟩ := (hq j).2.2
    exact toZModPow_eq_of_cleared (a j) (q j) (ha j) D z hD hellD hquot 2 (r j) hres
  have hirr := irreducible_family_map_of_template ell n hn c0 a hc hres
  have hmodel : (monicFamily n c0 a).map (algebraMap ℤ_[ell] ℚ_[ell]) =
      (monicFamily n C0 q).map (algebraMap ℚ ℚ_[ell]) := by
    rw [monicFamily_map, monicFamily_map]
    exact congrArg₂ (monicFamily n) hc0 (funext ha)
  obtain ⟨hmonic, hdegree⟩ := monicFamily_monic_degree n C0 q
  refine ⟨q, hmonic, hdegree, monicFamily_coeff_zero n C0 q,
    irreducible_of_padic_model ell _ hmonic _ hmodel hirr, ?_, ?_, havoid,
    monicFamily n c0 a, (monicFamily_monic_degree n c0 a).1, hmodel,
    family_congruences_of_template ell n hn c0 a hc hres⟩
  · exact monicFamily_denominator_support p n C0 q hCsupp (fun j => (hq j).1)
  · exact fun j => (hq j).2.1

/-- Exponents divisible by `ell-1` make the processed-prime denominator equal to
one modulo the fresh auxiliary prime, exactly as in the source construction. -/
theorem supported_denominator_residue_one {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (ell : ℕ) [Fact ell.Prime]
    (hcop : ∀ i, (p i).Coprime ell) (e : ι → ℕ) :
    ((∏ i, p i ^ ((ell - 1) * e i) : ℕ) : ZMod ell) = 1 := by
  simp only [Nat.cast_prod, Nat.cast_pow, pow_mul]
  have hone (i : ι) : (p i : ZMod ell) ^ (ell - 1) = 1 := by
    apply ZMod.pow_card_sub_one_eq_one
    exact (ZMod.isUnit_iff_coprime _ _).mpr (hcop i) |>.ne_zero
  simp only [hone, one_pow, Finset.prod_const_one]

/-- The source's signed reciprocal denominator has the required actual auxiliary
integral model whenever that denominator is one modulo the auxiliary prime. -/
theorem exists_signed_reciprocal_model (ell : ℕ) [Fact ell.Prime]
    (d D : ℕ) (hD : (D : ZMod ell) = 1) :
    ∃ c : ℤ_[ell], (c : ℚ_[ell]) = (((-1 : ℚ) ^ d / D : ℚ) : ℚ_[ell]) ∧
      PadicInt.toZModPow 1 c = (-1) ^ d := by
  have hD0 : D ≠ 0 := by
    intro h
    simp only [h, Nat.cast_zero, zero_ne_one] at hD
  have hellD : ¬ell ∣ D := by
    intro h
    have : (D : ZMod ell) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    exact zero_ne_one (this.symm.trans hD)
  have hden : (((-1 : ℚ) ^ d) / D).den ∣ D := by
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
      CoefficientApproximation.denominator_divides ((-1 : ℤ) ^ d) D
  have hnorm : ‖((((-1 : ℚ) ^ d) / D : ℚ) : ℚ_[ell])‖ ≤ 1 :=
    Padic.norm_rat_le_one (fun h => hellD (h.trans hden))
  let c : ℤ_[ell] := ⟨(((-1 : ℚ) ^ d) / D : ℚ), hnorm⟩
  refine ⟨c, rfl, ?_⟩
  apply toZModPow_eq_of_cleared c _ rfl D ((-1 : ℤ) ^ d) hD0 hellD
    (by simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]) 1 ((-1) ^ d)
  have hmod : Nat.ModEq ell D 1 :=
    (ZMod.natCast_eq_natCast_iff D 1 ell).mp (by simpa only [Nat.cast_one] using hD)
  have hD1 : (D : ZMod (ell ^ 1)) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff D 1 (ell ^ 1)).mpr
      (by simpa only [pow_one] using hmod)
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, hD1, one_mul]

end UnconditionalCounterexample.ShiftedEisenstein
