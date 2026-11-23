import UnconditionalCounterexample.Variations.GuardUnramified
import UnconditionalCounterexample.Variations.GuardResidueTuples
import UnconditionalCounterexample.Variations.IndependentTuples

/-!
# Independent guard lifts in unramified extensions

Within each prescribed Witt residue class, changing a lift by p times an
element of the p-adic base gives uncountably many integral candidates.
Choose the coordinates successively outside the algebraic locus of their
predecessors.
-/

noncomputable section

namespace UnconditionalCounterexample.Variations.GuardUnramified

open IndependentTuples

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [Algebra (ZMod p) k]

instance : CharZero (LocalField p k) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (LocalField p k)).injective

private theorem exists_next {A : Type*} [CommRing A] [IsDomain A] [Countable A]
    [Algebra A (LocalField p k)] [FaithfulSMul A (LocalField p k)] (c : k) :
    ∃ w : WittVector p k, w.coeff 0 = c ∧
      Transcendental A (algebraMap (WittVector p k) (LocalField p k) w) := by
  let O := WittVector p k
  let L := LocalField p k
  let b := WittVector.teichmuller p c
  let ψ (z : ℚ_[p]) : L := algebraMap O L b + (p : L) * algebraMap ℚ_[p] L z
  have hp : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective ψ := by
    intro x y h
    exact (algebraMap ℚ_[p] L).injective (mul_left_cancel₀ hp (add_left_cancel h))
  have bad := (countable_algebraic (A := A) (L := L)).preimage hinj
  have dense := bad.dense_compl ℚ_[p]
  obtain ⟨z, hz, hgood⟩ := dense.inter_open_nonempty (Metric.ball 0 1) Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self zero_lt_one⟩
  let a : ℤ_[p] := ⟨z, (by simpa [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < 1).le⟩
  let w : O := b + (p : O) * algebraMap ℤ_[p] O a
  use w
  constructor
  · change WittVector.constantCoeff (b + (p : O) * algebraMap ℤ_[p] O a) = _
    rw [map_add, map_mul, map_natCast, CharP.cast_eq_zero k p, zero_mul, add_zero]
    exact WittVector.teichmuller_coeff_zero p c
  · have he : algebraMap O L w = ψ z := by
      dsimp only [w, ψ]
      rw [map_add, map_mul, map_natCast, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L]
      rfl
    rw [he]
    exact hgood

/-- Actual algebraically independent integral lifts with specified residues. -/
theorem exists_lifts (n : ℕ) (a : Fin n → k) :
    ∃ w : Fin n → WittVector p k, (∀ i, (w i).coeff 0 = a i) ∧
      AlgebraicIndependent ℚ (fun i => algebraMap _ (LocalField p k) (w i)) := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, fun i => i.elim0,
      algebraicIndependent_empty_type_iff.mpr (algebraMap ℚ (LocalField p k)).injective⟩
  | succ n ih =>
    obtain ⟨w, hred, hI⟩ := ih (fun i => a i.succ)
    let y (i : Fin n) := algebraMap (WittVector p k) (LocalField p k) (w i)
    let A := Algebra.adjoin ℚ (Set.range y)
    have : Countable A := hI.aevalEquiv.surjective.countable
    obtain ⟨z, hz, ht⟩ := exists_next p k (A := A) (a 0)
    let x := algebraMap (WittVector p k) (LocalField p k) z
    refine ⟨Fin.cons z w, Fin.cases hz hred, ?_⟩
    have hf := (hI.option_iff_transcendental x).mpr ht
    convert hf.comp (finSuccEquiv n) (finSuccEquiv n).injective using 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

open MvPolynomial

/-- A fixed prime admits a guard in an actual finite unramified field.
The tuple avoids all the listed primitive reductions, its first coordinate
generates the integral ring, and its residue separates it from rational sites. -/
theorem exists_guard_tuple (r bound : ℕ)
    (S : Finset (MvPolynomial (Fin (r+1)) ℤ))
    (hS : ∀ f ∈ S, map (Int.castRingHom (ZMod p)) f ≠ 0) :
    ∃ e > bound, e.Prime ∧ ∃ w : Fin (r+1) → WittVector p (GaloisField p e),
      AlgebraicIndependent ℚ (fun i => algebraMap _ (LocalField p (GaloisField p e)) (w i)) ∧
      Algebra.adjoin ℤ_[p] ({w 0} : Set (WittVector p (GaloisField p e))) = ⊤ ∧
      (w 0).coeff 0 ∉ Set.range (algebraMap (ZMod p) (GaloisField p e)) ∧
      ∀ f ∈ S, IsUnit (eval₂Hom (Int.castRingHom _) w f) := by
  classical
  let S' := S.image (map (Int.castRingHom (ZMod p)))
  have hS' : ∀ f ∈ S', f ≠ 0 := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    exact hS _ hg
  obtain ⟨e, he, hp, a, _, hgen, hout, havoid⟩ := GuardResidueTuples.exists_guard p r bound S' hS'
  let E := GaloisField p e
  obtain ⟨w, hr, hi⟩ := exists_lifts p E (r+1) a
  refine ⟨e, he, hp, w, hi, adjoin_lift_eq_top p E _ (hr 0 ▸ hgen), hr 0 ▸ hout, ?_⟩
  intro f hf
  let O := WittVector p E
  let red : O →+* E := WittVector.constantCoeff
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  have h := havoid (map (Int.castRingHom (ZMod p)) f) (Finset.mem_image_of_mem _ hf)
  change eval₂Hom (algebraMap (ZMod p) E) a _ ≠ 0 at h
  rw [eval₂Hom_map_hom] at h
  change red (eval₂Hom (Int.castRingHom O) w f) ≠ 0
  rw [map_eval₂Hom]
  rw [show (fun i => red (w i)) = a from funext hr,
    show red.comp (Int.castRingHom O) = (algebraMap (ZMod p) E).comp (Int.castRingHom _) from Subsingleton.elim _ _]
  exact h

end UnconditionalCounterexample.Variations.GuardUnramified
