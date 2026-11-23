import UnconditionalCounterexample.Variations.DimensionRecoveryStage
import UnconditionalCounterexample.Variations.DimensionScheduleContent

noncomputable section
namespace UnconditionalCounterexample.Variations

open MvPolynomial Filter LocalAlgebra RadicalConductor LocalAlgebra.TransportedIntegralImage
open scoped Topology TensorProduct

variable {σ ι : Type*} [Fintype σ] [Finite ι] {p : ℕ} [Fact p.Prime]
    {B A : Type*} [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ_[p] A]
    [Algebra (MvPolynomial σ ℚ_[p]) A] [IsScalarTower ℚ_[p] (MvPolynomial σ ℚ_[p]) A]
    {E : ι → Type*} [∀ i, NontriviallyNormedField (E i)] [∀ i, NormedAlgebra ℚ_[p] (E i)]
    [∀ i, IsUltrametricDist (E i)] [∀ i, FiniteDimensional ℚ_[p] (E i)]

/-- An infinite family of bounded-exponent words yields a single exponent and a sequence
of stages tending to infinity after any prescribed starting stage. -/
theorem exists_fixed_word_exponent {W : ℕ → Type*} (a : ∀ n, W n → ℕ)
    (P : ∀ n, W n → Prop) (b N₀ : ℕ)
    (h : {n : ℕ | ∃ w, a n w ≤ b ∧ P n w}.Infinite) :
    ∃ e ≤ b, ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      ∀ n, N₀ ≤ j n ∧ ∃ w, a (j n) w = e ∧ P (j n) w := by
  have hf : ∃ᶠ n : ℕ in atTop, ∃ e : Fin (b+1), ∃ w, a n w = e.val ∧ P n w := by
    rw [frequently_atTop]
    intro N
    obtain ⟨n,hn,hle⟩ := h.exists_gt N
    obtain ⟨w,hw,hP⟩ := hn
    exact ⟨n,hle.le,⟨a n w,by omega⟩,w,rfl,hP⟩
  obtain ⟨e,he⟩ := frequently_exists.mp hf
  obtain ⟨j,hj,h⟩ := exists_seq_forall_of_frequently (he.and_eventually (eventually_ge_atTop N₀))
  exact ⟨e.val,by omega,j,hj,fun n ↦ ⟨(h n).2,(h n).1⟩⟩

private theorem exists_common_power {R : Type*} [CommRing R] (U : Subring R) (π : R) (hπ : π ∈ U)
    (z : σ → R) (h : ∀ j, ∃ k : ℕ, π^k * z j ∈ U) : ∃ s : ℕ, ∀ j, π^s * z j ∈ U := by
  classical
  choose k hk using h
  refine ⟨Finset.univ.sup k,fun j ↦ ?_⟩
  obtain ⟨l,hl⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := k) (Finset.mem_univ j))
  rw [hl, add_comm, pow_add, mul_assoc]
  exact U.mul_mem (U.pow_mem hπ l) (hk j)

omit [Fintype σ] in
private theorem scaled_polynomial_mem {K : Type*} [NontriviallyNormedField K] {Z : Type*} [CommRing Z]
    [Algebra K Z] (U : Subring Z) (z : σ → Z) (s t : K) (hs : s ≠ 0)
    (hscalar : ∀ c : K, ‖c‖ ≤ 1 → algebraMap K Z c ∈ U)
    (hz : ∀ j, algebraMap K Z s * z j ∈ U) (W : MvPolynomial σ K)
    (hW : ∀ m, ‖scaledCoefficient s t m W‖ ≤ 1) : algebraMap K Z t * aeval z W ∈ U := by
  obtain ⟨v, hv, heq⟩ := evaluated_congruence_of_scaledCoefficient U z s t 1 1 hs one_ne_zero hscalar hz W 0
    (fun m _ ↦ by simpa using hW m)
  simp only [mul_one, map_zero, mul_zero, sub_zero, map_one, one_mul] at heq
  exact heq ▸ hv

/-- The local conductor equality for a fixed uniform exponent along arbitrary late stages.
All stage inputs below are precise consequences of the chosen polynomial's local
neighborhood. Only the much weaker arithmetic condition of membership of the recovered
words depends on the subring T. -/
theorem conductor_of_scheduled_local_words
    (M : Submonoid (MvPolynomial σ ℚ_[p])) [IsLocalization M A] [IsNoetherianRing A]
    (e : ℚ_[p] ⊗[ℚ] B ≃ₐ[ℚ_[p]] A) (T : Subring B)
    (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B) * b ∈ T)
    (u : ∀ i, σ → E i) (ev : ∀ i, A →ₐ[ℚ_[p]] E i)
    (hev : ∀ i (F : MvPolynomial σ ℚ_[p]), ev i (algebraMap _ A F) = aeval (u i) F)
    (hgen : ∀ i, Algebra.adjoin ℚ_[p] (Set.range (u i)) = ⊤)
    (hdist : Function.Injective fun i ↦ RingHom.ker (aeval (R := ℚ_[p]) (u i)).toRingHom)
    (hval : ∀ i (t : T), ‖ev i (e ((1 : ℚ_[p]) ⊗ₜ[ℚ] (t : B)))‖ ≤ 1)
    (G : RecoveryGenerators (K := ℚ_[p]) u) (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
    (F H : ℕ → MvPolynomial σ ℚ_[p]) (N : ℕ → ℕ) (a : ℕ)
    (w : ℕ → image p B A e T)
    (hw : ∀ n, algebraMap _ A ((F n)^a) = algebraMap _ A (H n) * (w n : A))
    (hH : ∀ i n, aeval (u i) (H n) ≠ 0)
    (hb : ∀ n s, s ≤ j n → RecoveryGenerators.denScale (p : ℚ_[p]) Padic.norm_p_lt_one s (H n) + j n * j n ≤
      (G.genScale (p : ℚ_[p]) Padic.norm_p_lt_one s + N n) * a)
    (hc : ∀ n s, s ≤ j n → ∀ m,
      ‖(p : ℚ_[p])^(N n) * scaledCoefficient ((p : ℚ_[p])^s) ((p : ℚ_[p])^(G.genScale _ Padic.norm_p_lt_one s)) m (F n) -
        scaledCoefficient ((p : ℚ_[p])^s) ((p : ℚ_[p])^(G.genScale _ Padic.norm_p_lt_one s)) m (G.direction (p : ℚ_[p]) (j n))‖ ≤ ‖(p : ℚ_[p])‖^(j n * j n))
    (hg : ∀ i n, ∃ α : E i, ‖α⁻¹‖ ≤ ‖(p : ℚ_[p])‖^(j n * j n) ∧
        ‖α⁻¹ • residueWordGradient (u i) (F n) (H n) a -
          ∑ l : Fin G.count, ((p : E i)^(j n))^l.val • (fun k ↦ aeval (u i) (pderiv k (G.gen l)))‖ ≤
          ‖(p : ℚ_[p])‖^(j n * j n)) :
    conductorIdeal (image p B A e T) = ⨅ i, RingHom.ker (ev i) := by
  classical
  let U := image p B A e T
  let φ := algebraMap (MvPolynomial σ ℚ_[p]) A
  let z (l : σ) := φ (X l)
  have evalz (P : MvPolynomial σ ℚ_[p]) : aeval z P = φ P := by
    simpa [z, φ, aeval_X_left_apply] using (comp_aeval_apply (X : σ → MvPolynomial σ ℚ_[p]) (IsScalarTower.toAlgHom ℚ_[p] (MvPolynomial σ ℚ_[p]) A) P).symm
  have hscalar (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) : algebraMap ℚ_[p] A c ∈ U :=
    scalar_mem p B A e T c ((PadicInt.mem_subring_iff p).mpr hc)
  obtain ⟨s, hs⟩ := exists_common_power U (p : A) (natCast_mem U p) z
    (fun l ↦ exists_power_mul_mem p B A e T hclear (z l))
  have hπ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let c := G.genScale (p : ℚ_[p]) Padic.norm_p_lt_one s
  have hcoord (l : σ) : algebraMap ℚ_[p] A ((p : ℚ_[p])^s) * z l ∈ U := by simpa using hs l
  let v (l : Fin G.count) : U := ⟨(p : A)^c * φ (G.gen l), by
    simpa only [map_pow, map_natCast, evalz] using scaled_polynomial_mem U z _ _ (pow_ne_zero _ hπ) hscalar hcoord
      (G.gen l) (G.genScale_spec _ Padic.norm_p_lt_one s l)⟩
  let P := schedulePolynomial v
  have heval (n : ℕ) : (P.map U.subtype).eval ((p : A)^n) = (p : A)^c * φ (G.direction (p : ℚ_[p]) n) := by
    simp [P, schedulePolynomial, v, RecoveryGenerators.direction, Polynomial.map_sum, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, Algebra.smul_def, φ, Finset.mul_sum, mul_comm, mul_left_comm]
  have hsurj : Function.Surjective (AlgHom.pi ev) := by
    intro y
    obtain ⟨Q,hQ⟩ := closedPointValues_surjective u hgen hdist y
    exact ⟨φ Q,funext fun i ↦ (hev i Q).trans (congrFun hQ i)⟩
  apply tensorImage_conductor_eq p B A e T ev hsurj hval hclear P a
  · rw [schedulePolynomial_map]
    let b := Units.mk0 ((p : ℚ_[p])^c) (pow_ne_zero _ hπ)
    change (schedulePolynomial (fun j ↦ (p : A)^c * φ (G.gen j))).contentIdeal = _
    simpa only [b, Units.val_mk0, map_pow, map_natCast] using localized_schedule_content G M ev hev b
  · intro m
    obtain ⟨n,hn⟩ := (hj.eventually_ge_atTop (max s m)).exists
    have hsn := (le_max_left ..).trans hn
    let l := j n
    let b := RecoveryGenerators.denScale (p : ℚ_[p]) Padic.norm_p_lt_one s (H n)
    have hd : (p : A)^b * φ (H n) ∈ U := by
      simpa only [map_pow, map_natCast, evalz] using scaled_polynomial_mem U z _ _ (pow_ne_zero _ hπ) hscalar hcoord
        (H n) (RecoveryGenerators.denScale_spec _ Padic.norm_p_lt_one s (H n))
    obtain ⟨δ,hδ,hdif⟩ := evaluated_congruence_of_scaledCoefficient U z _ ((p : ℚ_[p])^c) ((p : ℚ_[p])^(l*l))
      ((p : ℚ_[p])^(N n)) (pow_ne_zero _ hπ) (pow_ne_zero _ hπ) hscalar hcoord (F n) (G.direction _ l)
      (fun m _ ↦ by simpa only [norm_pow] using hc n s hsn m)
    let Z := (p : A)^(c+N n) * φ (F n)
    have hz : Z - (P.map U.subtype).eval ((p : A)^l) = (p : A)^(l*l) * δ := by
      simpa only [Z, heval, ← pow_add, map_pow, map_natCast, evalz] using hdif
    have hpoly : (P.map U.subtype).eval ((p : A)^l) ∈ U := by
      let u : U := ⟨(p : A)^l, U.pow_mem (natCast_mem U p) _⟩
      exact (Polynomial.eval_map_apply U.subtype u) ▸ (P.eval u).property
    have hzmem : Z ∈ U := by
      rw [sub_eq_iff_eq_add.mp hz]
      exact U.add_mem (U.mul_mem (U.pow_mem (natCast_mem U p) _) hδ) hpoly
    refine ⟨l, (le_max_right ..).trans hn, ⟨Z,hzmem⟩, ⟨δ,hδ⟩, hz, ?_⟩
    have hu : (localPrimeUnit p A : A) = (p : A) := by simp [localPrimeUnit]
    have hscl := scaled_word_power_mem U (localPrimeUnit p A) (hu ▸ natCast_mem U p) (φ (F n)) (φ (H n)) (w n) a (c+N n) b (l*l) (w n).property
      (hu ▸ hd) (by simpa [φ] using hw n) (hb n s hsn)
    change (↑(localPrimeUnit p A)⁻¹ : A)^(l*l) * Z^a ∈ U
    simpa only [hu, Z] using hscl
  · intro i
    apply unbounded_leibniz_of_word_gradients M (u i) (ev i) (hev i) U F H (fun _ ↦ a) w hw (hH i)
    intro L hL
    choose α ha herr using hg i
    have heq : ‖(p : E i)‖ = ‖(p : ℚ_[p])‖ := by rw [← map_natCast (algebraMap ℚ_[p] (E i)) p, norm_algebraMap']
    have hpi : (p : E i) ≠ 0 := norm_pos_iff.mp (heq ▸ norm_pos_iff.mpr hπ)
    apply gradient_direction_tendsto_atTop _ (closedPoint_generator_gradients_span u hgen hdist G.gen G.span i)
      (p : E i) hpi (heq ▸ Padic.norm_p_lt_one) j hj _ α _ _ L hL
    · exact Filter.Eventually.of_forall (fun n ↦ heq ▸ ha n)
    · exact Filter.Eventually.of_forall (fun n ↦ heq ▸ herr n)

end UnconditionalCounterexample.Variations
