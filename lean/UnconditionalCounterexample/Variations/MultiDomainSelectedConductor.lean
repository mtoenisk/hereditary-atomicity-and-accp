import UnconditionalCounterexample.Variations.MultiDomainFibreIntegrality
import UnconditionalCounterexample.Variations.MultiDomainRealized
import UnconditionalCounterexample.Variations.MultiDomainConductorFibres
import UnconditionalCounterexample.Variations.DimensionSelectedConductor

/-! # Integer conductors in the two selected multivariate domains -/

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations MultiDomain LocalAlgebra
  MultivariateRecovery RadicalConductor TransportedIntegralImage
open scoped TensorProduct

variable (r : ℕ) (q : PrimeIndex) (upper : Bool)

local notation "L" => realizedLocal r q upper
local notation "G" => standardGeometry r
local notation "c" => flagPoint r
local notation "D₀" => selectedData L G
local notation "B" => poleAlgebra D₀
local notation "M" => localPoles q c upper G

private theorem fixed_flag : (fun i ↦ algebraMap ℚ GeometricField (c i)) ∈ (standardGeometry r).fixed := by
  change algebraMap ℚ GeometricField ∘ c ∈ (standardGeometry r).fixed
  simp [standardGeometry]

set_option maxHeartbeats 1200000 in
private theorem local_power (p : PrimeIndex) (S D : Subring B)
    (hSD : S ≤ D) (hw : HasBoundedLocalWords q c upper G S)
    (hclear : ∀ b : B, ∃ n : ℕ, 0 < n ∧ (n : B)*b ∈ S)
    (hint : ∀ i : (localFibre q c upper G p).Component (withPoint upper q p), ∀ d : D,
      ‖rationalFibreEval L G c (flagPoint_retained L) p (withPoint upper q p) i (d : B)‖ ≤ 1)
    (n : ℕ) (hn : (n : B)*algebraMap (Poly r) B (TPoly r) ∈ S) :
    ∃ k : ℕ, (¬p.val ∣ n → k = 0) ∧ ∀ z ∈ IntegralTensorImage.image p.val B D,
      (p.val : ℚ_[p.val] ⊗[ℚ] B)^k*z ∈ IntegralTensorImage.image p.val B S := by
  classical
  let : IsLocalization M B := inferInstanceAs (IsLocalization (denominators D₀) _)
  let F := localFibre q c upper G p
  let extra := withPoint upper q p
  let P := MvPolynomial (Fin (r+1)) ℚ_[p.val]
  let A := Localization ((localPoles q c upper (standardGeometry r)).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val])))
  let e := tensorEquiv (K := ℚ_[p.val]) M B A
  let v := selectedPointEval q c upper G (fixed_flag r) p A
  let b : B := algebraMap (Poly r) B (TPoly r)
  have hev (i : F.Component extra) (x : B) : v i (baseElement (K := ℚ_[p.val]) M A x) =
      rationalFibreEval L G c (flagPoint_retained L) p extra i x := by
    apply closedPointEval_baseElement (k := ℚ) (K := ℚ_[p.val]) M A (localSites q c upper G p i) (retained_local_sites q c upper G (fixed_flag r) p i) (ev := (rationalFibreEval L G c (flagPoint_retained L) p extra i).toRingHom)
    intro f
    exact (closedPointEval_polynomial _ _ _ _ f)
  have hv (i : F.Component extra) (d : D) :
      ‖v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] (d : B)))‖ ≤ 1 :=
    (hev i d) ▸ hint i d
  have hk : (⨅ i, RingHom.ker (v i).toRingHom) ≤ conductorIdeal (image p.val B A e S) := by
    rw [selected_point_conductor q c upper G (fixed_flag r) p S hw hclear
      (fun i t ↦ hv i ⟨t,hSD t.property⟩)]
    intro z hz
    apply RingHom.mem_ker.mpr
    exact funext fun i ↦ (Ideal.mem_iInf.mp hz i : v i z = 0)
  by_cases hp : p.val ∣ n
  · have hs : Function.Surjective (AlgHom.pi v) := by
      intro y
      obtain ⟨f,hf⟩ := closedPointValues_surjective (localSites q c upper G p)
        (F.guard.points_generate _) (F.points_injective c extra) y
      refine ⟨algebraMap P A f,funext fun i ↦ ?_⟩
      exact (closedPointEval_polynomial _ A _ (retained_local_sites q c upper G (fixed_flag r) p i) f).trans (congrFun hf i)
    obtain ⟨k,hk'⟩ := F.guard.exceptional_tensor_power e S D v hs hclear hv hk
    exact ⟨k,fun h ↦ (h hp).elim,tensor_power_of_transport p.val S D e k hk'⟩
  · have hx (s : F.Side extra) : ‖F.sidePoints c extra s 0‖ ≤ 1 := by
      cases h : F.primary with
      | none => simp [Fibre.sidePoints,h]
      | some a =>
        rw [Fibre.sidePoints,h,Option.elim_some]
        exact le_of_not_gt (fun hlt ↦ (a.2.integral 0).not_gt (by
          simpa only [map_one] using (Padic.norm_lt_norm_iff_mulValuation_lt.mp
            (show ‖(1 : ℚ_[p.val])‖ < _ from (norm_one (α := ℚ_[p.val])).trans_lt hlt))))
    have hc (i : F.Component extra) : v i (e ((1 : ℚ_[p.val]) ⊗ₜ[ℚ] b)) =
        F.guard.points (F.sidePoints c extra) i 0 := by
      exact (hev i b).trans ((rationalFibreEval_polynomial L G c (flagPoint_retained L) p extra i (TPoly r)).trans
        (MvPolynomial.eval₂_X _ _ _))
    have hsub := F.guard.good_tensor_inclusion e S D v b n hn hp (F.sidePoints c extra) hx hc hv hk
    exact ⟨0,fun _ ↦ rfl,tensor_power_of_transport p.val S D e 0 (fun z hz ↦ by simpa using hsub hz)⟩

private theorem selected_integer_conductor {D : Type*} [CommRing D] [IsDomain D]
    (i : D →+* ordinary D₀) (hi : Function.Injective i)
    (hpoint : upper = true → ∀ z : D, point D₀ c (flagPoint_retained L) (i z) ∈ PointPullback.localRationals q.val)
    (T : Subring D) (hT : ¬ Factorization.IsBFDomain T) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : D, (m : D)*z ∈ T := by
  classical
  let C := realizedChoices (r := r) q upper
  let f := intoPole.comp i
  let S := T.map f
  let R := requirements L G
  have hmem (y : T) : ProfileChoices.inPole (i (y : D)) ∈ S := ⟨y,y.property,rfl⟩
  have hh := C.generic_recovery R (all_points r) (all_ideals r) rfl rfl
    (i.comp T.subtype) (hi.comp Subtype.val_injective) hT (RationalHull.hull S)
    (fun y ↦ Algebra.subset_adjoin (hmem y))
  have hw := hasBoundedLocalWords_of_nonBF q c upper G C rfl rfl (i.comp T.subtype)
    (hi.comp Subtype.val_injective) hT S hmem
  apply C.integer_conductor R (all_points r) (all_ideals r) rfl rfl i hi T hT
  intro n _
  dsimp only
  intro hn
  have hloc (p : PrimeIndex) := local_power r q upper p S f.range (by
    rintro x ⟨z,_,rfl⟩; exact ⟨z,rfl⟩) hw (RationalHull.exists_nat_mul_mem_of_hull_eq_top S hh)
    (fun j d ↦ by
      obtain ⟨z,hz⟩ := d.property
      rw [← hz]
      apply norm_rationalFibreEval L G c (flagPoint_retained L) p _ j (i z)
      intro h _
      have h' : upper = true ∧ p = q := by simpa [withPoint] using h
      obtain ⟨_,rfl⟩ := h'
      exact hpoint (by assumption) z) n hn
  constructor
  · intro p _
    obtain ⟨k,_,h⟩ := hloc p
    exact ⟨k,h⟩
  · intro p hp
    obtain ⟨k,e,h⟩ := hloc p
    intro z hz
    simpa only [e hp,pow_zero,one_mul] using h z hz

/-- The ordinary domain has an integer conductor into each non-BF subring. -/
theorem ordinary_integer_conductor (r : ℕ) (q : PrimeIndex)
    (T : Subring (ordinary (selectedData (realizedLocal r q false) (standardGeometry r))))
    (hT : ¬ Factorization.IsBFDomain T) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : ordinary (selectedData (realizedLocal r q false) (standardGeometry r)), (m : _) * z ∈ T :=
  selected_integer_conductor r q false (RingHom.id _) Function.injective_id (by simp) T hT

/-- The point pullback has an integer conductor into each non-BF subring. -/
theorem pullback_integer_conductor (r : ℕ) (q : PrimeIndex)
    (T : Subring (pullback (selectedData (realizedLocal r q true) (standardGeometry r))
      (flagPoint r) (flagPoint_retained (realizedLocal r q true)) q.val))
    (hT : ¬ Factorization.IsBFDomain T) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : pullback (selectedData (realizedLocal r q true) (standardGeometry r))
      (flagPoint r) (flagPoint_retained (realizedLocal r q true)) q.val, (m : _) * z ∈ T :=
  selected_integer_conductor r q true (toOrdinary _ _ _ _) (toOrdinary_injective _ _ _ _)
    (fun _ ↦ point_toOrdinary_mem _ _ _ _) T hT

end UnconditionalCounterexample.MultivariateSelection
