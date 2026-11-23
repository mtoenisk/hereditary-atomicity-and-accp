import UnconditionalCounterexample.Variations.MultivariateSelectionActual
import UnconditionalCounterexample.Variations.DimensionScheduledConductor
import UnconditionalCounterexample.Variations.DimensionClosedEvaluation
import UnconditionalCounterexample.Variations.MultivariateWordRecovery
import UnconditionalCounterexample.Variations.MultiDomainLowRecovery

noncomputable section
namespace UnconditionalCounterexample.MultivariateSelection

open MvPolynomial GuardSupport Variations LocalAlgebra TransportedIntegralImage MultivariateRecovery RadicalConductor
open scoped Topology TensorProduct

variable {r : ℕ} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable (q : PrimeIndex) (c : Fin (r+1) → ℚ) (upper : Bool) (G : Geometry r K)
variable (hc : (fun i => algebraMap ℚ K (c i)) ∈ G.fixed)

abbrev localRaw (n : ℕ) := siteRaw (actualPrescription q c upper) G n
abbrev localHistory (n : ℕ) := fun j : Fin n ↦ siteChain (actualPrescription q c upper) G j.val
abbrev localPoles := Submonoid.closure (Set.range (localRaw q c upper G))
abbrev localFibre (p : PrimeIndex) := permanentFibre (actualPrescription q c upper) G p

abbrev localSites (p : PrimeIndex) := (localFibre q c upper G p).guard.points
  ((localFibre q c upper G p).sidePoints c (withPoint upper q p))

include hc in
theorem retained_local_sites (p : PrimeIndex) (i : (localFibre q c upper G p).Component (withPoint upper q p)) :
    ∀ m : (localPoles q c upper G).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val])),
      aeval (localSites q c upper G p i) m.val ≠ 0 := by
  apply retained_of_factor_values
  intro n
  let f := localFibre q c upper G p
  let L := actualPrescription q c upper
  have hcn := clean_actual L G c hc (n+1) (⟨n,by omega⟩ : Fin (n+1))
  let x := localSites q c upper G p i
  change eval₂Hom (algebraMap ℚ _) x _ ≠ 0
  rw [show algebraMap ℚ (f.guard.Field i) = Rat.castHom _ from Subsingleton.elim ..]
  exact f.componentEval_ne_zero c _ i _ (raw_irreducible (requirements L G) n).ne_zero hcn

def selectedPointEval (p : PrimeIndex) (A : Type*) [CommRing A] [Algebra ℚ_[p.val] A]
    [Algebra (MvPolynomial (Fin (r+1)) ℚ_[p.val]) A] [IsScalarTower ℚ_[p.val] (MvPolynomial (Fin (r+1)) ℚ_[p.val]) A]
    [IsLocalization ((localPoles q c upper G).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) A]
    (i : (localFibre q c upper G p).Component (withPoint upper q p)) :=
  closedPointEval _ A (localSites q c upper G p i) (retained_local_sites q c upper G hc p i)

/-- The actual words in the rational subring, with the stage exponent and cleared
denominator in the chronological word list. -/
def HasBoundedLocalWords {B : Type*} [CommRing B] [Algebra (Poly r) B] (T : Subring B) :=
  ∃ b : ℕ, {n : ℕ | ∃ w : triangularWords n (localHistory q c upper G n), w.val.1 ≤ b ∧
    ∃ x ∈ T, algebraMap (Poly r) B ((localRaw q c upper G n) ^ w.val.1) =
      algebraMap (Poly r) B w.val.2 * x}.Infinite

/-- The cofinal bounded-exponent statement in the horizontal function field supplies
literal cleared word relations in the original subring. -/
theorem hasBoundedLocalWords_of_normalized {B L : Type*} [CommRing B] [Algebra (Poly r) B]
    [IsLocalization (localPoles q c upper G) B] [Field L] (T : Subring B)
    (φ : B →+* L) (hφ : Function.Injective φ) (b : ℕ)
    (h : {n : ℕ | ∃ w : BoundedWord n, w.latestExponent ≤ b ∧ ∃ x ∈ T,
      φ x = normalizedWord (φ.comp (algebraMap (Poly r) B)) (localRaw q c upper G) w}.Infinite) :
    HasBoundedLocalWords q c upper G T := by
  classical
  let R := requirements (actualPrescription q c upper) G
  let F := localRaw q c upper G
  let f := φ.comp (algebraMap (Poly r) B)
  have hreg : localPoles q c upper G ≤ nonZeroDivisors (Poly r) := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i,rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (raw_irreducible R i).ne_zero
  have hinj : Function.Injective f := hφ.comp (IsLocalization.injective B hreg)
  have hn (i : ℕ) : f (F i) ≠ 0 := (map_ne_zero_iff f hinj).mpr
    (raw_irreducible R i).ne_zero
  refine ⟨b,h.mono ?_⟩
  rintro n ⟨w,hb,x,hx,he⟩
  let D := denominator F w
  have hlisted : (w.latestExponent,D) ∈ triangularWords n (localHistory q c upper G n) :=
    normalized_word_listed R w
  refine ⟨⟨(w.latestExponent,D),hlisted⟩,hb,x,hx,?_⟩
  have hD : f D ≠ 0 := by
    simp only [D,denominator,map_prod,map_pow]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hn i))
  apply hφ
  have heq := ((eq_div_iff hD).mp (he.trans (word_eq_fraction f F hn w))).symm
  simpa only [f, RingHom.comp_apply, map_mul, mul_comm] using heq

/-- An actual non-BF source subring of either selected domain supplies the bounded
word hypotheses for every arithmetic fibre at once. -/
theorem hasBoundedLocalWords_of_nonBF {D : MultiDomain.Data (r+1)} (C : MultiDomain.ProfileChoices D)
    (hraw : D.raw = localRaw q c upper G) (hE : C.E = normalizationPower)
    {S : Type*} [CommRing S] [IsDomain S] (f : S →+* MultiDomain.ordinary D) (hf : Function.Injective f)
    (hbad : ¬ Factorization.IsBFDomain S) (T : Subring (MultiDomain.poleAlgebra D))
    (hT : ∀ y : S, MultiDomain.ProfileChoices.inPole (f y) ∈ T) : HasBoundedLocalWords q c upper G T := by
  let : IsLocalization (localPoles q c upper G) (MultiDomain.poleAlgebra D) := by
    change IsLocalization (Submonoid.closure (Set.range (localRaw q c upper G))) _
    rw [← hraw]
    infer_instance
  obtain ⟨k,_,hk⟩ := C.infinitely_many_bounded_words f hf hbad
  apply hasBoundedLocalWords_of_normalized q c upper G T (MultiDomain.poleAlgebra D).subtype
    Subtype.val_injective (2*k)
  apply hk.mono
  rintro n ⟨w,hw,_,y,hy⟩
  refine ⟨w,hw,MultiDomain.ProfileChoices.inPole (f y),hT y,?_⟩
  rw [← hraw, normalizedWord, ← hE]
  exact hy

include hc in
theorem selected_local_conductor (p : PrimeIndex)
    {B A : Type*} [CommRing B] [Algebra ℚ B] [Algebra (Poly r) B] [IsScalarTower ℚ (Poly r) B]
    [IsLocalization (localPoles q c upper G) B] [CommRing A] [Algebra ℚ_[p.val] A]
    [Algebra (MvPolynomial (Fin (r+1)) ℚ_[p.val]) A] [IsScalarTower ℚ_[p.val] (MvPolynomial (Fin (r+1)) ℚ_[p.val]) A]
    [IsLocalization ((localPoles q c upper G).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) A]
    [IsNoetherianRing A] (T : Subring B) (hw : HasBoundedLocalWords q c upper G T)
    (hclear : ∀ x : B, ∃ n : ℕ, 0 < n ∧ (n : B)*x ∈ T)
    (ev : ∀ i : (localFibre q c upper G p).Component (withPoint upper q p),
      A →ₐ[ℚ_[p.val]] (localFibre q c upper G p).guard.Field i)
    (hev : ∀ i (P : MvPolynomial (Fin (r+1)) ℚ_[p.val]), ev i (algebraMap _ A P) =
      aeval ((localFibre q c upper G p).guard.points ((localFibre q c upper G p).sidePoints c (withPoint upper q p)) i) P)
    (hval : ∀ i (t : T), ‖ev i (baseElement (K := ℚ_[p.val]) (localPoles q c upper G) A (t : B))‖ ≤ 1) :
    conductorIdeal (image p.val B A (tensorEquiv (K := ℚ_[p.val]) (localPoles q c upper G) B A) T) =
      ⨅ i, RingHom.ker (ev i) := by
  classical
  let L := actualPrescription q c upper
  let D := localPoles q c upper G
  let e := tensorEquiv (K := ℚ_[p.val]) D B A
  let U := image p.val B A e T
  let f := localFibre q c upper G p
  let extra := withPoint upper q p
  let hist := localHistory q c upper G
  let W (n : ℕ) := triangularWords n (hist n)
  obtain ⟨b,hb⟩ := hw
  obtain ⟨a,_,j,hj,hs⟩ := exists_fixed_word_exponent (W := fun n ↦ ↥(W n)) (fun _ w ↦ w.val.1)
    (fun n w ↦ ∃ x ∈ T, algebraMap (Poly r) B ((localRaw q c upper G n)^w.val.1) = algebraMap _ B w.val.2 * x)
    b (firstAppearance L G p + 1) hb
  choose words heq x hx hrel using fun n ↦ (hs n).2
  let F (n : ℕ) := MvPolynomial.map (algebraMap ℚ ℚ_[p.val]) (localRaw q c upper G (j n))
  let H (n : ℕ) := Fibre.localDen (p := p) (hist (j n)) (words n)
  let X (n : ℕ) : U := ⟨baseElement (K := ℚ_[p.val]) D A (x n), original_mem p.val B A e T ⟨x n,hx n⟩⟩
  have hlisted n : ∃ N : ℕ, f.Tests c extra (hist (j n)) N (F n) := by
    have hmem := eventual_processed L G p (n := j n) ((hs n).1)
    have hb := actual_batch L G (j n)
    have hmem' : p ∈ (allocate q (j n) (hist (j n))).processed := by
      rw [hb] at hmem
      exact hmem
    exact selected_tests q c upper G hc (j n) ⟨p,hmem'⟩
  choose N hn using hlisted
  apply conductor_of_scheduled_local_words (D.map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) e T hclear _ ev hev (f.guard.points_generate _)
    (f.points_injective c extra) hval (f.generators c extra) j hj F H N a X
  · intro n
    have h := MultivariateWordRecovery.word_relation (K := ℚ_[p.val]) D A (localRaw q c upper G (j n))
      (words n).val.2 (words n).val.1 (x n) (by simpa only [map_pow] using hrel n)
    change algebraMap _ A (F n ^ a) = algebraMap _ A (H n) * baseElement (K := ℚ_[p.val]) D A (x n)
    rw [mul_comm]
    simpa only [F, H, Fibre.localDen, heq] using h
  · intro i n
    have hclean := clean_actual L G c hc (j n)
    have hj' (t : Fin (j n)) : f.componentEval c extra i ((hist (j n) t).raw t.val) ≠ 0 :=
      f.componentEval_ne_zero c extra i _ (fun he ↦ hclean t (he ▸ map_zero _)) (hclean t)
    change eval₂Hom _ _ (MvPolynomial.map _ _) ≠ 0
    rw [eval₂Hom_map_hom, ← IsScalarTower.algebraMap_eq ℚ ℚ_[p.val] (f.guard.Field i)]
    exact triangular_denominator_ne_zero _ _ hj' _ (words n).property
  · intro n s hs
    simpa only [heq] using (hn n).denominator s hs (words n)
  · intro n s hs m
    exact (hn n).coefficients s hs m
  · intro i n
    obtain ⟨α, _, hi, hd⟩ := (hn n).gradients i (words n)
    refine ⟨α,hi,?_⟩
    simpa only [heq, map_natCast] using hd

/-- At each arithmetic prime the conductor is the full kernel of the canonical product
of localized closed-point evaluations of the selected sequence. -/
theorem selected_point_conductor (p : PrimeIndex)
    {B A : Type*} [CommRing B] [Algebra ℚ B] [Algebra (Poly r) B] [IsScalarTower ℚ (Poly r) B]
    [IsLocalization (localPoles q c upper G) B] [CommRing A] [Algebra ℚ_[p.val] A]
    [Algebra (MvPolynomial (Fin (r+1)) ℚ_[p.val]) A] [IsScalarTower ℚ_[p.val] (MvPolynomial (Fin (r+1)) ℚ_[p.val]) A]
    [IsLocalization ((localPoles q c upper G).map (MvPolynomial.map (algebraMap ℚ ℚ_[p.val]))) A]
    [IsNoetherianRing A] (T : Subring B) (hw : HasBoundedLocalWords q c upper G T)
    (hclear : ∀ x : B, ∃ n : ℕ, 0 < n ∧ (n : B)*x ∈ T)
    (hval : ∀ i (t : T), ‖selectedPointEval q c upper G hc p A i
      (baseElement (K := ℚ_[p.val]) (localPoles q c upper G) A (t : B))‖ ≤ 1) :
    conductorIdeal (image p.val B A (tensorEquiv (K := ℚ_[p.val]) (localPoles q c upper G) B A) T) =
      RingHom.ker (AlgHom.pi (selectedPointEval q c upper G hc p A)) := by
  rw [selected_local_conductor q c upper G hc p T hw hclear (selectedPointEval q c upper G hc p A)
    (fun i P ↦ closedPointEval_polynomial _ A _ _ P) hval]
  ext x
  change (x ∈ ⨅ i, RingHom.ker (selectedPointEval q c upper G hc p A i)) ↔
    (AlgHom.pi (selectedPointEval q c upper G hc p A)) x = 0
  rw [Ideal.mem_iInf, funext_iff]
  rfl

end UnconditionalCounterexample.MultivariateSelection
