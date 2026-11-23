import UnconditionalCounterexample.Variations.PrivateGuardsGeometricPoints
import UnconditionalCounterexample.Variations.PrivateGuardsConfigurations

/-! # Finite main-stage tests recover the punctured generic fibre

Test one representative of each joint rational evaluation kernel. The same
finite lists therefore control all retained geometric points and directions
over an uncountable algebraically closed field, even when the punctures
remove all points with coordinates algebraic over the rationals.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuardsRecovery

open MvPolynomial MultivariateFibres MultivariateStage MultivariateListedWords
open MultivariateSchedule MultivariateWordRecovery

variable {k K σ : Type} [Field k] [Field K] [Algebra k K] [Fintype σ]

/-- A single point enumeration includes both tuples of every representative
configuration; it can feed the same finite test machinery as the main schedule. -/
def configPoint (R : ℕ → Config σ K) (n : ℕ) : σ → K :=
  if n % 2 = 0 then (R (n/2)).1 else (R (n/2)).2

/-- At each main stage take its earlier main crossings, all enumerated
configurations within the prefix, and the actual list of word denominators. -/
def mainTests (R : ℕ → Config σ K) (F : ℕ → MvPolynomial σ k)
    (W : ℕ → Finset (ℕ × MvPolynomial σ k)) (n : ℕ)
    (hfin : (crossings (fun i => extend (K := K) (F i)) (Fintype.card σ) n).Finite) : Finset (Test K σ) := by
  classical
  exact tests (configPoint R) n hfin.toFinset ((W n).image fun w => (w.1,extend (K := K) w.2))

theorem mainTests_valid (R : ℕ → Config σ K) (F : ℕ → MvPolynomial σ k)
    (W : ℕ → Finset (ℕ × MvPolynomial σ k)) (n : ℕ)
    (hfin : (crossings (fun i => extend (K := K) (F i)) (Fintype.card σ) n).Finite) :
    ∀ t ∈ mainTests R F W n hfin, t.Valid := fun _ ht => tests_valid _ _ _ _ ht

/-- Computing the test set requires only the main prefix and the current list. -/
theorem mainTests_congr (R : ℕ → Config σ K) (F G : ℕ → MvPolynomial σ k)
    (W V : ℕ → Finset (ℕ × MvPolynomial σ k)) (n : ℕ) (he : ∀ i < n, F i = G i) (hw : W n = V n)
    (hf : (crossings (fun i => extend (K := K) (F i)) (Fintype.card σ) n).Finite)
    (hg : (crossings (fun i => extend (K := K) (G i)) (Fintype.card σ) n).Finite) :
    mainTests R F W n hf = mainTests R G V n hg := by
  have hc : crossings (fun i => extend (K := K) (F i)) (Fintype.card σ) n =
      crossings (fun i => extend (K := K) (G i)) (Fintype.card σ) n := by
    unfold crossings
    apply Set.iUnion_congr; intro s
    apply Set.iUnion_congr; intro hs
    ext u
    exact forall₂_congr fun i hi => by
      dsimp only
      rw [he i (Finset.mem_range.mp ((Finset.mem_powersetCard.mp hs).1 hi))]
  have hp : hf.toFinset = hg.toFinset := by
    ext u; simpa only [Set.Finite.mem_toFinset] using Set.ext_iff.mp hc u
  simp only [mainTests, hp, hw]

private theorem rep_mem (R : ℕ → Config σ K) {j n : ℕ} (hn : 2*j+1 ≤ n)
    (P : Finset (σ → K)) (W : Finset (ℕ × MvPolynomial σ K))
    (w : ℕ × MvPolynomial σ K) (hw : w ∈ W) :
    ((Test.pair (R j).1 (R j).2 w.1 w.2).Valid →
      Test.pair (R j).1 (R j).2 w.1 w.2 ∈ tests (configPoint R) n P W) ∧
    ((Test.tangent (R j).1 (R j).2 w.1 w.2).Valid →
      Test.tangent (R j).1 (R j).2 w.1 w.2 ∈ tests (configPoint R) n P W) := by
  classical
  let S := (Finset.range (n+1)).image (configPoint R)
  have hmem : (((R j).1,(R j).2),w) ∈ (S ×ˢ S) ×ˢ W := by
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hw⟩
    · exact Finset.mem_image.mpr ⟨2*j,Finset.mem_range.mpr (by omega),by simp [configPoint]⟩
    · exact Finset.mem_image.mpr ⟨2*j+1,Finset.mem_range.mpr (by omega),by simp [configPoint,show (2*j+1)/2 = j by omega]⟩
  exact ⟨fun hv => Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨_,hmem,rfl⟩)),hv⟩, fun hv => Finset.mem_filter.mpr ⟨Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨_,hmem,rfl⟩),hv⟩⟩

set_option maxHeartbeats 700000 in
/-- The enlarged localization is recovered from the actual words and finite
geometric tests. Auxiliary factors need no leading-form or crossing tests,
and future factors need not preserve earlier point reservations. -/
theorem recover_of_mainTests [Countable k] [IsAlgClosed K] [Uncountable K]
    (D F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ) (W : ℕ → Finset (ℕ × MvPolynomial σ k))
    (R : ℕ → Config σ K) (hR : ∀ x, ∃ n, SameTests (k := k) (R n) x)
    (B : Type) [CommRing B] [IsDomain B] [Algebra k B] [Algebra (MvPolynomial σ k) B]
    [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization (Submonoid.closure (Set.range D)) B]
    (E : Type) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E]
    [IsLocalization ((Submonoid.closure (Set.range D)).map (MvPolynomial.map (algebraMap k K))) E]
    (A : Subalgebra k B)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (htop : ∀ i, ∃ q : MvPolynomial σ k, q.totalDegree < d i ∧ F i = l i ^ d i + q)
    (hlin : ∀ s : Finset ℕ, s.card = Fintype.card σ → ∀ j : σ,
      ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i)
    (hstage : ∀ n t, t ∈ mainTests R F W n (finite_geometric_crossings F l d hl htop hlin n) →
      t.Holds (extend (F n)))
    (hword : ∀ j, {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A),
      (a,H) ∈ W i ∧ H ∈ Submonoid.closure (Set.range D) ∧ H.totalDegree < a * d i ∧ D j ∣ H ∧
      algebraMap (MvPolynomial σ k) B (F i) ^ a = algebraMap (MvPolynomial σ k) B H * w}.Infinite) :
    A = ⊤ := by
  classical
  let M := Submonoid.closure (Set.range D)
  let N := M.map (MvPolynomial.map (algebraMap k K))
  let G (i : ℕ) := extend (K := K) (F i)
  let list (i : ℕ) := (W i).image (fun w => (w.1,extend (K := K) w.2))
  let hf := finite_geometric_crossings (K := K) F l d hl htop hlin
  have late (u v : σ → K) : ∃ (i a : ℕ) (H : MvPolynomial σ k) (w : A), 0 < a ∧ H ∈ M ∧
      algebraMap (MvPolynomial σ k) B (F i) ^ a = algebraMap (MvPolynomial σ k) B H * w ∧
      ((Test.pair u v a (extend H)).Valid → (Test.pair u v a (extend H)).Holds (G i)) ∧
      ((Test.tangent u v a (extend H)).Valid → (Test.tangent u v a (extend H)).Holds (G i)) := by
    obtain ⟨j,hrep⟩ := hR (u,v)
    obtain ⟨i,⟨a,H,w,hw,hH,hd,_,hrel⟩,hi⟩ := (hword 0).exists_gt (2*j+1)
    have hmem : (a,extend (K := K) H) ∈ list i := Finset.mem_image.mpr ⟨(a,H),hw,rfl⟩
    have ha : a ≠ 0 := by rintro rfl; simp at hd
    have hh := rep_mem R hi.le (hf i).toFinset (list i) _ hmem
    exact ⟨i,a,H,w,Nat.pos_of_ne_zero ha,hH,hrel,
      fun h => (hrep.pair_holds _ _ _).mp (hstage i _ (hh.1 ((hrep.pair_valid H a).mpr h))),
      fun h => (hrep.tangent_holds _ _ _).mp (hstage i _ (hh.2 ((hrep.tangent_valid H a).mpr h)))⟩
  apply recover (K := K) D F l d B E A hl htop hlin
  · intro s hs u
    have hc : s.card = Fintype.card σ + 1 := by simpa using hs
    have hh := no_common_zero G (Fintype.card σ) (fun n z hz =>
      hstage n (.point z) (point_mem_tests (configPoint R) n (hf n).toFinset (list n) z
        ((hf n).mem_toFinset.mpr hz))) s hc u
    simpa only [G,extend,eval_map,aeval_def] using hh
  · intro j; apply (hword j).mono
    rintro i ⟨a,H,w,_,_,hr⟩; exact ⟨a,H,w,hr⟩
  · dsimp only
    intro I hI _ hdis
    let : Countable B := (IsLocalization.mk'_surjective (S := B) M).countable
    exact retained_of_countable_rank N E (rank_of_countable_base M B E) I hI hdis
  · dsimp only
    intro u v hu hv hne
    obtain ⟨i,a,H,w,ha,hH,hrel,hpair,_⟩ := late u v
    have hm : extend (K := K) H ∈ N := ⟨H,hH,rfl⟩
    exact ⟨w,separates (K := K) (p := F i) (H := H) (a := a) M E (w : B) hrel u v hu hv
      (hpair ⟨hne,ha,hu ⟨_,hm⟩,hv ⟨_,hm⟩⟩)⟩
  · dsimp only
    intro u hu v hv
    obtain ⟨i,a,H,w,ha,hH,hrel,_,htan⟩ := late u v
    have hm : extend (K := K) H ∈ N := ⟨H,hH,rfl⟩
    exact ⟨w,G i ^ a,extend H,word_relation (K := K) M E _ _ _ _ hrel,
      htan ⟨hv,ha,hu ⟨_,hm⟩⟩⟩

end UnconditionalCounterexample.Variations.PrivateGuardsRecovery
