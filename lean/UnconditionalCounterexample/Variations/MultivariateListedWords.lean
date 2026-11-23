import UnconditionalCounterexample.Variations.MultivariateSchedule
import UnconditionalCounterexample.Variations.MultivariateWordRecovery

/-!
# Recovery from the finite tests of a multivariate schedule

A subalgebra containing a subsequence of listed words equals the original
localization. The stage tests cover all words in each finite list, so a
different subalgebra can choose its witnesses at different stages.
-/

noncomputable section

namespace UnconditionalCounterexample.MultivariateListedWords

open MvPolynomial MultivariateFibres MultivariateSchedule MultivariateReservations
open MultivariateRecovery MultivariateWordRecovery MultivariateStage

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [Fintype σ]

/-- Coefficientwise extension to the geometric test field. -/
abbrev extend (p : MvPolynomial σ k) : MvPolynomial σ K := MvPolynomial.map (algebraMap k K) p

omit [IsAlgClosed K] in
/-- General position over the base field makes the earlier geometric crossings finite. -/
theorem finite_geometric_crossings (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (htop : ∀ i, ∃ p : MvPolynomial σ k, p.totalDegree < d i ∧ F i = l i ^ d i + p)
    (hlin : ∀ s : Finset ℕ, s.card = Fintype.card σ → ∀ j : σ,
      ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i) (n : ℕ) :
    (crossings (fun i => extend (K := K) (F i)) (Fintype.card σ) n).Finite := by
  have hdeg (p : MvPolynomial σ k) : (extend (K := K) p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (f := fun e => e.sum fun (_ : σ) (n : ℕ) => n) (support_map_subset (algebraMap k K) p)
  apply finite_crossings _ (fun i => extend (K := K) (l i)) d
  · intro i _; exact (hdeg _).trans (hl i)
  · intro i _
    obtain ⟨p, hp, hF⟩ := htop i
    exact ⟨extend p, (hdeg _).trans_lt hp, by simp [hF,extend]⟩
  · intro s _ hc j
    obtain ⟨c, hc⟩ := hlin s hc j
    refine ⟨fun i => algebraMap k K (c i), ?_⟩
    simpa only [map_X, map_sum, map_mul, map_C] using congrArg (MvPolynomial.map (algebraMap k K)) hc

/-- The actual finite list required of a raw-polynomial stage. -/
def stageTests
    (point : ℕ → σ → K) (P : ℕ → Ideal (MvPolynomial σ K)) (fixed : Finset (σ → K))
    (F : ℕ → MvPolynomial σ k) (W : ℕ → Finset (ℕ × MvPolynomial σ k))
    (n : ℕ) (hf : (crossings (fun i => extend (K := K) (F i)) (Fintype.card σ) n).Finite) :
    Finset (Test K σ) := by
  classical
  exact tests point n
    (protection P (fun i => extend (K := K) (F i)) (Fintype.card σ) n fixed hf)
    ((W n).image (fun w => (w.1,extend (K := K) w.2)))

theorem stageTests_valid
    (point : ℕ → σ → K) (P : ℕ → Ideal (MvPolynomial σ K)) (fixed : Finset (σ → K))
    (F : ℕ → MvPolynomial σ k) (W : ℕ → Finset (ℕ × MvPolynomial σ k))
    (n : ℕ) (hf : (crossings (fun i => extend (K := K) (F i)) (Fintype.card σ) n).Finite)
    {t : Test K σ} (ht : t ∈ stageTests point P fixed F W n hf) : t.Valid := by
  classical
  exact tests_valid _ _ _ _ ht

omit [IsAlgClosed K] [Fintype σ] in
private theorem earlier_eq (F G : ℕ → MvPolynomial σ K) (n : ℕ) (hFG : ∀ i < n, F i = G i) :
    earlier F n = earlier G n := by
  classical
  exact Finset.image_congr fun i hi => hFG i (Finset.mem_range.mp hi)

private theorem reserved_eq (P : ℕ → Ideal (MvPolynomial σ K)) (F G : ℕ → MvPolynomial σ K)
    (n : ℕ) (hFG : ∀ i < n, F i = G i) : reserved P F n = reserved P G n := by
  classical
  ext u
  simp only [reserved, Finset.mem_biUnion, Finset.mem_range]
  apply exists_congr; intro j
  exact and_congr_right (fun hj => by rw [earlier_eq F G j (fun i hi => hFG i (by omega))])

omit [IsAlgClosed K] [Fintype σ] in
private theorem crossings_eq (F G : ℕ → MvPolynomial σ K) (r n : ℕ) (hFG : ∀ i < n, F i = G i) :
    crossings F r n = crossings G r n := by
  unfold crossings
  apply Set.iUnion_congr
  intro s
  apply Set.iUnion_congr
  intro hs
  ext u
  exact forall₂_congr (fun i hi => by rw [hFG i (Finset.mem_range.mp ((Finset.mem_powersetCard.mp hs).1 hi))])

/-- A candidate successor can compute the tests before choosing its polynomial.
They depend only on the proper prefix and the current finite list of words. -/
theorem stageTests_congr
    (point : ℕ → σ → K) (P : ℕ → Ideal (MvPolynomial σ K)) (fixed : Finset (σ → K))
    (F G : ℕ → MvPolynomial σ k) (W V : ℕ → Finset (ℕ × MvPolynomial σ k)) (n : ℕ)
    (hFG : ∀ i < n, F i = G i) (hWV : W n = V n)
    (hf : (crossings (fun i => extend (K := K) (F i)) (Fintype.card σ) n).Finite)
    (hg : (crossings (fun i => extend (K := K) (G i)) (Fintype.card σ) n).Finite) :
    stageTests point P fixed F W n hf = stageTests point P fixed G V n hg := by
  classical
  let F' (i : ℕ) := extend (K := K) (F i)
  let G' (i : ℕ) := extend (K := K) (G i)
  have he (i : ℕ) (hi : i<n) : F' i = G' i := congrArg (extend (K := K)) (hFG i hi)
  have hset : hf.toFinset = hg.toFinset := by
    ext u; simpa only [Set.Finite.mem_toFinset] using Set.ext_iff.mp (crossings_eq F' G' _ n he) u
  simp only [stageTests, protection, hWV, hset]
  rw [reserved_eq P _ _ n he]

set_option maxHeartbeats 800000 in
/-- Join the finite stage tests to the original localization. The word
witnesses, their denominators and their exponents are those of the supplied
subalgebra. All geometric conditions of RECOVER follow from the checked
finite lists. -/
theorem recover_of_stageTests
    (F l : ℕ → MvPolynomial σ k) (d : ℕ → ℕ) (W : ℕ → Finset (ℕ × MvPolynomial σ k))
    (point : ℕ → σ → K) (hp : Function.Surjective point)
    (P : ℕ → Ideal (MvPolynomial σ K)) (hP : Function.Surjective P) (fixed : Finset (σ → K))
    (B : Type*) [CommRing B] [IsDomain B] [Algebra k B] [Algebra (MvPolynomial σ k) B]
    [IsScalarTower k (MvPolynomial σ k) B] [IsLocalization (Submonoid.closure (Set.range F)) B]
    (E : Type*) [CommRing E] [Algebra K E] [Algebra (MvPolynomial σ K) E]
    [IsScalarTower K (MvPolynomial σ K) E]
    [IsLocalization ((Submonoid.closure (Set.range F)).map (MvPolynomial.map (algebraMap k K))) E]
    (A : Subalgebra k B)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (htop : ∀ i, ∃ q : MvPolynomial σ k, q.totalDegree < d i ∧ F i = l i ^ d i + q)
    (hlin : ∀ s : Finset ℕ, s.card = Fintype.card σ → ∀ j : σ,
      ∃ c : ℕ → k, X j = ∑ i ∈ s, C (c i) * l i)
    (hstage : ∀ n t, t ∈ stageTests point P fixed F W n
      (finite_geometric_crossings F l d hl htop hlin n) → t.Holds (extend (F n)))
    (hword : ∀ j, {i | ∃ (a : ℕ) (H : MvPolynomial σ k) (w : A),
      (a,H) ∈ W i ∧ H ∈ Submonoid.closure (Set.range F) ∧ H.totalDegree < a * d i ∧ F j ∣ H ∧
      algebraMap (MvPolynomial σ k) B (F i) ^ a = algebraMap (MvPolynomial σ k) B H * w}.Infinite) :
    A = ⊤ := by
  classical
  let M := Submonoid.closure (Set.range F)
  let N := M.map (MvPolynomial.map (algebraMap k K))
  let G (i : ℕ) := extend (K := K) (F i)
  let list (i : ℕ) := (W i).image (fun w => (w.1,extend (K := K) w.2))
  let hf := finite_geometric_crossings (K := K) F l d hl htop hlin
  let Q (i : ℕ) := protection P G (Fintype.card σ) i fixed (hf i)
  have hN : N = Submonoid.closure (Set.range G) := by
    rw [show N = _ from MonoidHom.map_mclosure (MvPolynomial.map (algebraMap k K)) (Set.range F),
      ← Set.range_comp]; rfl
  obtain ⟨_,hgeom,hpoints⟩ := conclusions_of_protection P hP G (Fintype.card σ) fixed hf point list hstage
  have late (u v : σ → K) : ∃ (i a : ℕ) (H : MvPolynomial σ k) (w : A), (a,extend (K := K) H) ∈ list i ∧
      0 < a ∧ H ∈ M ∧
      algebraMap (MvPolynomial σ k) B (F i) ^ a = algebraMap (MvPolynomial σ k) B H * w ∧
      ((Test.pair u v a (extend H)).Valid → (Test.pair u v a (extend H)).Holds (G i)) ∧
      ((Test.tangent u v a (extend H)).Valid → (Test.tangent u v a (extend H)).Holds (G i)) := by
    obtain ⟨n,hn⟩ := eventually_mem_tests point hp u v
    obtain ⟨i,⟨a,H,w,hw,hH,hd,_,hrel⟩,hi⟩ := (hword 0).exists_gt n
    have hmem : (a,extend (K := K) H) ∈ list i := Finset.mem_image.mpr ⟨(a,H),hw,rfl⟩
    have ha : a ≠ 0 := by rintro rfl; simp at hd
    have hh := hn i hi.le (Q i) (list i) _ hmem
    exact ⟨i,a,H,w,hmem,Nat.pos_of_ne_zero ha,hH,hrel,
      fun h => hstage i _ (hh.1 h), fun h => hstage i _ (hh.2 h)⟩
  apply recover (K := K) F l d B E A hl htop hlin
  · intro s hc u
    simpa only [G, extend, eval_map, aeval_def] using hgeom s (by simpa using hc) u
  · intro j; apply (hword j).mono
    rintro i ⟨a,H,w,_,_,hr⟩; exact ⟨a,H,w,hr⟩
  · dsimp only
    intro I hI _ hdisj
    change Disjoint (N : Set (MvPolynomial σ K)) _ at hdisj
    change ∃ u, Retained N u ∧ I ≤ pointIdeal u
    rw [hN] at hdisj ⊢
    exact hpoints I hI hdisj
  · dsimp only
    intro u v hu hv hne
    obtain ⟨i,a,H,w,_,ha,hH,hrel,hpair,_⟩ := late u v
    have hm : extend (K := K) H ∈ N := ⟨H,hH,rfl⟩
    exact ⟨w, separates (K := K) (p := F i) (H := H) (a := a) M E (w : B) hrel u v hu hv (hpair ⟨hne,ha,hu ⟨_,hm⟩,hv ⟨_,hm⟩⟩)⟩
  · dsimp only
    intro u hu v hv
    obtain ⟨i,a,H,w,_,ha,hH,hrel,_,htan⟩ := late u v
    have hm : extend (K := K) H ∈ N := ⟨H,hH,rfl⟩
    exact ⟨w, G i ^ a, extend H, word_relation (K := K) M E _ _ _ _ hrel,
      htan ⟨hv,ha,hu ⟨_,hm⟩⟩⟩

end UnconditionalCounterexample.MultivariateListedWords
