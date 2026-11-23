import UnconditionalCounterexample.Variations.PrivateGuardsGeneric
import UnconditionalCounterexample.Variations.PrivateGuardsMainRule
import UnconditionalCounterexample.Variations.PrivateGuardsRealized

/-! # Generic recovery along the joint main and private-guard recursion

Add the geometric tests and the word-denominator degree bound to a live
prescription. They depend only on the completed rounds and can accompany
every local arithmetic condition in the original prescription.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial MultivariateInfinity MultivariateListedWords MultivariateSelection
open PrivateGuardsRecovery

variable {r n d : ℕ} {M : ℕ → Type} {K : Type} [Field K] [CharZero K]

private def expanded (h : History r M n) : ℕ → Entry r Unit := fun i =>
  if hi : i < n then ⟨(h ⟨i,hi⟩).entry.degree,(h ⟨i,hi⟩).entry.lower,(h ⟨i,hi⟩).entry.lower_lt,()⟩
  else ⟨2,0,by simp,()⟩

private def oldMain (h : History r M n) (i : ℕ) := (expanded h i).raw i
private def oldPuncture (h : History r M n) (i : ℕ) := if hi : i<n then (h ⟨i,hi⟩).puncture else 1

private theorem vspan (s : Finset ℕ) (hs : s.card = Fintype.card (Fin (r+1))) (j : Fin (r+1)) :
    ∃ b : ℕ → ℚ, X j = ∑ i ∈ s, C (b i) * vandermondeForm (r+1) i :=
  vandermondeForm_spans (r+1) s (by simpa using hs) j

private def words (F G : ℕ → Poly r) (n : ℕ) : Finset (ℕ × Poly r) := by
  classical exact Finset.univ.image (fun w : BoundedWord n => (w.latestExponent,mixedDenominator F G w))

private def representatives (r : ℕ) (K : Type) [Field K] [CharZero K] :
    ℕ → PrivateGuardsRecovery.Config (Fin (r+1)) K := (exists_configurations (k := ℚ)).choose

private theorem finCross [IsAlgClosed K] (h : History r M n) :
    (MultivariateSchedule.crossings (fun i => extend (K := K) (oldMain h i))
      (Fintype.card (Fin (r+1))) n).Finite :=
  finite_geometric_crossings _ _ (fun i => (expanded h i).degree) (vandermonde_degree r)
    (fun i => ⟨_,(expanded h i).lower_lt,rfl⟩) vspan n

/-- Degree needed to clear the whole finite list of mixed words. -/
def genericDegreeFloor (h : History r M n) := (words (oldMain h) (oldPuncture h) n).sup
  (fun w => w.2.totalDegree)

/-- Finite geometric tests on the main prefix of a live history. -/
def genericTests (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (h : History r M n) :=
  mainTests (representatives r K) (oldMain h) (words (oldMain h) (oldPuncture h)) n (finCross h)

theorem genericTests_valid [IsAlgClosed K] (h : History r M n) :
    ∀ t ∈ genericTests K h, t.Valid := mainTests_valid _ _ _ _ _

/-- Strengthen the current prescription and leave its arithmetic data and chosen memory intact. -/
def genericPrescription [IsAlgClosed K] {h : History r M n} (P : Prescription K h) : Prescription K h where
  memory := P.memory
  reg := P.reg
  blocked := P.blocked
  separate := P.separate
  floor := max P.floor (genericDegreeFloor h)
  regular d hd := P.regular d ((le_max_left ..).trans_lt hd)
  pairs := P.pairs
  geometry := by
    classical
    exact P.geometry ∪ genericTests K h
  valid t ht := by
    classical
    exact (Finset.mem_union.mp ht).elim (P.valid t) (mainTests_valid _ _ _ _ _ t)

variable [IsAlgClosed K] (c : Fin (r+1) → ℚ) (P : ∀ n (h : History r M n), Prescription K h)

def genericRule : Rule r M c := ruleOf c (fun n h => genericPrescription (P n h))

theorem genericRule_accepts_original {n : ℕ} (h : History r M n) {x : MainChoice r n (M n)}
    (hx : (genericRule c P).Accepts n h x) : (P n h).Satisfied x := by
  classical
  obtain ⟨hfloor,hm,hd,hp,hr,hg,hs⟩ := hx
  exact ⟨(le_max_left ..).trans_lt hfloor,hm,hd,hp,
    fun v => by obtain ⟨he,hr⟩ := hr v; exact ⟨(le_max_left ..).trans_lt he,hr⟩,
    fun t ht => hg t (Finset.mem_union_left _ ht),hs⟩

private theorem mixedDenominator_congr (F G F' G' : ℕ → Poly r) {n : ℕ} (w : BoundedWord n)
    (hf : ∀ i<n, F i = F' i) (hg : ∀ i<n, G i = G' i) :
    mixedDenominator F G w = mixedDenominator F' G' w := by
  unfold mixedDenominator denominator
  apply Finset.prod_congr rfl
  intro j hj
  have hi := Finset.mem_range.mp hj
  have he : interleave F G j = interleave F' G' j := by
    unfold interleave; split <;> first | exact hf _ (by omega) | exact hg _ (by omega)
  rw [he]

/-- Interface for any rule whose accepted entries meet the finite geometric
tests and the actual denominator degree bound. -/
def MeetsGenericTests (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (L : Rule r M c) : Prop :=
  ∀ n (h : History r M n) (x : MainChoice r n (M n)), L.Accepts n h x →
    genericDegreeFloor h < x.entry.degree ∧ ∀ t ∈ genericTests K h, t.Holds (extend (x.entry.raw n))

theorem genericRule_meets : MeetsGenericTests c K (genericRule c P) := by
  classical
  intro n h x hx
  exact ⟨(le_max_right ..).trans_lt hx.1, fun t ht => hx.2.2.2.2.2.1 t (Finset.mem_union_right _ ht)⟩

variable (C : Config r d) (L : Rule r M c) (geometry : MeetsGenericTests c K L)
local notation "F" => main C L
local notation "G" => puncture C L

private theorem word_list_eq (n : ℕ) :
    words (oldMain (before C L n)) (oldPuncture (before C L n)) n = words F G n := by
  classical
  apply Finset.image_congr
  intro w _
  exact Prod.ext rfl (mixedDenominator_congr _ _ _ _ w
    (fun i hi => by simp [oldMain,expanded,hi,before,main,Entry.raw])
    (fun i hi => by simp [oldPuncture,hi,before,puncture]))

include geometry in
private theorem stages (n : ℕ) :
    ∀ t ∈ mainTests (representatives r K) F (words F G) n
      (finite_geometric_crossings _ _ (fun i => (event C L i).entry.degree) (vandermonde_degree r)
        (fun i => ⟨_,(event C L i).entry.lower_lt,rfl⟩) vspan n), t.Holds (extend (F n)) := by
  classical
  intro t ht
  apply (geometry n _ _ (accepted C L n).main_ok).2 t
  unfold genericTests
  rw [mainTests_congr (representatives r K) (oldMain (before C L n)) F _ (words F G) n (fun i hi => by simp [oldMain,expanded,hi,before,main,Entry.raw])
    (word_list_eq c C L n) (finCross _) _]
  exact ht

include geometry in
/-- On this actual joint recursive history an unbounded subsequence of
normalized main words recovers its enlarged localization, including all
of its chosen private punctures. -/
theorem recover_of_actual_words [Uncountable K] (B : Type) [CommRing B] [IsDomain B] [Algebra ℚ B]
    [Algebra (Poly r) B] [IsScalarTower ℚ (Poly r) B] [IsLocalization (inverted (Set.range F) G) B]
    (T : Type) [Field T] (φ : B →+* T) (hφ : Function.Injective φ) (A : Subalgebra ℚ B)
    (hwords : {n | ∃ (w : BoundedWord n) (x : A),
      let W := normalizedMain (φ.comp (algebraMap (Poly r) B) ∘ F)
        (φ.comp (algebraMap (Poly r) B) ∘ G) mixedPower
      φ (x : B) = W n ^ w.latestExponent * (∏ j ∈ Finset.range n, W j ^ w.oldExponent j)}.Infinite) :
    A = ⊤ := by
  classical
  let D := interleave F G
  have hm : Submonoid.closure (Set.range D) = inverted (Set.range F) G := by
    apply congrArg Submonoid.closure
    ext t
    constructor
    · rintro ⟨i,rfl⟩
      unfold D interleave; split <;> first | exact Or.inl ⟨_,rfl⟩ | exact Or.inr ⟨_,rfl⟩
    · rintro (⟨i,rfl⟩ | ⟨i,rfl⟩)
      · exact ⟨2*i,interleave_even ..⟩
      · exact ⟨2*i+1,interleave_odd ..⟩
  let : IsLocalization (Submonoid.closure (Set.range D)) B := hm ▸ inferInstance
  let S := Submonoid.closure (Set.range D)
  have hr : S ≤ nonZeroDivisors (Poly r) := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i,rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    unfold D interleave; split
    · exact (event C L _).irreducible.ne_zero
    · exact (event C L _).irreducible_puncture.ne_zero
  let f := φ.comp (algebraMap (Poly r) B)
  have hinj : Function.Injective f := hφ.comp (IsLocalization.injective B hr)
  have hF (n : ℕ) : f (F n) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (event C L n).irreducible.ne_zero
  have hG (n : ℕ) : f (G n) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (event C L n).irreducible_puncture.ne_zero
  let E := Localization (S.map (MvPolynomial.map (algebraMap ℚ K)))
  apply recover_of_mainTests (K := K) D F (vandermondeForm (r+1)) _
    (words F G) (representatives r K) (exists_configurations (k := ℚ)).choose_spec B E A
    (vandermonde_degree r) (fun i => ⟨_,(event C L i).entry.lower_lt,rfl⟩) vspan (stages c C L geometry)
  intro j
  apply Set.infinite_of_forall_exists_gt
  intro b
  obtain ⟨n,⟨w,x,hx⟩,hgt⟩ := hwords.exists_gt (max b j)
  let H := mixedDenominator F G w
  have hH : H ∈ S := denominator_mem_closure D (liftedWord w)
  have hw : (w.latestExponent,H) ∈ words F G n := Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩
  have hd : H.totalDegree < (event C L n).entry.degree := by
    apply lt_of_le_of_lt _ (geometry n _ _ (accepted C L n).main_ok).1
    unfold genericDegreeFloor
    rw [word_list_eq]
    exact Finset.le_sup (f := fun y : ℕ × Poly r => y.2.totalDegree) hw
  have hzero : f H ≠ 0 := (map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp (hr hH))
  have he := ((eq_div_iff hzero).mp (hx.trans (normalized_main_word_fraction f F G hF hG w))).symm
  exact ⟨n,⟨_,H,x,hw,hH,hd.trans_le (Nat.le_mul_of_pos_left _ w.latestExponent_bounds.1),
    dvd_denominator D (liftedWord w) (by omega),hφ (by simpa [f,mul_comm] using he)⟩,
    (le_max_left ..).trans_lt hgt⟩

include geometry in
/-- Specialization to the horizontal subalgebra of the chosen main and auxiliary
polynomials inside the rational function field. -/
theorem recover_pole_of_meets [Uncountable K]
    (A : Subalgebra ℚ ((family C L).poleAlgebra (fun n => (event C L n).irreducible)))
    (hwords : {n | ∃ (w : BoundedWord n) (x : A),
      let W := (family C L).generator mixedPower
      (((x : (family C L).poleAlgebra _) : FractionRing (Poly r))) =
        W n ^ w.latestExponent * (∏ j ∈ Finset.range n, W j ^ w.oldExponent j)}.Infinite) : A = ⊤ := by
  let B := (family C L).poleAlgebra (fun n => (event C L n).irreducible)
  let : IsLocalization (inverted (Set.range F) G) B := inferInstanceAs
    (IsLocalization (inverted (Set.range F) (family C L).puncture) ((family C L).poleAlgebra _))
  exact recover_of_actual_words c C L geometry B _ B.subtype Subtype.val_injective A hwords

/-- The strengthened prescription gives the recovery theorem for its literal pole algebra. -/
theorem recover_actual_pole [Uncountable K]
    (A : Subalgebra ℚ ((family C (genericRule c P)).poleAlgebra
      (fun n => (event C (genericRule c P) n).irreducible)))
    (hwords : {n | ∃ (w : BoundedWord n) (x : A),
      let W := (family C (genericRule c P)).generator mixedPower
      (((x : (family C (genericRule c P)).poleAlgebra _) : FractionRing (Poly r))) =
        W n ^ w.latestExponent * (∏ j ∈ Finset.range n, W j ^ w.oldExponent j)}.Infinite) : A = ⊤ :=
  recover_pole_of_meets c C (genericRule c P) (genericRule_meets c P) A hwords

end UnconditionalCounterexample.Variations.PrivateGuards.Live
