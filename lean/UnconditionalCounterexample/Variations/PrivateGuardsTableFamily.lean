import UnconditionalCounterexample.Variations.PrivateGuardsRegular
import UnconditionalCounterexample.Variations.PrivateGuardsTableRule
import UnconditionalCounterexample.Variations.PrivateGuardsTableAllocation
import UnconditionalCounterexample.Variations.PrivateGuardsRealized

/-!
# The simultaneous main, public-site and private-site construction

An actual round installs two primaries, a screened guard at each newly
covered prime and an Eisenstein prime. The main polynomial obeys the
entire regular or private-fibre schedule. The round then punctures its
height target and installs a private pair outside all primes just used.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open GuardSupport MvPolynomial MultivariateSelection MultivariateInfinity

variable {r n d : ℕ} {M : ℕ → Type*} {p : PrimeIndex} {K : Type*} [Field K] [CharZero K]

/-- All local assertions at one processed prime. Earlier private primes get
their joint unramified and rational branches, the other primes the regular fibre. -/
structure LocalTests (h : History r M n) (F : Fibre r p) (c : Fin (r+1) → ℚ)
    (N : ℕ) (f : LocalPoly r p) : Prop where
  privately : ∀ (j : Fin n) (e : p = (h j).prime),
    tripleTests (h j).pair (e ▸ F.guard) h N (e ▸ f)
  regularly : (∀ j, (h j).prime ≠ p) → RegularTests h F c N f

private theorem local_selection (h : History r M n) (F : Fibre r p) (c : Fin (r+1) → ℚ)
    (hi : Function.Injective (fun i => (h i).prime.val)) :
    ∃ bound : ℕ, ∀ d ≥ bound, ∀ leading : LocalPoly r p, leading.totalDegree ≤ d →
      ∃ L : OpenLower r d p, ∃ N : ℕ, ∀ f : LocalPoly r p, f.totalDegree < d →
        (fun m => f.coeff m) ∈ L.neighborhood → LocalTests h F c N (leading + f) := by
  classical
  by_cases hp : ∃ j, (h j).prime = p
  · obtain ⟨j,rfl⟩ := hp
    refine ⟨(h j).pair.tripleFloor F.guard n,fun d hd leading hL => ?_⟩
    obtain ⟨L,N,ht⟩ := tripleChoice (h j).pair F.guard h d hd leading hL
    refine ⟨L,N,fun f hf hU => ⟨?_,fun hbad => (hbad j rfl).elim⟩⟩
    intro i he
    have he' : j = i := hi (congrArg Subtype.val he)
    subst i
    exact ht f hf hU
  · refine ⟨F.floor c false n,fun d hd leading hL => ?_⟩
    obtain ⟨L,N,ht⟩ := regularOpen h F c d hd leading hL
    exact ⟨L,N,fun f hf hU => ⟨fun i he => (hp ⟨i,he.symm⟩).elim,fun _ => ht f hf hU⟩⟩

/-- Degree constraints and geometric tests evaluated on the joint history. -/
structure TablePolicy (r : ℕ) (K : Type*) [Field K] where
  floor : ∀ n, History r (Batch r) n → ℕ
  geometry : ∀ n, History r (Batch r) n → Finset (MultivariateStage.Test K (Fin (r+1)))
  valid : ∀ n h t, t ∈ geometry n h → t.Valid

def TablePolicy.empty (r : ℕ) : TablePolicy r ℚ :=
  ⟨fun n _ => n,fun _ _ => ∅,fun _ _ _ he => (Finset.notMem_empty _ he).elim⟩

variable (P : TablePolicy r K) (q : PrimeIndex) (c : Fin (r+1) → ℚ)

private def localFloor (h : History r (Batch r) n) (hi : Function.Injective (fun i => (h i).prime.val))
    (v : (liveBatch q n h).processed) : ℕ :=
  (local_selection h (batchFibre _ v) c hi).choose

def tableDegree (h : History r (Batch r) n) (hi : Function.Injective (fun i => (h i).prime.val)) : ℕ :=
  max 1 (max (P.floor n h) (Finset.univ.sup (localFloor q c h hi))) + 1

private theorem leading_le (p : PrimeIndex) (n d : ℕ) :
    (vandermondeForm (k := ℚ_[p.val]) (r+1) n ^ d).totalDegree ≤ d := by
  apply (totalDegree_pow _ _).trans
  have hl : (vandermondeForm (k := ℚ_[p.val]) (r+1) n).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C,totalDegree_X])
  simpa using Nat.mul_le_mul_left d hl

omit [CharZero K] in
private theorem tableOpen_exists (h : History r (Batch r) n) (hi : Function.Injective (fun i => (h i).prime.val))
    (v : (liveBatch q n h).processed) :
    ∃ L : OpenLower r (tableDegree P q c h hi) v.val, ∃ N : ℕ, ∀ f : LocalPoly r v.val,
      f.totalDegree < tableDegree P q c h hi → (fun m => f.coeff m) ∈ L.neighborhood →
      LocalTests h (batchFibre _ v) c N
        (vandermondeForm (k := ℚ_[v.val.val]) (r+1) n ^ tableDegree P q c h hi + f) := by
  apply (local_selection h (batchFibre _ v) c hi).choose_spec _ _ _ (leading_le ..)
  exact ((Finset.le_sup (f := localFloor q c h hi) (Finset.mem_univ v)).trans
    ((le_max_right _ _).trans (le_max_right _ _))).trans (Nat.le_succ _)

def tablePrescription (h : History r (Batch r) n) (hi : Function.Injective (fun i => (h i).prime.val)) :
    TablePrescription K h where
  memory := liveBatch q n h
  degree := tableDegree P q c h hi
  degree_two := Nat.succ_le_succ (Nat.le_max_left ..)
  primes := (liveBatch q n h).processed
  reserved := ∅
  aux := (liveBatch q n h).aux
  fresh := (liveBatch_valid q n h).aux_fresh
  old_private j := (liveBatch_extra q n h).1 (extra_private h j)
  opens v := (tableOpen_exists P q c h hi v).choose
  private_units j u hu hm b := by
    let v : (liveBatch q n h).processed := ⟨(h j).prime,(liveBatch_extra q n h).1 (extra_private h j)⟩
    let φ := algebraMap ℚ ℚ_[(h j).prime.val]
    let f := MvPolynomial.map φ u
    have hf : f.totalDegree < tableDegree P q c h hi :=
      (Finset.sup_mono (f := fun m => m.sum fun (_ : Fin (r+1)) (t : ℕ) => t)
        (support_map_subset φ u)).trans_lt hu
    have hmem : (fun m => f.coeff m) ∈ (tableOpen_exists P q c h hi v).choose.neighborhood := by
      simpa only [f,φ,coeff_map,eq_ratCast] using hm
    have H := ((tableOpen_exists P q c h hi v).choose_spec.choose_spec f hf hmem).privately j rfl
    have H' := tripleTests_units (h j).pair (batchFibre _ v).guard h H b
    simpa only [← map_vandermonde (algebraMap ℚ ℚ_[(h j).prime.val]),← map_pow, f,φ,← map_add,
      aeval_map_algebraMap] using H'
  geometry := P.geometry n h
  valid := P.valid n h

def tableRule : Rule r (Batch r) c := ruleOfTable c (fun _ h hi => tablePrescription P q c h hi)

variable (C : Config r d)

private theorem actual_satisfied (n : ℕ) :
    ∃ hi, (tablePrescription P q c (before C (tableRule P q c) n) hi).Satisfied
      (event C (tableRule P q c) n).toMainChoice :=
  (accepted C (tableRule P q c) n).main_ok

theorem memory_eq (n : ℕ) :
    (event C (tableRule P q c) n).entry.memory = liveBatch q n (before C (tableRule P q c) n) := by
  obtain ⟨_,h⟩ := actual_satisfied P q c C n
  exact h.2.1

theorem degree_greater (n : ℕ) : P.floor n (before C (tableRule P q c) n) <
    (event C (tableRule P q c) n).entry.degree := by
  obtain ⟨_,h⟩ := actual_satisfied P q c C n
  rw [h.1]
  exact Nat.lt_succ_of_le ((le_max_left ..).trans (le_max_right ..))

theorem geometry_holds (n : ℕ) (t) (ht : t ∈ P.geometry n (before C (tableRule P q c) n)) :
    t.Holds (MvPolynomial.map (algebraMap ℚ K) (main C (tableRule P q c) n)) := by
  obtain ⟨_,h⟩ := actual_satisfied P q c C n
  exact h.2.2.2.2.2.1 t ht

theorem processed_tests (n : ℕ) :
    let h := before C (tableRule P q c) n
    ∀ v : (liveBatch q n h).processed, ∃ N,
      LocalTests h (batchFibre _ v) c N (MvPolynomial.map (algebraMap ℚ ℚ_[v.val.val]) (main C (tableRule P q c) n)) := by
  intro h v
  obtain ⟨hi,H⟩ := actual_satisfied P q c C n
  let raw := (event C (tableRule P q c) n).entry
  let φ := algebraMap ℚ ℚ_[v.val.val]
  let f := MvPolynomial.map φ raw.lower
  have hd : raw.degree = tableDegree P q c h hi := H.1
  have hlt : f.totalDegree < tableDegree P q c h hi := (Finset.sup_mono
    (f := fun m => m.sum fun (_ : Fin (r+1)) (t : ℕ) => t)
    (support_map_subset φ raw.lower)).trans_lt (raw.lower_lt.trans_eq hd)
  have hmem : (fun m => f.coeff m) ∈ (tableOpen_exists P q c h hi v).choose.neighborhood := by
    have hpc := H.2.2.2.2.1 v
    change (fun m => ((raw.lower.coeff m : ℚ) : ℚ_[v.val.val])) ∈
      (tableOpen_exists P q c h hi v).choose.neighborhood at hpc
    simpa only [f,φ,coeff_map,eq_ratCast] using hpc
  refine ⟨(tableOpen_exists P q c h hi v).choose_spec.choose,?_⟩
  have Ht := (tableOpen_exists P q c h hi v).choose_spec.choose_spec f hlt hmem
  change LocalTests h (batchFibre _ v) c _ (MvPolynomial.map φ (vandermondeForm (k := ℚ) (r+1) n ^ raw.degree + raw.lower))
  simpa only [map_add,map_pow,map_vandermonde,hd] using Ht

end UnconditionalCounterexample.Variations.PrivateGuards.Live
