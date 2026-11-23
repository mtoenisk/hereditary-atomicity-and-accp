import UnconditionalCounterexample.Variations.PrivateGuardsLive

/-!
# Simultaneous recursion for the main polynomials and the private primes

Each accepted main choice sees only the completed rounds. Its actual
polynomial and reserved primes are then frozen and tested by the new
puncture. The resulting pair is present for every later main choice.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.PrivateGuards.Live

open MvPolynomial GuardSupport MultivariateSelection

variable {r d : ℕ} {M : ℕ → Type*}

/-- The local/global main selector can attach arbitrary extra state and
certificates (for example the ordinary and primary data). -/
structure Rule (r : ℕ) (M : ℕ → Type*) (c : Fin (r+1) → ℚ) where
  Accepts : ∀ n, History r M n → MainChoice r n (M n) → Prop
  produces : ∀ n (h : History r M n), Function.Injective (fun j => (h j).prime.val) →
    ∃ m : MainChoice r n (M n), eval c (m.entry.raw n) ≠ 0 ∧
      UnitsAt h (m.entry.raw n) ∧ Accepts n h m

variable {c : Fin (r+1) → ℚ}

/-- Finite list frozen *after* the choice of this round's main polynomial. -/
def checkedAt {n : ℕ} (test : Finset (Poly r)) (h : History r M n) (m : MainChoice r n (M n)) :
    Finset (Poly r) := by
  classical
  exact insert (m.entry.raw n) (test ∪ (Finset.univ.image (fun j : Fin n => (h j).entry.raw j.val) ∪
    Finset.univ.image (fun j : Fin n => (h j).puncture)))

/-- Includes all prime assignments of the main selector, now and in earlier
rounds, as well as every previously chosen private prime. -/
def reservedAt {n : ℕ} (h : History r M n) (m : MainChoice r n (M n)) : Finset PrimeIndex := by
  classical
  exact m.reserved ∪ (Finset.univ.biUnion fun j : Fin n => insert (h j).prime (h j).reserved)

structure Accepted (rule : Rule r M c) (P : PrimeSpectrum (Poly r)) (Q : Ideal (Poly r))
    {n : ℕ} (test : Finset (Poly r)) (h : History r M n) (v : Round r n (M n)) : Prop where
  main_ok : rule.Accepts n h v.toMainChoice
  survives : eval c (v.entry.raw n) ≠ 0
  prior_units : UnitsAt h (v.entry.raw n)
  checked_eq : v.checked = checkedAt test h v.toMainChoice
  punctures : v.puncture ∈ P.asIdeal
  avoids_retained : v.puncture ∉ Q
  avoids_tests : ∀ f ∈ v.checked, ¬ v.puncture ∣ f
  prime_gt : ∀ p ∈ reservedAt h v.toMainChoice, p.val < v.prime.val

private theorem successor {n : ℕ} (rule : Rule r M c) (P Q : PrimeSpectrum (Poly r))
    (hsmall : Q.asIdeal.height < P.asIdeal.height) (hlarge : 1 < P.asIdeal.height)
    (test : Finset (Poly r)) (ht : ∀ f ∈ test, f ≠ 0) (h : History r M n)
    (hi : Function.Injective (fun j => (h j).prime.val)) :
    ∃ v, Accepted rule P Q.asIdeal test h v := by
  classical
  obtain ⟨m,hs,hu,hm⟩ := rule.produces n h hi
  let S := checkedAt test h m
  have hS (f : Poly r) (hf : f ∈ S) : f ≠ 0 := by
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact m.irreducible.ne_zero
    rcases Finset.mem_union.mp hf with hf | hf
    · exact ht _ hf
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hf
      exact (h j).irreducible.ne_zero
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hf
      exact (h j).irreducible_puncture.ne_zero
  have hp : P.asIdeal ≠ ⊥ := fun he => by simp [he] at hlarge
  let : StrongNormalizationMonoid (Poly r) := UniqueFactorizationMonoid.strongNormalizationMonoid
  obtain ⟨g,hir,hg,hq,hav⟩ := exists_puncture_avoiding_tests P.asIdeal Q.asIdeal hp hsmall hlarge S hS
  let reserved := reservedAt h m
  obtain ⟨p, hbound, ⟨seed⟩⟩ := exists_smoothSeed g hir S hav (reserved.sup Subtype.val)
  obtain ⟨site⟩ := seed.realize
  refine ⟨⟨m,g,hir,p,S,site⟩,hm,hs,hu,rfl,hg,hq,hav,?_⟩
  exact fun q hq => (Finset.le_sup (f := Subtype.val) hq).trans_lt hbound

/-- A coherent family of prefixes extends by one accepted round. -/
private structure Prefix (r : ℕ) (M : ℕ → Type*) (n : ℕ) where
  row : History r M n
  distinct : Function.Injective (fun j => (row j).prime.val)

private theorem old_prime_mem {n : ℕ} (h : History r M n) (m : MainChoice r n (M n)) (i : Fin n) :
    (h i).prime ∈ reservedAt h m := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_insert_self ..⟩)

private def Prefix.snoc {n : ℕ} (h : Prefix r M n) (v : Round r n (M n))
    (hv : ∀ i : Fin n, (h.row i).prime.val < v.prime.val) : Prefix r M (n+1) where
  row := Fin.snoc h.row v
  distinct := by
    let a (i : Fin n) := (h.row i).prime.val
    have he : (fun i : Fin (n+1) => ((Fin.snoc h.row v : History r M (n+1)) i).prime.val) = Fin.snoc a v.prime.val := by
      funext i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]
      | cast i => simp only [Fin.snoc_castSucc]; rfl
    rw [he]
    exact Fin.snoc_injective_of_injective h.distinct (by rintro ⟨i,hi⟩; exact (hv i).ne hi)

variable (rule : Rule r M c) (P : ℕ → PrimeSpectrum (Poly r)) (Q : PrimeSpectrum (Poly r))
  (hs : ∀ n, Q.asIdeal.height < (P n).asIdeal.height) (hl : ∀ n, 1 < (P n).asIdeal.height)
  (test : ℕ → Finset (Poly r)) (ht : ∀ n f, f ∈ test n → f ≠ 0)

private def chronology : (n : ℕ) → Prefix r M n
  | 0 => ⟨fun i => i.elim0,fun i => i.elim0⟩
  | n+1 =>
    let h := chronology n
    let hnext := successor rule (P n) Q (hs n) (hl n) (test n) (ht n) h.row h.distinct
    h.snoc hnext.choose (fun i => hnext.choose_spec.prime_gt _ (old_prime_mem h.row _ i))

private abbrev historyAt (n : ℕ) := (chronology rule P Q hs hl test ht n).row

def round (n : ℕ) : Round r n (M n) :=
  (successor rule (P n) Q (hs n) (hl n) (test n) (ht n)
    (historyAt rule P Q hs hl test ht n) (chronology rule P Q hs hl test ht n).distinct).choose

private theorem history_eq (n : ℕ) (i : Fin n) :
    historyAt rule P Q hs hl test ht n i = round rule P Q hs hl test ht i.val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last =>
      change (Fin.snoc (historyAt rule P Q hs hl test ht n) (round rule P Q hs hl test ht n) :
        History r M (n+1)) (Fin.last n) = _
      simp only [Fin.snoc_last,Fin.val_last]
    | cast i =>
      change (Fin.snoc (historyAt rule P Q hs hl test ht n) (round rule P Q hs hl test ht n) :
        History r M (n+1)) i.castSucc = _
      simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using ih i

/-- The actual stage obeys its local/global acceptance predicate at the
literal earlier stages, and its private guard avoids this stage's actual main. -/
theorem round_accepted (n : ℕ) :
    Accepted rule (P n) Q.asIdeal (test n) (fun j : Fin n => round rule P Q hs hl test ht j.val)
      (round rule P Q hs hl test ht n) := by
  have h := (successor rule (P n) Q (hs n) (hl n) (test n) (ht n)
    (historyAt rule P Q hs hl test ht n) (chronology rule P Q hs hl test ht n).distinct).choose_spec
  have he : historyAt rule P Q hs hl test ht n = (fun j : Fin n => round rule P Q hs hl test ht j.val) :=
    funext (history_eq rule P Q hs hl test ht n)
  change Accepted rule (P n) Q.asIdeal (test n) (historyAt rule P Q hs hl test ht n)
    (round rule P Q hs hl test ht n) at h
  exact he ▸ h

end UnconditionalCounterexample.Variations.PrivateGuards.Live
