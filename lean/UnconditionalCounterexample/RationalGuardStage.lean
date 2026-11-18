import UnconditionalCounterexample.PaperGuardStages

/-!
# Rational factors determine the guard stage

The finite previous rational raw family and its denominator support determine
actual monic integral models at every unassigned prime. Degree is preserved,
so the next exponential cutoff is computed before any new raw coefficient.
The ordinary and auxiliary guard steps return norm-one evaluations of the actual
rational raw polynomials, not merely units of unrelated local models.

At each stage of Proposition 3.1, a finite batch of new primes receives its permanent guard arguments.
-/

namespace UnconditionalCounterexample.RationalGuardStage

open Polynomial GuardSupport PaperGuardStages

/-- The next cutoff uses only previous raw degrees and the new degree already
chosen, before any new raw coefficient or p-adic approximation is selected. -/
def nextCutoff {J : Type*} [Fintype J] (Q : J → ℚ[X]) (oldM stage newDegree : ℕ) : ℕ :=
  max oldM (max stage (2 ^ (4 + (∑ j, (Q j).natDegree) + newDegree))) + 1

theorem nextCutoff_bounds {J : Type*} [Fintype J] (Q : J → ℚ[X])
    (oldM stage newDegree : ℕ) :
    oldM < nextCutoff Q oldM stage newDegree ∧ stage < nextCutoff Q oldM stage newDegree ∧
      2 ^ (4 + (∑ j, (Q j).natDegree) + newDegree) < nextCutoff Q oldM stage newDegree := by
  unfold nextCutoff
  have h1 := le_max_left oldM (max stage (2 ^ (4 + (∑ j, (Q j).natDegree) + newDegree)))
  have h2 := le_max_right oldM (max stage (2 ^ (4 + (∑ j, (Q j).natDegree) + newDegree)))
  have h3 := le_max_left stage (2 ^ (4 + (∑ j, (Q j).natDegree) + newDegree))
  have h4 := le_max_right stage (2 ^ (4 + (∑ j, (Q j).natDegree) + newDegree))
  omega

/-- Translate a unit evaluation of an integral model into the actual rational
raw-polynomial evaluation of norm one. -/
theorem norm_eval_eq_one_of_integral_model {p : ℕ} [Fact p.Prime]
    (Q : ℚ[X]) (G : ℤ_[p][X])
    (hG : G.map (algebraMap ℤ_[p] ℚ_[p]) = Q.map (algebraMap ℚ ℚ_[p]))
    (β : ℤ_[p]) (hu : IsUnit (G.eval β)) :
    ‖Q.eval₂ (algebraMap ℚ ℚ_[p]) β.val‖ = 1 := by
  have heval := congrArg (Polynomial.eval β.val) hG
  rw [eval_map, eval_map] at heval
  have heq : ((G.eval β : ℤ_[p]) : ℚ_[p]) = Q.eval₂ (algebraMap ℚ ℚ_[p]) β.val := by
    change G.eval₂ (algebraMap ℤ_[p] ℚ_[p]) ((algebraMap ℤ_[p] ℚ_[p]) β) = _ at heval
    rw [eval₂_at_apply] at heval
    exact heval
  rw [← heq]
  exact PadicInt.isUnit_iff.mp hu

/-- Integral models of every prior rational raw, constructed from the actual
finite denominator-support invariant rather than supplied as stage inputs. -/
theorem exists_models {J : Type*} (A : Assignment) (Q : J → ℚ[X])
    (hQ : ∀ j, (Q j).Monic)
    (hsupp : ∀ j n (p : PrimeIndex), p.val ∣ ((Q j).coeff n).den → p ∈ A.primes) :
    ∃ F : (p : PrimeIndex) → J → ℤ_[p.val][X], ∀ p ∉ A.primes, ∀ j,
      (F p j).map (algebraMap ℤ_[p.val] ℚ_[p.val]) = (Q j).map (algebraMap ℚ ℚ_[p.val]) ∧
      (F p j).natDegree = (Q j).natDegree ∧ (F p j).Monic := by
  classical
  have hex (p : PrimeIndex) (hp : p ∉ A.primes) (j : J) :
      ∃ G : ℤ_[p.val][X], G.map (algebraMap ℤ_[p.val] ℚ_[p.val]) =
        (Q j).map (algebraMap ℚ ℚ_[p.val]) ∧ G.natDegree = (Q j).natDegree ∧ G.Monic := by
    have hfresh (q : A.primes) : q.val.val ≠ p.val := by
      intro heq
      apply hp
      have hqp : q.val = p := Subtype.ext heq
      exact hqp ▸ q.property
    obtain ⟨G, hmap, hdegree, hmonic⟩ := GuardStages.exists_integral_polynomial_model
      (fun q : A.primes => q.val.val) (Q j) (fun n q hprime hdiv =>
        ⟨⟨⟨q, hprime⟩, hsupp j n ⟨q, hprime⟩ hdiv⟩, rfl⟩) p.val hfresh
    exact ⟨G, hmap, hdegree, hmonic (hQ j)⟩
  let F (p : PrimeIndex) (j : J) : ℤ_[p.val][X] :=
    if hp : p ∉ A.primes then (hex p hp j).choose else 1
  refine ⟨F, ?_⟩
  intro p hp j
  simpa only [F, dite_eq_left hp] using (hex p hp j).choose_spec

/-- The ordinary guard transition now consumes only prior rational raw factors,
their support invariant, and the paper's previous-cutoff coverage. -/
theorem exists_rational_stage_transition {J : Type*} [Fintype J]
    (A : Assignment) (Q : J → ℚ[X]) (hQ : ∀ j, (Q j).Monic)
    (hsupp : ∀ j n (p : PrimeIndex), p.val ∣ ((Q j).coeff n).den → p ∈ A.primes)
    (i M : ℕ) (required : Finset PrimeIndex)
    (hcovered : GuardStages.primesThrough (2 ^ (4 + ∑ j, (Q j).natDegree)) ⊆ A.primes) :
    ∃ B : Assignment, B.primes = nextPrimes A M required ∧ A.primes ⊆ B.primes ∧
      (∀ p (hp : p ∈ A.primes) (hpB : p ∈ B.primes), B.guard p hpB = A.guard p hp) ∧
      ∀ p (hp : p ∈ B.primes), p ∉ A.primes →
        (B.guard p hp).birth = i ∧ PadicInt.toZMod (B.guard p hp).value ≠ 1 ∧
        ∀ j, ‖(Q j).eval₂ (algebraMap ℚ ℚ_[p.val]) (B.guard p hp).value.val‖ = 1 := by
  classical
  obtain ⟨F, hF⟩ := exists_models A Q hQ hsupp
  have hdegree (p : PrimeIndex) (hp : p ∉ A.primes) :
      (∑ j, (F p j).natDegree) ≤ ∑ j, (Q j).natDegree := by
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro j _
    exact (hF p hp j).2.1
  obtain ⟨B, hBT, hAB, hOld, hNew⟩ := PaperGuardStages.exists_stage_transition
    A i (∑ j, (Q j).natDegree) M required hcovered Finset.univ F
    (fun p hp j _ => (hF p hp j).2.2) hdegree
  refine ⟨B, hBT, hAB, hOld, ?_⟩
  intro p hp hn
  obtain ⟨hbirth, hres, hraw⟩ := hNew p hp hn
  refine ⟨hbirth, hres, ?_⟩
  intro j
  exact norm_eval_eq_one_of_integral_model (Q j) (F p j) (hF p hn j).1
    (B.guard p hp).value (hraw j (Finset.mem_univ j))

/-- Coverage of the concrete next cutoff already covers the degree budget for
the next stage, without needing any coefficient of the new raw polynomial. -/
theorem next_degree_cutoff_covered {J : Type*} [Fintype J]
    (Q : J → ℚ[X]) (oldM stage newDegree : ℕ) (A : Assignment)
    (required : Finset PrimeIndex) :
    GuardStages.primesThrough (2 ^ (4 + (∑ j, (Q j).natDegree) + newDegree)) ⊆
      nextPrimes A (nextCutoff Q oldM stage newDegree) required := by
  intro p hp
  apply cutoff_subset_nextPrimes A (nextCutoff Q oldM stage newDegree) required
  apply (GuardStages.mem_primesThrough p _).mpr
  exact ((GuardStages.mem_primesThrough p _).mp hp).trans
    (nextCutoff_bounds Q oldM stage newDegree).2.2.le

/-- The auxiliary choice also uses only the actual prior rational polynomials
and their coefficient support, and remains distinct from the processing set. -/
theorem exists_rational_auxiliary_guard {J : Type*} [Fintype J]
    (A : Assignment) (Q : J → ℚ[X]) (hQ : ∀ j, (Q j).Monic)
    (hsupp : ∀ j n (p : PrimeIndex), p.val ∣ ((Q j).coeff n).den → p ∈ A.primes)
    (i M : ℕ) :
    ∃ ell : PrimeIndex, ∃ g : Guard ell, M < ell.val ∧ ell ∉ A.primes ∧
      g.birth = i ∧ PadicInt.toZMod g.value ≠ 1 ∧
      ∀ j, ‖(Q j).eval₂ (algebraMap ℚ ℚ_[ell.val]) g.value.val‖ = 1 := by
  classical
  obtain ⟨F, hF⟩ := exists_models A Q hQ hsupp
  have hdegree (p : PrimeIndex) (hp : p ∉ A.primes) :
      (∑ j, (F p j).natDegree) ≤ ∑ j, (Q j).natDegree := by
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro j _
    exact (hF p hp j).2.1
  obtain ⟨ell, g, hlarge, hfresh, hbirth, hres, hraw⟩ := PaperGuardStages.exists_fresh_auxiliary_guard
    A i (∑ j, (Q j).natDegree) M Finset.univ F (fun p hp j _ => (hF p hp j).2.2) hdegree
  refine ⟨ell, g, hlarge, hfresh, hbirth, hres, ?_⟩
  intro j
  exact norm_eval_eq_one_of_integral_model (Q j) (F ell j) (hF ell hfresh j).1
    g.value (hraw j (Finset.mem_univ j))

end UnconditionalCounterexample.RationalGuardStage
