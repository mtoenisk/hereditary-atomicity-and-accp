import UnconditionalCounterexample.Profiles

/-!
# The overlapping mod-three obstruction

The first pair and each successive overlapping triple satisfy a congruence modulo
three. A finite effective profile bounded by one on a tail vanishes there after the
first full triple.
-/

namespace UnconditionalCounterexample

/-- The initial relation uses the source convention that the coordinate at -1
is zero. All other relations use natural indices with no subtraction. -/
def TripleCongruent (g : ℕ → ℤ) : Prop :=
  (g 0 + g 1) % 3 = 0 ∧
    ∀ n : ℕ, (g (2 * n + 1) + g (2 * n + 2) + g (2 * n + 3)) % 3 = 0

/-- Three integers in `[0,1]` whose sum is divisible by three are equal. -/
theorem equal_of_small_triple {a b c : ℤ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hsum : (a + b + c) % 3 = 0) : a = b ∧ b = c := by
  omega

/-- Only the tail triple relations are needed to force eventual-zero profiles
bounded by one to vanish from the beginning of that triple tail. -/
theorem tail_eq_zero_of_triple_congruences (g : ℕ → ℤ) (k : ℕ)
    (hzero : EventuallyConstantProfile g 0)
    (hsmall : ∀ i : ℕ, 2 * k + 1 ≤ i → 0 ≤ g i ∧ g i ≤ 1)
    (hcong : ∀ n : ℕ, k ≤ n →
      (g (2 * n + 1) + g (2 * n + 2) + g (2 * n + 3)) % 3 = 0) :
    ∀ i : ℕ, 2 * k + 1 ≤ i → g i = 0 := by
  have heq (n : ℕ) (hn : k ≤ n) :
      g (2 * n + 1) = g (2 * n + 2) ∧
      g (2 * n + 2) = g (2 * n + 3) :=
    equal_of_small_triple (hsmall _ (by omega)) (hsmall _ (by omega))
      (hsmall _ (by omega)) (hcong n hn)
  have hodd (n : ℕ) (hn : k ≤ n) : g (2 * n + 1) = 0 := by
    obtain ⟨N, hN⟩ := hzero
    have hprop (m : ℕ) : g (2 * n + 1) = g (2 * (n + m) + 1) := by
      induction m with
      | zero => simp
      | succ m ih =>
        have hstep := (heq (n + m) (by omega)).1.trans (heq (n + m) (by omega)).2
        calc
          g (2 * n + 1) = g (2 * (n + m) + 1) := ih
          _ = g (2 * (n + m) + 3) := hstep
          _ = g (2 * (n + (m + 1)) + 1) := by congr 1
    exact (hprop N).trans (hN _ (by omega))
  have heven (n : ℕ) (hn : k ≤ n) : g (2 * n + 2) = 0 :=
    (heq n hn).1.symm.trans (hodd n hn)
  intro i hi
  obtain ⟨n, hn, hni⟩ : ∃ n : ℕ, k ≤ n ∧ (i = 2 * n + 1 ∨ i = 2 * n + 2) := by
    refine ⟨(i - 1) / 2, ?_, ?_⟩ <;> omega
  rcases hni with hni | hni
  · simpa only [hni] using hodd n hn
  · simpa only [hni] using heven n hn

/-- Finitely supported effective profiles satisfy the same tail obstruction. -/
theorem finsupp_tail_eq_zero_of_triple_congruent (g : ℕ →₀ ℤ) (k : ℕ)
    (hcong : TripleCongruent g)
    (hsmall : ∀ i : ℕ, 2 * k + 1 ≤ i → 0 ≤ g i ∧ g i ≤ 1) :
    ∀ i : ℕ, 2 * k + 1 ≤ i → g i = 0 :=
  tail_eq_zero_of_triple_congruences g k (finsupp_eventually_zero g) hsmall
    (fun n _ => hcong.2 n)

/-- The profile of `a_n` satisfies all the principal-profile congruences. -/
theorem primaryAtomProfile_tripleCongruent (n : ℕ) :
    TripleCongruent (primaryAtomProfile n) := by
  constructor
  · simp only [primaryAtomProfile]
    split_ifs <;> omega
  · intro k
    simp only [primaryAtomProfile]
    split_ifs <;> omega

/-- There is no nonzero effective eventual-zero principal profile below the
order-one profile of `a_n`. This is the finite-summand obstruction used to show
that the latter profile is an atom. -/
theorem eq_zero_of_le_primaryAtomProfile (g : ℕ → ℤ) (n : ℕ)
    (hzero : EventuallyConstantProfile g 0) (hcong : TripleCongruent g)
    (hnonneg : ∀ i : ℕ, 0 ≤ g i)
    (hle : ∀ i : ℕ, g i ≤ primaryAtomProfile n i) : g = 0 := by
  have hbefore (i : ℕ) (hi : i < 2 * n) : g i = 0 := by
    have h := hle i
    rw [primaryAtomProfile_of_lt hi] at h
    exact le_antisymm h (hnonneg i)
  have htail : ∀ i : ℕ, 2 * n + 1 ≤ i → g i = 0 := by
    apply tail_eq_zero_of_triple_congruences g n hzero
    · intro i hi
      refine ⟨hnonneg i, ?_⟩
      have h := hle i
      rwa [primaryAtomProfile_of_gt (by omega)] at h
    · exact fun k _ => hcong.2 k
  have hpivot : g (2 * n) = 0 := by
    have hg := hle (2 * n)
    rw [primaryAtomProfile_pivot] at hg
    have hgn := hnonneg (2 * n)
    cases n with
    | zero =>
      have h1 := htail 1 (by omega)
      have hc := hcong.1
      simp only [h1, add_zero] at hc
      simp only [Nat.mul_zero] at hg hgn ⊢
      omega
    | succ n =>
      have h1 := hbefore (2 * n + 1) (by omega)
      have h3 := htail (2 * n + 3) (by omega)
      have hc := hcong.2 n
      rw [h1, h3, zero_add, add_zero] at hc
      have heq : 2 * n + 2 = 2 * (n + 1) := by omega
      rw [heq] at hc
      omega
  funext i
  change g i = 0
  by_cases hi : i < 2 * n
  · exact hbefore i hi
  by_cases heq : i = 2 * n
  · simpa only [heq] using hpivot
  · exact htail i (by omega)

/-- The finitely supported form of the order-one profile obstruction. -/
theorem finsupp_eq_zero_of_le_primaryAtomProfile (g : ℕ →₀ ℤ) (n : ℕ)
    (hcong : TripleCongruent g) (hnonneg : ∀ i : ℕ, 0 ≤ g i)
    (hle : ∀ i : ℕ, g i ≤ primaryAtomProfile n i) : g = 0 := by
  have h := eq_zero_of_le_primaryAtomProfile g n (finsupp_eventually_zero g)
    hcong hnonneg hle
  ext i
  exact congrFun h i

end UnconditionalCounterexample
