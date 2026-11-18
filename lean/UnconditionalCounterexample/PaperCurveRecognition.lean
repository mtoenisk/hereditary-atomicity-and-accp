import UnconditionalCounterexample.PaperWords

/-!
# The literal geometric-pole recognition lemma

Lemma 5.2 recognizes the pole algebra. The hypotheses are poles at every
omitted geometric point, a pole at infinity, and separation and nonzero first
derivatives at retained points. Irreducibility of the actual omitted factors
turns a pole at one of their roots into denominator divisibility. The actual
nonzero constant coefficients supply the retained point zero internally.
-/

noncomputable section
namespace UnconditionalCounterexample.PaperCurveRecognition
open Polynomial PaperConstruction

abbrev K := AlgebraicClosure ℚ
abbrev B := PoleAlgebra.generated poles

/-- A common geometric root of an irreducible polynomial and another polynomial
forces divisibility already over the original coefficient field. -/
theorem irreducible_dvd_of_common_root {k L : Type*} [Field k] [Field L] [Algebra k L]
    (p q : k[X]) (hp : Irreducible p) (a : L)
    (hpa : p.eval₂ (algebraMap k L) a = 0) (hqa : q.eval₂ (algebraMap k L) a = 0) : p ∣ q := by
  apply hp.dvd_iff_not_isCoprime.mpr
  intro hc
  rcases Polynomial.aeval_ne_zero_of_isCoprime hc a with h | h
  · exact h hpa
  · exact h hqa

/-- Literal manuscript Lemma 5.2 for the actual rational pole algebra.
No denominator-divisibility, retained-point, finiteness, or degree premise
beyond the stated pole at infinity is required. -/
theorem subalgebra_eq_top
    (A : Subalgebra ℚ B)
    (hpoles : ∀ a : K, ¬ PaperWords.Retained a → ∃ f : A,
      ((f : B) : RatFunc ℚ).denom.eval₂ (algebraMap ℚ K) a = 0)
    (hinfinity : ∃ f : A, ((f : B) : RatFunc ℚ).denom.natDegree <
      ((f : B) : RatFunc ℚ).num.natDegree)
    (hsep : ∀ a b : K, PaperWords.Retained a → PaperWords.Retained b → a ≠ b →
      ∃ f : A, RatFunc.eval (algebraMap ℚ K) a ((f : B) : RatFunc ℚ) ≠
        RatFunc.eval (algebraMap ℚ K) b ((f : B) : RatFunc ℚ))
    (htangent : ∀ a : K, PaperWords.Retained a → ∃ f : A,
      CurveRecovery.geometricDerivativeAt K ((f : B) : RatFunc ℚ) a ≠ 0) : A = ⊤ := by
  obtain ⟨s, hs⟩ := hinfinity
  apply CurveRecovery.subalgebra_eq_top_of_geometric_poles poles K
    (by rintro f ⟨j, rfl⟩; exact (construction.chain.raw_monic j).ne_zero) 0
    (by
      rintro f ⟨j, rfl⟩
      rw [eval₂_at_zero]
      exact (_root_.map_ne_zero (algebraMap ℚ K)).mpr (construction.chain.raw_constant_ne_zero j))
    A ?_ s hs ?_ ?_
  · rintro f ⟨j, rfl⟩
    have hirr := construction.chain.raw_irreducible j
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_eval₂_eq_zero (algebraMap ℚ K) (raw j)
      (degree_ne_of_natDegree_ne hirr.natDegree_pos.ne')
    obtain ⟨z, hz⟩ := hpoles a (fun hret => hret j ha)
    exact ⟨z, irreducible_dvd_of_common_root _ _ hirr a ha hz⟩
  · intro a b ha hb hab
    exact hsep a b (fun j => ha (raw j) ⟨j, rfl⟩) (fun j => hb (raw j) ⟨j, rfl⟩) hab
  · intro a ha
    exact htangent a (fun j => ha (raw j) ⟨j, rfl⟩)

end UnconditionalCounterexample.PaperCurveRecognition
