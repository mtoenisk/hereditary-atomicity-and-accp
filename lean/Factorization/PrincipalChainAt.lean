import Factorization.PrincipalIdeals

/-!
# Principal-ideal chains starting at a specified element
-/

namespace Factorization

variable {R : Type*} [CommSemiring R]

/-- An infinite strictly ascending chain of nonzero principal ideals whose first
generator is the specified element. -/
def HasStrictPrincipalIdealChainAt (x : R) : Prop :=
  ∃ f : ℕ → R, f 0 = x ∧ (∀ n, f n ≠ 0) ∧
    StrictMono (fun n => Ideal.span ({f n} : Set R))

theorem HasStrictPrincipalIdealChainAt.ne_zero {x : R}
    (h : HasStrictPrincipalIdealChainAt x) : x ≠ 0 := by
  obtain ⟨f, rfl, hn, _⟩ := h
  exact hn 0

/-- For a nonzero element, failure of accessibility for strict divisibility is
equivalent to a strict principal-ideal chain starting at that very element. -/
theorem not_acc_dvdNotUnit_iff_hasStrictPrincipalIdealChainAt [IsDomain R] {x : R}
    (hx : x ≠ 0) : ¬ Acc DvdNotUnit x ↔ HasStrictPrincipalIdealChainAt x := by
  rw [not_acc_iff_exists_descending_chain]
  constructor
  · rintro ⟨f, hf, hstep⟩
    refine ⟨f, hf, ?_, strictMono_nat_of_lt_succ fun n =>
      Ideal.span_singleton_lt_span_singleton.mpr (hstep n)⟩
    rintro (_ | n)
    · exact hf ▸ hx
    · exact (hstep n).1
  · rintro ⟨f, hf, _, hstrict⟩
    exact ⟨f, hf, fun n => Ideal.span_singleton_lt_span_singleton.mp
      (hstrict (Nat.lt_succ_self n))⟩

end Factorization
