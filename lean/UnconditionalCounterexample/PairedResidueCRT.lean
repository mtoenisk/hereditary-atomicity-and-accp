import UnconditionalCounterexample.PairedResidues
import UnconditionalCounterexample.FiniteOrders
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units

/-!
# Actual integer residue quotients and finite-index orders

The primary and guard residue maps are assembled by CRT, with kernel exactly nD.
The actual coordinate X has unit coordinate difference, giving surjectivity.
The checked FiniteOrders API then proves the manuscript finite-index
classification, quotient generator, and conductor for the literal integer order.
-/

namespace UnconditionalCounterexample.PairedResidues
noncomputable section
open Polynomial GuardSupport PairedDomain

variable (S : Set ℚ[X]) (d : Places)

/-- The same literal residue map indexed by its rational prime. -/
def primePairResidue (p : PrimeIndex) (h : ℕ) :
    domain S d →+* ZMod (p.val ^ h) × ZMod (p.val ^ h) :=
  let e := ZMod.ringEquivCongr
    (congrArg (fun q : PrimeIndex => q.val ^ h) (d.primes.apply_symm_apply p))
  (RingEquiv.prodCongr e e).toRingHom.comp (pairResidue S d (d.primes.symm p) h)

theorem primePairResidue_ker (p : PrimeIndex) (h : ℕ) :
    RingHom.ker (primePairResidue S d p h) =
      Ideal.span {((p.val ^ h : ℕ) : domain S d)} := by
  unfold primePairResidue
  rw [RingHom.ker_comp_of_injective _ (RingEquiv.prodCongr _ _).injective,
    pairResidue_ker_natCast, d.primes.apply_symm_apply]

theorem primePairResidue_X_difference_isUnit (p : PrimeIndex) (h : ℕ)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    IsUnit ((primePairResidue S d p h ⟨RatFunc.X, X_mem S d⟩).2 -
      (primePairResidue S d p h ⟨RatFunc.X, X_mem S d⟩).1) := by
  let e := ZMod.ringEquivCongr
    (congrArg (fun q : PrimeIndex => q.val ^ h) (d.primes.apply_symm_apply p))
  have hu := pairResidue_X_difference_isUnit S d (d.primes.symm p) h
    (primary_not_isUnit d hfirst _) (hguard _)
  change IsUnit (e _ - e _)
  rw [← map_sub]
  exact hu.map e.toRingHom

/-- Primary and guard residue vectors, with one entry for every prime factor. -/
def factorResidue (n : ℕ) (b : Bool) : domain S d →+*
    Π (p : n.primeFactors), ZMod ((p : ℕ) ^ n.factorization p) :=
  RingHom.pi fun p =>
    let f := primePairResidue S d ⟨p, Nat.prime_of_mem_primeFactors p.property⟩
      (n.factorization p)
    if b then (RingHom.snd _ _).comp f else (RingHom.fst _ _).comp f

/-- Literal paired residues assembled by the integer Chinese remainder theorem. -/
def globalResidue (n : ℕ) (hn : n ≠ 0) : domain S d →+* ZMod n × ZMod n :=
  (((ZMod.equivPi n hn).symm.toRingHom).comp (factorResidue S d n false)).prod
    (((ZMod.equivPi n hn).symm.toRingHom).comp (factorResidue S d n true))

@[simp] theorem globalResidue_fst (n : ℕ) (hn : n ≠ 0) (x : domain S d)
    (p : n.primeFactors) :
    ZMod.equivPi n hn (globalResidue S d n hn x).1 p =
      (primePairResidue S d ⟨p, Nat.prime_of_mem_primeFactors p.property⟩
        (n.factorization p) x).1 := by
  simp [globalResidue, factorResidue]

@[simp] theorem globalResidue_snd (n : ℕ) (hn : n ≠ 0) (x : domain S d)
    (p : n.primeFactors) :
    ZMod.equivPi n hn (globalResidue S d n hn x).2 p =
      (primePairResidue S d ⟨p, Nat.prime_of_mem_primeFactors p.property⟩
        (n.factorization p) x).2 := by
  simp [globalResidue, factorResidue]

theorem globalResidue_eq_zero_iff (n : ℕ) (hn : n ≠ 0) (x : domain S d) :
    globalResidue S d n hn x = 0 ↔
      ∀ (p : n.primeFactors), primePairResidue S d
        ⟨p, Nat.prime_of_mem_primeFactors p.property⟩ (n.factorization p) x = 0 := by
  constructor
  · intro hx p
    apply Prod.ext
    · have h := congrArg (fun z : ZMod n × ZMod n => ZMod.equivPi n hn z.1 p) hx
      simpa only [globalResidue_fst, Prod.fst_zero, map_zero, Pi.zero_apply] using h
    · have h := congrArg (fun z : ZMod n × ZMod n => ZMod.equivPi n hn z.2 p) hx
      simpa only [globalResidue_snd, Prod.snd_zero, map_zero, Pi.zero_apply] using h
  · intro hx
    apply Prod.ext
    · apply (ZMod.equivPi n hn).injective
      ext p
      simpa only [globalResidue_fst, Prod.fst_zero, map_zero, Pi.zero_apply] using
        congrArg Prod.fst (hx p)
    · apply (ZMod.equivPi n hn).injective
      ext p
      simpa only [globalResidue_snd, Prod.snd_zero, map_zero, Pi.zero_apply] using
        congrArg Prod.snd (hx p)

/-- Coprime prime-power kernels intersect in the literal ideal nD. -/
theorem globalResidue_ker (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (globalResidue S d n hn) = Ideal.span {(n : domain S d)} := by
  calc
    RingHom.ker (globalResidue S d n hn) =
        ⨅ (p : n.primeFactors), RingHom.ker (primePairResidue S d
          ⟨p, Nat.prime_of_mem_primeFactors p.property⟩ (n.factorization p)) := by
      ext x
      simpa only [Ideal.mem_iInf, RingHom.mem_ker] using globalResidue_eq_zero_iff S d n hn x
    _ = ⨅ (p : n.primeFactors), Ideal.span {(((p : ℕ) ^ n.factorization p : ℕ) : domain S d)} := by
      simp only [primePairResidue_ker]
    _ = Ideal.span {(n : domain S d)} := by
      rw [Ideal.iInf_span_singleton_natCast n.pairwise_coprime_pow_primeFactors_factorization,
        ← Nat.prod_primeFactors_coe_pow_factorization hn]

theorem globalResidue_X_difference_isUnit (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    IsUnit ((globalResidue S d n hn ⟨RatFunc.X, X_mem S d⟩).2 -
      (globalResidue S d n hn ⟨RatFunc.X, X_mem S d⟩).1) := by
  have h : IsUnit (ZMod.equivPi n hn
      ((globalResidue S d n hn ⟨RatFunc.X, X_mem S d⟩).2 -
        (globalResidue S d n hn ⟨RatFunc.X, X_mem S d⟩).1)) := by
    apply Pi.isUnit_iff.mpr
    intro p
    simpa only [map_sub, Pi.sub_apply, globalResidue_fst, globalResidue_snd] using
      primePairResidue_X_difference_isUnit S d
        ⟨p, Nat.prime_of_mem_primeFactors p.property⟩ (n.factorization p) hfirst hguard
  simpa using h.map (ZMod.equivPi n hn).symm.toRingHom

theorem globalResidue_surjective (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    Function.Surjective (globalResidue S d n hn) :=
  pairMap_surjective_of_unit_difference _ _ ⟨RatFunc.X, X_mem S d⟩
    (globalResidue_X_difference_isUnit S d n hn hfirst hguard)

/-- The actual quotient ring D/nD, including the trivial case n=1. -/
def integerQuotientEquiv (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    (domain S d ⧸ Ideal.span {(n : domain S d)}) ≃+* ZMod n × ZMod n :=
  (Ideal.quotEquivOfEq (globalResidue_ker S d n hn).symm).trans
    (RingHom.quotientKerEquivOfSurjective (globalResidue_surjective S d n hn hfirst hguard))

@[simp] theorem integerQuotientEquiv_mk (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q))
    (x : domain S d) :
    integerQuotientEquiv S d n hn hfirst hguard
      (Ideal.Quotient.mk (Ideal.span {(n : domain S d)}) x) = globalResidue S d n hn x := rfl

/-- The additive quotient by the literal order Z+nD is cyclic of order n. -/
def orderQuotientEquiv (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    (domain S d ⧸ (PaperTargets.integerOrder (domain S d) n).toAddSubgroup) ≃+ ZMod n :=
  FiniteOrders.integerOrderQuotientEquiv n (globalResidue S d n hn)
    (globalResidue_surjective S d n hn hfirst hguard) (globalResidue_ker S d n hn)

@[simp] theorem orderQuotientEquiv_mk (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q))
    (x : domain S d) :
    orderQuotientEquiv S d n hn hfirst hguard
      (QuotientAddGroup.mk' (PaperTargets.integerOrder (domain S d) n).toAddSubgroup x) =
      (globalResidue S d n hn x).2 - (globalResidue S d n hn x).1 := rfl

theorem orderQuotient_generated_by_X (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    ∀ x : domain S d ⧸ (PaperTargets.integerOrder (domain S d) n).toAddSubgroup,
      ∃ z : ℤ, z • QuotientAddGroup.mk'
        (PaperTargets.integerOrder (domain S d) n).toAddSubgroup ⟨RatFunc.X, X_mem S d⟩ = x :=
  FiniteOrders.integerOrderQuotient_generated_by_unit_difference n (globalResidue S d n hn)
    (globalResidue_surjective S d n hn hfirst hguard) (globalResidue_ker S d n hn)
    ⟨RatFunc.X, X_mem S d⟩ (globalResidue_X_difference_isUnit S d n hn hfirst hguard)

theorem order_index (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    (PaperTargets.integerOrder (domain S d) n).toAddSubgroup.index = n :=
  FiniteOrders.index_integerOrder n (globalResidue S d n hn)
    (globalResidue_surjective S d n hn hfirst hguard) (globalResidue_ker S d n hn)

theorem order_conductor (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    RadicalConductor.conductorIdeal (PaperTargets.integerOrder (domain S d) n) =
      Ideal.span {(n : domain S d)} :=
  FiniteOrders.conductor_integerOrder n (globalResidue S d n hn)
    (globalResidue_surjective S d n hn hfirst hguard) (globalResidue_ker S d n hn)

/-- The manuscript's two-value congruence characterization at every prime divisor. -/
theorem mem_order_iff_prime_congruences (n : ℕ) (hn : n ≠ 0) (x : domain S d) :
    x ∈ PaperTargets.integerOrder (domain S d) n ↔
      ∀ (p : n.primeFactors),
        (primePairResidue S d ⟨p, Nat.prime_of_mem_primeFactors p.property⟩
          (n.factorization p) x).1 =
        (primePairResidue S d ⟨p, Nat.prime_of_mem_primeFactors p.property⟩
          (n.factorization p) x).2 := by
  rw [show PaperTargets.integerOrder (domain S d) n =
      FiniteOrders.residueOrder (globalResidue S d n hn) from
    FiniteOrders.integerOrder_eq_residueOrder n _ (globalResidue_ker S d n hn)]
  change (globalResidue S d n hn x).1 = (globalResidue S d n hn x).2 ↔ _
  rw [← (ZMod.equivPi n hn).injective.eq_iff, funext_iff]
  simp only [globalResidue_fst, globalResidue_snd]

theorem finite_integerQuotient (n : ℕ) (hn : n ≠ 0)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q)) :
    Finite (domain S d ⧸ Ideal.span {(n : domain S d)}) := by
  let : NeZero n := ⟨hn⟩
  exact Finite.of_equiv (ZMod n × ZMod n)
    (integerQuotientEquiv S d n hn hfirst hguard).symm.toEquiv

/-- Proposition 7.3: inclusion Z+nD⊆T and equal index identify every finite-index subring. -/
theorem finite_index_subring_eq_order (n : ℕ) (hn : 0 < n)
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q))
    (T : Subring (domain S d)) (hindex : T.toAddSubgroup.index = n) :
    T = PaperTargets.integerOrder (domain S d) n :=
  FiniteOrders.finite_index_subring_eq_integerOrder n hn (globalResidue S d n hn.ne')
    (globalResidue_surjective S d n hn.ne' hfirst hguard) (globalResidue_ker S d n hn.ne') T hindex

theorem finite_quotient_iff_order
    (hfirst : ¬ IsUnit (d.primary 0)) (hguard : ∀ q, IsUnit (d.guard q))
    (T : Subring (domain S d)) :
    Finite (domain S d ⧸ T.toAddSubgroup) ↔
      ∃ n : ℕ, 0 < n ∧ T = PaperTargets.integerOrder (domain S d) n := by
  constructor
  · intro hfinite
    have hn : 0 < T.toAddSubgroup.index :=
      Nat.pos_of_ne_zero (T.toAddSubgroup.index_ne_zero_iff_finite.mpr hfinite)
    exact ⟨T.toAddSubgroup.index, hn,
      finite_index_subring_eq_order S d _ hn hfirst hguard T rfl⟩
  · rintro ⟨n,hn,rfl⟩
    apply (PaperTargets.integerOrder (domain S d) n).toAddSubgroup.index_ne_zero_iff_finite.mp
    rw [order_index S d n hn.ne' hfirst hguard]
    exact hn.ne'

end
end UnconditionalCounterexample.PairedResidues
