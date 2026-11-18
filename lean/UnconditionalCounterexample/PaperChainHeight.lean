import UnconditionalCounterexample.TailRatioChains
import UnconditionalCounterexample.PaperSquareChainActual
import UnconditionalCounterexample.PaperAtoms
import UnconditionalCounterexample.FiniteDivisorBounds

namespace UnconditionalCounterexample.PaperConstruction
open FiniteDivisorBounds

/-- In every unital subring, low-order elements have finitely many actual divisors. -/
theorem finite_subring_divisors_of_order_le_one (T : Subring domain) (x : T) (hx : x ≠ 0)
    (horder : PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ) ≤ 1) :
    {a : T | a ∣ x}.Finite := by
  apply finite_divisors_subring T x
  exact finite_divisors_of_finite_classes (fun u hu => (isUnit_iff_sign u).mp hu)
    (finite_associates_divisors_of_order_le_one x (fun h => hx (Subtype.ext h)) horder)

/-- The low-order finiteness statement concerns intrinsic atoms of the subring. -/
theorem finite_subring_factorizations_of_order_le_one (T : Subring domain) (x : T) (hx : x ≠ 0)
    (horder : PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ) ≤ 1) :
    {s : Multiset T | (∀ a ∈ s, Irreducible a) ∧ Associated s.prod x}.Finite :=
  finite_atomic_factorizations hx (finite_subring_divisors_of_order_le_one T x hx horder)

theorem subring_bounded_of_order_le_one (T : Subring domain) (x : T) (hx : x ≠ 0)
    (horder : PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ) ≤ 1) :
    Factorization.HasBoundedFactorizations x :=
  hasBoundedFactorizations_of_finite_divisor_classes hx
    (finite_classes_of_finite_divisors (finite_subring_divisors_of_order_le_one T x hx horder))

/-- Proposition 7.4 for the actual single constructed domain and every finite-index subring. -/
theorem finite_index_chain_height (T : Subring domain) (hfinite : Finite (domain ⧸ T.toAddSubgroup))
    (x : T) (hx : x ≠ 0) :
    HasStrictChainAt x ↔ 2 ≤ PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ) := by
  constructor
  · intro hchain
    by_contra hhigh
    exact not_hasStrictChainAt_of_finite_divisors
      (finite_subring_divisors_of_order_le_one T x hx (by omega)) hchain
  · exact TailRatioChains.high_order_chain_of_finite_index places qPole qPole_isUnit
      qPole_primary qPole_guard T hfinite x hx

/-- At finite index, bounded nonunit decompositions occur exactly at orders zero and one. -/
theorem finite_index_bounded_iff_low_order
    (T : Subring domain) (hfinite : Finite (domain ⧸ T.toAddSubgroup)) (x : T) (hx : x ≠ 0) :
    Factorization.HasBoundedFactorizations x ↔
      PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ) ≤ 1 := by
  constructor
  · intro hbounded
    by_contra hhigh
    exact ConductorChains.not_bounded_of_strict_chain
      ((finite_index_chain_height T hfinite x hx).mpr (by omega)) hbounded
  · exact subring_bounded_of_order_le_one T x hx

/-- Atomicity turns the constructed high-order chains into unbounded atom lengths. -/
theorem finite_index_atom_lengths_unbounded_of_atomicity
    (T : Subring domain) (hfinite : Finite (domain ⧸ T.toAddSubgroup))
    (hatomic : Factorization.IsAtomicDomain T) (x : T) (hx : x ≠ 0)
    (horder : 2 ≤ PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ)) :
    ¬ BddAbove (Factorization.factorizationLengths x) :=
  ConductorChains.atom_lengths_unbounded_of_strict_chain hatomic hx
    ((finite_index_chain_height T hfinite x hx).mpr horder)

/-- The actual element [D:T]·t² witnesses order two in every finite-index subring. -/
theorem exists_order_two_of_finite_index
    (T : Subring domain) (hfinite : Finite (domain ⧸ T.toAddSubgroup)) :
    ∃ x : T, x ≠ 0 ∧ PrimaryStabilization.tOrder ((x : domain) : RatFunc ℚ) = 2 := by
  let n := T.toAddSubgroup.index
  have hn : n ≠ 0 := T.toAddSubgroup.index_ne_zero_iff_finite.mpr hfinite
  have hmem : (n : domain) * parameter^2 ∈ T := by
    change (n : domain) * parameter^2 ∈ T.toAddSubgroup
    simpa only [nsmul_eq_mul] using T.toAddSubgroup.nsmul_index_mem (parameter^2)
  let x : T := ⟨(n : domain) * parameter^2,hmem⟩
  have hnR : (n : RatFunc ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hxR : (n : RatFunc ℚ) * RatFunc.X^2 ≠ 0 :=
    mul_ne_zero hnR (pow_ne_zero 2 RatFunc.X_ne_zero)
  refine ⟨x, ?_, ?_⟩
  · intro h
    exact hxR (congrArg (fun z : T => ((z : domain) : RatFunc ℚ)) h)
  · change PrimaryStabilization.tOrder ((n : RatFunc ℚ)*RatFunc.X^2) = 2
    rw [PrimaryStabilization.tOrder_mul hnR (pow_ne_zero 2 RatFunc.X_ne_zero), pow_two,
      PrimaryStabilization.tOrder_mul RatFunc.X_ne_zero RatFunc.X_ne_zero,
      PrimaryStabilization.tOrder_X]
    have hC : (n : RatFunc ℚ) = RatFunc.C (n : ℚ) := (map_natCast RatFunc.C n).symm
    rw [hC, PrimaryStabilization.tOrder_C]
    norm_num

theorem finite_index_not_wfDvdMonoid
    (T : Subring domain) (hfinite : Finite (domain ⧸ T.toAddSubgroup)) : ¬ WfDvdMonoid T := by
  obtain ⟨x,hx,horder⟩ := exists_order_two_of_finite_index T hfinite
  obtain ⟨y,_,_,hy⟩ := (finite_index_chain_height T hfinite x hx).mpr (by omega)
  exact Factorization.not_wfDvdMonoid_iff_exists_strictMono_principalIdealChain.mpr
    ⟨fun i => Ideal.span ({y i} : Set T), fun i => ⟨y i,rfl⟩, hy⟩

theorem finite_index_not_isBFDomain
    (T : Subring domain) (hfinite : Finite (domain ⧸ T.toAddSubgroup)) : ¬ Factorization.IsBFDomain T := by
  obtain ⟨x,hx,horder⟩ := exists_order_two_of_finite_index T hfinite
  intro hBF
  have hlow := (finite_index_bounded_iff_low_order T hfinite x hx).mp (hBF x hx)
  omega

end UnconditionalCounterexample.PaperConstruction
