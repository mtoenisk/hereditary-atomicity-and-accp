import UnconditionalCounterexample.FiniteOrders
import UnconditionalCounterexample.PrimaryChoices
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Prime-index subrings distinguish the varying-prime examples

This is the invariant and counting part of manuscript Corollary
Corollary 8.2. An actual quotient map to `ZMod p`
with kernel pR rules out a unital subring of additive index p; a surjection
to `ZMod p × ZMod p` supplies one by taking the diagonal preimage. Existence
of such a subring is preserved by abstract ring equivalence.

The permanent endpoint `signature_eq_of_residue_pattern` recovers the
selected prime set from actual one/two-factor residue maps, and
`not_ringEquiv_of_distinct_signatures` then excludes an isomorphism.
`cardinal_infinite_prime_sets` proves the parameter space has continuum size
using an explicit even/odd prime-index encoding.

The mixed one-point and paired construction realizes these residue signatures.
-/

noncomputable section
namespace UnconditionalCounterexample.PrimeIndexSignature

universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- Existence of an actual unital subring of the stated additive index. -/
def HasIndexSubring (R : Type u) [CommRing R] (p : ℕ) : Prop :=
  ∃ T : Subring R, T.toAddSubgroup.index = p

/-- A ring equivalence preserves existence of an index-p unital subring. -/
theorem hasIndexSubring_iff_of_equiv (e : R ≃+* A) (p : ℕ) :
    HasIndexSubring R p ↔ HasIndexSubring A p := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T.map e.toRingHom, ?_⟩
    change (T.toAddSubgroup.map e.toAddEquiv.toAddMonoidHom).index = p
    exact (T.toAddSubgroup.index_map_equiv e.toAddEquiv).trans hT
  · rintro ⟨T, hT⟩
    refine ⟨T.map e.symm.toRingHom, ?_⟩
    change (T.toAddSubgroup.map e.symm.toAddEquiv.toAddMonoidHom).index = p
    exact (T.toAddSubgroup.index_map_equiv e.symm.toAddEquiv).trans hT

/-- A one-factor residue quotient leaves no proper integer order. -/
theorem integerOrder_eq_top_of_single_residue (p : ℕ) (f : R →+* ZMod p)
    (hker : RingHom.ker f = Ideal.span {(p : R)}) :
    FiniteOrders.integerOrder (R := R) p = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (f x)
  have hx : x - (z : R) ∈ Ideal.span {(p : R)} := by
    rw [← hker, RingHom.mem_ker]
    simp only [map_sub, map_intCast, hz, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  refine ⟨z, y, ?_⟩
  rw [← hy]
  ring

/-- In the single-residue case there is no unital subring of prime index. -/
theorem not_hasIndexSubring_of_single_residue (p : ℕ) (hp : p.Prime)
    (f : R →+* ZMod p) (hker : RingHom.ker f = Ideal.span {(p : R)}) :
    ¬ HasIndexSubring R p := by
  rintro ⟨T, hT⟩
  have hle := FiniteOrders.integerOrder_le_of_index T p hT
  rw [integerOrder_eq_top_of_single_residue p f hker] at hle
  have htop : T = ⊤ := top_le_iff.mp hle
  have hindex : (1 : ℕ) = p := by simpa [htop] using hT
  exact hp.ne_one hindex.symm

/-- The diagonal preimage supplies a subring of index p in the paired case. -/
theorem hasIndexSubring_of_pair_residue (p : ℕ) (f : R →+* ZMod p × ZMod p)
    (hf : Function.Surjective f) : HasIndexSubring R p :=
  ⟨FiniteOrders.residueOrder f, FiniteOrders.index_residueOrder p f hf⟩

/-- An intrinsic signature of the abstract ring. -/
def signature (R : Type u) [CommRing R] : Set GuardSupport.PrimeIndex :=
  {p | HasIndexSubring R p.val}

theorem signature_eq_of_equiv (e : R ≃+* A) : signature R = signature A := by
  ext p
  exact hasIndexSubring_iff_of_equiv e p.val

/-- The actual one/two-factor residue pattern determines this signature. -/
theorem signature_eq_of_residue_pattern (S : Set GuardSupport.PrimeIndex)
    (hpair : ∀ p ∈ S, ∃ f : R →+* ZMod p.val × ZMod p.val, Function.Surjective f)
    (hsingle : ∀ p ∉ S, ∃ f : R →+* ZMod p.val,
      RingHom.ker f = Ideal.span {(p.val : R)}) : signature R = S := by
  classical
  ext p
  constructor
  · intro hp
    by_contra hnot
    obtain ⟨f, hker⟩ := hsingle p hnot
    exact not_hasIndexSubring_of_single_residue p.val p.property f hker hp
  · intro hp
    obtain ⟨f, hf⟩ := hpair p hp
    exact hasIndexSubring_of_pair_residue p.val f hf

/-- Distinct literal residue signatures preclude an abstract ring isomorphism. -/
theorem not_ringEquiv_of_distinct_signatures
    {S T : Set GuardSupport.PrimeIndex} (hS : signature R = S)
    (hT : signature A = T) (hne : S ≠ T) : ¬ Nonempty (R ≃+* A) := by
  rintro ⟨e⟩
  exact hne (hS.symm.trans ((signature_eq_of_equiv e).trans hT))

/-- A concrete encoding into infinite prime sets: odd-indexed primes are
always retained and even-indexed primes encode an arbitrary subset of ℕ. -/
def encodedPrimes (S : Set ℕ) : Set GuardSupport.PrimeIndex :=
  (fun n => PrimaryChoices.primes (2 * n)) '' S ∪
    Set.range (fun n => PrimaryChoices.primes (2 * n + 1))

theorem mem_encodedPrimes_even (S : Set ℕ) (n : ℕ) :
    PrimaryChoices.primes (2 * n) ∈ encodedPrimes S ↔ n ∈ S := by
  constructor
  · rintro (⟨m, hm, heq⟩ | ⟨m, heq⟩)
    · have hmn : m = n := by have := PrimaryChoices.primes.injective heq; omega
      exact hmn ▸ hm
    · have := PrimaryChoices.primes.injective heq
      omega
  · intro hn
    exact Or.inl ⟨n, hn, rfl⟩

theorem encodedPrimes_infinite (S : Set ℕ) : (encodedPrimes S).Infinite := by
  apply (Set.infinite_range_of_injective (f := fun n => PrimaryChoices.primes (2 * n + 1)) ?_).mono
    Set.subset_union_right
  intro m n h
  have := PrimaryChoices.primes.injective h
  omega

def encodeInfinitePrimes : Set ℕ ↪ {S : Set GuardSupport.PrimeIndex // S.Infinite} where
  toFun S := ⟨encodedPrimes S, encodedPrimes_infinite S⟩
  inj' := by
    intro S T h
    ext n
    rw [← mem_encodedPrimes_even S n, ← mem_encodedPrimes_even T n]
    exact Set.ext_iff.mp (Subtype.ext_iff.mp h) _

/-- The parameter space in manuscript §8.2 has exactly continuum size. -/
theorem cardinal_infinite_prime_sets :
    Cardinal.mk {S : Set GuardSupport.PrimeIndex // S.Infinite} = Cardinal.continuum := by
  apply le_antisymm
  · calc
      Cardinal.mk {S : Set GuardSupport.PrimeIndex // S.Infinite} ≤
          Cardinal.mk (Set GuardSupport.PrimeIndex) := Cardinal.mk_subtype_le _
      _ = Cardinal.continuum := by
        rw [Cardinal.mk_set, Cardinal.mk_congr PrimaryChoices.primes.toEquiv.symm]
        simp
  · rw [← Cardinal.mk_set_nat]
    exact Cardinal.mk_le_of_injective encodeInfinitePrimes.injective

end UnconditionalCounterexample.PrimeIndexSignature
