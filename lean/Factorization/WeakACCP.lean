import Factorization.CommonDivisors
import Factorization.Hereditary
import Factorization.PrincipalChainAt
import Mathlib.RingTheory.Coprime.Basic

/-! # Weak ACCP and strong atomicity -/

namespace Factorization

/-- Weak ACCP asks for an accessible residual of an original entry of each
finite nonempty family of nonzero elements. -/
def IsWeakACCP (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  IsAtomicDomain R ∧ ∀ s : Finset R, s.Nonempty → (∀ x ∈ s, x ≠ 0) →
    ∃ d : R, (∀ x ∈ s, d ∣ x) ∧ ∃ x ∈ s, ∃ q : R, x = d * q ∧ Acc DvdNotUnit q

/-- In a strongly atomic domain every nonzero pair admits a maximal common
divisor, equivalently a common factor leaving relatively prime residuals. -/
def IsStronglyAtomicDomain (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  IsAtomicDomain R ∧ ∀ a b : R, a ≠ 0 → b ≠ 0 →
    ∃ d q r : R, a = d * q ∧ b = d * r ∧ IsRelPrime q r

/-- Weak ACCP in every unital subring, with its intrinsic divisibility. -/
def IsHereditarilyWeakACCP (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ T : Subring R, IsWeakACCP T

/-- Strong atomicity in every unital subring. -/
def IsHereditarilyStronglyAtomic (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ T : Subring R, IsStronglyAtomicDomain T

variable {R : Type*} [CommRing R] [IsDomain R]

/-- For a domain satisfying ACCP the common divisor may always be one. -/
theorem isWeakACCP_of_wfDvdMonoid (hR : WfDvdMonoid R) : IsWeakACCP R := by
  refine ⟨isAtomicDomain_of_wfDvdMonoid hR, ?_⟩
  intro s hs _
  obtain ⟨x, hx⟩ := hs
  exact ⟨1, fun y _ => one_dvd y, x, hx, x, (one_mul x).symm, hR.apply x⟩

/-- Weak ACCP gives a maximal common divisor even for finite families. -/
theorem IsWeakACCP.exists_maximalCommonDivisor (hR : IsWeakACCP R) (s : Finset R)
    (hs : s.Nonempty) (hn : ∀ x ∈ s, x ≠ 0) : ∃ d : R, IsMaximalCommonDivisor s d := by
  obtain ⟨d, hd, x, hx, q, hq, ha⟩ := hR.2 s hs hn
  obtain ⟨m, _, hm⟩ := exists_maximalCommonDivisor_of_acc_residual hx (hn x hx) hd hq ha
  exact ⟨m, hm⟩

theorem IsWeakACCP.isStronglyAtomicDomain (hR : IsWeakACCP R) : IsStronglyAtomicDomain R := by
  classical
  refine ⟨hR.1, ?_⟩
  intro a b ha hb
  obtain ⟨d, hd⟩ := hR.exists_maximalCommonDivisor {a, b} (by simp) (by simpa using And.intro ha hb)
  obtain ⟨q, hq⟩ := hd.1 a (by simp)
  obtain ⟨r, hr⟩ := hd.1 b (by simp)
  have hd0 : d ≠ 0 := left_ne_zero_of_mul (hq ▸ ha)
  exact ⟨d, q, r, hq, hr, (isMaximalCommonDivisor_pair_iff hd0).mp (hq ▸ hr ▸ hd)⟩

/-- A relatively prime pair of inaccessible nonzero elements obstructs weak ACCP. -/
theorem not_isWeakACCP_of_isRelPrime {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsRelPrime a b) (haa : ¬ Acc DvdNotUnit a) (hba : ¬ Acc DvdNotUnit b) :
    ¬ IsWeakACCP R := by
  classical
  intro hR
  obtain ⟨d, hd, x, hx, q, hq, hac⟩ := hR.2 {a, b} (by simp) (by simpa using And.intro ha hb)
  obtain ⟨u, hu⟩ := hab (hd a (by simp)) (hd b (by simp))
  have hassoc : Associated q x := ⟨u, by rw [hu, mul_comm, ← hq]⟩
  have hax := hassoc.acc_dvdNotUnit_iff.mp hac
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  exact hx.elim (fun h => haa (h ▸ hax)) (fun h => hba (h ▸ hax))

/-- A relatively prime pair obstructs weak ACCP if a strict principal-ideal
chain starts at each of its members. -/
theorem not_isWeakACCP_of_isRelPrime_of_strictChains {x y : R} (hxy : IsRelPrime x y)
    (hx : HasStrictPrincipalIdealChainAt x) (hy : HasStrictPrincipalIdealChainAt y) :
    ¬ IsWeakACCP R :=
  not_isWeakACCP_of_isRelPrime hx.ne_zero hy.ne_zero hxy
    ((not_acc_dvdNotUnit_iff_hasStrictPrincipalIdealChainAt hx.ne_zero).mpr hx)
    ((not_acc_dvdNotUnit_iff_hasStrictPrincipalIdealChainAt hy.ne_zero).mpr hy)

/-- A Bézout identity supplies relative primality for the two-chain obstruction. -/
theorem not_isWeakACCP_of_isCoprime_of_strictChains {x y : R} (hxy : IsCoprime x y)
    (hx : HasStrictPrincipalIdealChainAt x) (hy : HasStrictPrincipalIdealChainAt y) :
    ¬ IsWeakACCP R :=
  not_isWeakACCP_of_isRelPrime_of_strictChains hxy.isRelPrime hx hy

omit [IsDomain R] in
/-- Accessibility under strict divisibility pulls back through a ring equivalence. -/
theorem acc_dvdNotUnit_of_ringEquiv {S : Type*} [CommRing S]
    (e : R ≃+* S) (x : R) (hx : Acc DvdNotUnit (e x)) : Acc DvdNotUnit x := by
  apply RelHomClass.acc
    (RelHom.mk (fun y : R => e y) ?_ : (DvdNotUnit : R → R → Prop) →r DvdNotUnit) x hx
  intro a b hab
  obtain ⟨ha, u, hnu, hb⟩ := hab
  exact ⟨by simpa using ha, e u, fun hu => hnu ((MulEquiv.isUnit_map e).mp hu),
    by simpa only [map_mul] using congrArg e hb⟩

/-- Weak ACCP uses intrinsic units and is invariant under ring equivalence. -/
theorem IsWeakACCP.of_ringEquiv {S : Type*} [CommRing S] [IsDomain S]
    (hS : IsWeakACCP S) (e : R ≃+* S) : IsWeakACCP R := by
  classical
  refine ⟨(isAtomicDomain_ringEquiv_iff e).mp hS.1, ?_⟩
  intro s hs hn
  have hnon : ∀ y ∈ s.image e, y ≠ 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simpa using hn x hx
  obtain ⟨d, hd, y, hy, q, heq, hacc⟩ := hS.2 (s.image e) (hs.image e) hnon
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  refine ⟨e.symm d, ?_, x, hx, e.symm q, ?_, ?_⟩
  · intro z hz
    simpa using map_dvd e.symm (hd (e z) (Finset.mem_image_of_mem e hz))
  · simpa using congrArg e.symm heq
  · exact acc_dvdNotUnit_of_ringEquiv e _ (by simpa using hacc)

/-- The top subring provides weak ACCP of the ambient domain. -/
theorem IsHereditarilyWeakACCP.isWeakACCP (hR : IsHereditarilyWeakACCP R) : IsWeakACCP R :=
  (hR ⊤).of_ringEquiv (Subring.topEquiv : (⊤ : Subring R) ≃+* R).symm

/-- The implication from weak ACCP to strong atomicity applies inside each subring. -/
theorem IsHereditarilyWeakACCP.isHereditarilyStronglyAtomic
    (hR : IsHereditarilyWeakACCP R) : IsHereditarilyStronglyAtomic R :=
  fun T => (hR T).isStronglyAtomicDomain

end Factorization
