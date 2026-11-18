import HereditaryAtomicity.DVRBase.MultiplaceDescentProfile
import HereditaryAtomicity.DVRBase.MultiplaceFiniteIsolation

/-! Finite source descent terminates with the joint finite-fibre condition. -/
noncomputable section
namespace HereditaryAtomicity.DVRBase
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- An actual strict source chain with finite top support and a fixed exact
ratio support. It contains no class-finiteness or descent conclusion. -/
structure SupportedSourceChain (R : Type*) [CommRing R]
    (S : Finset (MaximalSpectrum R)) where
  endpoint : ℕ → R
  ratio : ℕ → R
  endpoint_ne_zero : ∀ n, endpoint n ≠ 0
  step : ∀ n, endpoint n = endpoint (n + 1) * ratio n
  ratio_nonunit : ∀ n, ¬ IsUnit (ratio n)
  finite_top : Set.Finite {P : MaximalSpectrum R | endpoint 0 ∈ P.asIdeal}
  support : ∀ n (P : MaximalSpectrum R), ratio n ∈ P.asIdeal ↔ P ∈ S

namespace SupportedSourceChain
variable [IsDomain R] [Ring.KrullDimLE 1 R]

omit [IsDomain R] [Ring.KrullDimLE 1 R] in
theorem recurrent (S : Finset (MaximalSpectrum R)) (C : SupportedSourceChain R S)
    (P : MaximalSpectrum R) : Set.Infinite {n | C.ratio n ∈ P.asIdeal} ↔ P ∈ S := by
  simp only [C.support]
  by_cases hP : P ∈ S
  · simp only [hP, Set.ofPred_true, iff_true]
    exact Set.infinite_univ
  · simp only [hP, Set.ofPred_false, iff_false]
    exact Set.finite_empty.not_infinite

/-- Descending along components strictly decreases the finite recurrent support, so it reaches
a source chain with joint finite fibres. Every intermediate chain and final support are
constructed from genuine component ideals; joint finite fibres is not an assumption. -/
theorem exists_jointFiniteFibers
    (S : Finset (MaximalSpectrum R)) (π : MaximalSpectrum R → R)
    (hU : ∀ P ∈ S, IsClopenInFiber (π P) {P})
    (C : SupportedSourceChain R S) (hS : S.Nonempty) :
    ∃ (T : Finset (MaximalSpectrum R)) (hTS : T ⊆ S) (C' : SupportedSourceChain R T),
      T.Nonempty ∧ JointFiniteFibers (componentPrefixProfile T (fun P => π P)
        (fun P => hU P (hTS P.property)) C'.endpoint C'.endpoint_ne_zero) := by
  classical
  revert hU C hS
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hU C hS
    by_cases hj : JointFiniteFibers (componentPrefixProfile S (fun P => π P)
        (fun P => hU P P.property) C.endpoint C.endpoint_ne_zero)
    · exact ⟨S, Finset.Subset.refl S, C, hS, hj⟩
    · obtain ⟨S', n₀, E, c, a, hne, hsub, hE, hc, hc0, hca, hna, hfinite, hsupport, hrec⟩ :=
        exists_proper_recurrent_chain_of_not_jointFiniteFibers S (fun P => π P)
          (fun P => hU P P.property) C.endpoint C.ratio C.endpoint_ne_zero C.step
          C.finite_top (fun P => (C.recurrent S P).mpr P.property)
          (fun n P hp => (C.support n P).mp hp) hj
      let C' : SupportedSourceChain R S' := ⟨c, a, hc, hca, hna, hfinite, hsupport⟩
      obtain ⟨T, hTS', C'', hT, hjT⟩ := ih S' hsub
        (fun P hP => hU P (hsub.le hP)) C' hne
      exact ⟨T, hTS'.trans hsub.le, C'', hT, hjT⟩

omit [IsDomain R] [Ring.KrullDimLE 1 R] in
/-- Literal blocking constructs the common-support source package from an
original chain and its actual recurrent set. -/
theorem exists_of_recurrent_set
    (S : Finset (MaximalSpectrum R)) (hS : S.Nonempty)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hfinite : Set.Finite {P : MaximalSpectrum R | x 0 ∈ P.asIdeal})
    (hrec : ∀ P : MaximalSpectrum R, Set.Infinite {n | t n ∈ P.asIdeal} ↔ P ∈ S) :
    ∃ (C : SupportedSourceChain R S) (f : ℕ → ℕ),
      StrictMono f ∧ ∀ n, C.endpoint n = x (f n) := by
  obtain ⟨f, r, hf, _, hfr, hrsupp⟩ := exists_sourceChain_recurrent_blocking x t hxt hfinite
    Set.univ Set.infinite_univ
  have hs (n : ℕ) (P : MaximalSpectrum R) : r n ∈ P.asIdeal ↔ P ∈ S :=
    (hrsupp n P).trans (hrec P)
  have hnonunit (n : ℕ) : ¬ IsUnit (r n) := by
    obtain ⟨P, hP⟩ := hS
    intro hu
    exact (inferInstance : P.asIdeal.IsPrime).ne_top
      (P.asIdeal.eq_top_of_isUnit_mem ((hs n P).mpr hP) hu)
  have htop : Set.Finite {P : MaximalSpectrum R | x (f 0) ∈ P.asIdeal} :=
    hfinite.subset (fun P hP => P.asIdeal.mem_of_dvd
      (sourceChain_endpoint_dvd_top x t hxt (f 0)) hP)
  exact ⟨⟨fun n => x (f n), r, fun n => hx (f n), hfr, hnonunit, htop, hs⟩, f, hf, fun _ => rfl⟩

end SupportedSourceChain

/-- Finite top support and genuine nonunit ratios force a nonempty finite
actual recurrent set. This does not assume a recurrent centre exists. -/
theorem exists_finite_nonempty_recurrent_set
    (x t : ℕ → R) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hnonunit : ∀ n, ¬ IsUnit (t n))
    (hfinite : Set.Finite {P : MaximalSpectrum R | x 0 ∈ P.asIdeal}) :
    ∃ S : Finset (MaximalSpectrum R), S.Nonempty ∧
      ∀ P : MaximalSpectrum R, Set.Infinite {n | t n ∈ P.asIdeal} ↔ P ∈ S := by
  classical
  let recSet : Set (MaximalSpectrum R) := {P | Set.Infinite {n | t n ∈ P.asIdeal}}
  have hrecfinite : recSet.Finite := hfinite.subset (by
    intro P hP
    obtain ⟨n, hn⟩ := hP.nonempty
    exact P.asIdeal.mem_of_dvd (sourceChain_ratio_dvd_top x t hxt n) hn)
  have hrecne : recSet.Nonempty := by
    by_contra hn
    have hall (P : MaximalSpectrum R) : Set.Finite {n | t n ∈ P.asIdeal} := by
      apply Set.not_infinite.mp
      exact fun hP => hn ⟨P, hP⟩
    let T := {P : MaximalSpectrum R // x 0 ∈ P.asIdeal}
    let : Fintype T := hfinite.fintype
    have hcover : (⋃ P : T, {n | t n ∈ P.val.asIdeal}) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro n
      obtain ⟨I, hI, htI⟩ := exists_max_ideal_of_mem_nonunits (hnonunit n)
      let P : MaximalSpectrum R := ⟨I, hI⟩
      have hxP : x 0 ∈ P.asIdeal := I.mem_of_dvd (sourceChain_ratio_dvd_top x t hxt n) htI
      exact Set.mem_iUnion.mpr ⟨⟨P, hxP⟩, htI⟩
    have hu : (Set.univ : Set ℕ).Finite := hcover ▸ Set.finite_iUnion (fun P : T => hall P)
    exact Set.infinite_univ hu
  refine ⟨hrecfinite.toFinset, ?_, fun P => (Set.Finite.mem_toFinset hrecfinite).symm⟩
  obtain ⟨P, hP⟩ := hrecne
  exact ⟨P, (Set.Finite.mem_toFinset hrecfinite).mpr hP⟩

variable [IsDomain R] [Ring.KrullDimLE 1 R]

/-- Finite component descent from the original strict chain. The genuine
component classes reach joint finite fibres on an actual source chain whose recurrent set is
contained in the original one. No class-finiteness premise is supplied. -/
theorem exists_jointFiniteFibers_sourceChain
    (π : MaximalSpectrum R → R)
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hnonunit : ∀ n, ¬ IsUnit (t n))
    (hfinite : Set.Finite {P : MaximalSpectrum R | x 0 ∈ P.asIdeal})
    (hU : ∀ P : MaximalSpectrum R, Set.Infinite {n | t n ∈ P.asIdeal} →
      IsClopenInFiber (π P) {P}) :
    ∃ (S : Finset (MaximalSpectrum R))
      (hSrec : ∀ P ∈ S, Set.Infinite {n | t n ∈ P.asIdeal})
      (C : SupportedSourceChain R S), S.Nonempty ∧
      JointFiniteFibers (componentPrefixProfile S (fun P => π P)
        (fun P => hU P (hSrec P P.property)) C.endpoint C.endpoint_ne_zero) := by
  obtain ⟨S, hS, hrec⟩ := exists_finite_nonempty_recurrent_set x t hxt hnonunit hfinite
  obtain ⟨C, _, _, _⟩ := SupportedSourceChain.exists_of_recurrent_set S hS x t hx hxt hfinite hrec
  obtain ⟨T, hTS, C', hT, hj⟩ := C.exists_jointFiniteFibers S π
    (fun P hP => hU P ((hrec P).mpr hP)) hS
  exact ⟨T, fun P hP => (hrec P).mpr (hTS hP), C', hT, hj⟩

end HereditaryAtomicity.DVRBase

namespace HereditaryAtomicity.DVRBase
open scoped BigOperators
variable {R : Type*} [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R]

/-- Every strict source chain with finite top support admits actual finite
component descent to joint finite fibres. The singleton component geometry is constructed from the
original finite top; it is not a hypothesis. -/
theorem exists_jointFiniteFibers_sourceChain_of_finite_top
    (x t : ℕ → R) (hx : ∀ n, x n ≠ 0) (hxt : ∀ n, x n = x (n + 1) * t n)
    (hnonunit : ∀ n, ¬ IsUnit (t n))
    (hfinite : Set.Finite {P : MaximalSpectrum R | x 0 ∈ P.asIdeal}) :
    ∃ (S : Finset (MaximalSpectrum R)) (C : SupportedSourceChain R S)
      (hU : ∀ P : S, IsClopenInFiber (x 0) {P.val}),
      S.Nonempty ∧ (∀ P ∈ S, Set.Infinite {n | t n ∈ P.asIdeal}) ∧
      JointFiniteFibers (componentPrefixProfile S (fun _ => x 0) hU
        C.endpoint C.endpoint_ne_zero) := by
  have hU (P : MaximalSpectrum R) (hrec : Set.Infinite {n | t n ∈ P.asIdeal}) :
      IsClopenInFiber (x 0) {P} := by
    obtain ⟨n, hn⟩ := hrec.nonempty
    have hxP := P.asIdeal.mem_of_dvd (sourceChain_ratio_dvd_top x t hxt n) hn
    exact isClopenInFiber_singleton_of_finite_support (x 0) (x 0) (hx 0) hfinite P hxP hxP
  obtain ⟨S, hSrec, C, hS, hj⟩ := exists_jointFiniteFibers_sourceChain
    (fun _ => x 0) x t hx hxt hnonunit hfinite hU
  exact ⟨S, C, fun P => hU P (hSrec P P.property), hS, hSrec, hj⟩
end HereditaryAtomicity.DVRBase
