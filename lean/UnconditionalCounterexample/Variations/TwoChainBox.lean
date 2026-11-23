import UnconditionalCounterexample.LowOrderDivisors
import Mathlib.Data.Fintype.Prod

/-!
# Common divisors at the two centres

Fix all endpoint and outside values of a divisor. On each primary tail the
difference from a representative is eventually zero. Where the representative
has settled and the top has order at most one, all differences have the same
sign. The overlapping congruences force equality there, uniformly over the
class. The bounding top may depend on the colour.
-/

namespace UnconditionalCounterexample.Variations.TwoChainBox

/-- If two primary profiles have the same endpoint and their difference is
principal, one fixed stabilization cutoff for the representative and the
bound controls the entire tail of the other profile. -/
theorem eq_tail_of_small_bound {u z : ℕ → ℕ} {e k : ℕ}
    (hu : ∀ i, 2 * k + 1 ≤ i → u i = e)
    (hz : ∃ N, ∀ i, N ≤ i → z i = e)
    (hsmall : ∀ i, 2 * k + 1 ≤ i → z i ≤ 1)
    (he : e ≤ 1) (hcong : TripleCongruent (fun i => (z i : ℤ) - u i)) :
    ∀ i, 2 * k + 1 ≤ i → z i = u i := by
  let g := fun i => (z i : ℤ) - u i
  obtain ⟨N, hN⟩ := hz
  have hevent : EventuallyConstantProfile g 0 := by
    refine ⟨max N (2 * k + 1), fun i hi => ?_⟩
    simp only [g, hN i (by omega), hu i (by omega), sub_self]
  by_cases hzero : e = 0
  · have h := tail_eq_zero_of_triple_congruences g k hevent (by
      intro i hi
      specialize hsmall i hi
      dsimp [g]
      rw [hu i hi, hzero]
      omega) (fun n _ => hcong.2 n)
    intro i hi
    specialize h i hi
    dsimp [g] at h
    omega
  · have hneg : EventuallyConstantProfile (fun i => -g i) 0 := by
      obtain ⟨M, hM⟩ := hevent
      exact ⟨M, fun i hi => by simp only [hM i hi, neg_zero]⟩
    have h := tail_eq_zero_of_triple_congruences (fun i => -g i) k hneg (by
      intro i hi
      specialize hsmall i hi
      dsimp [g]
      rw [hu i hi]
      omega) (by
        intro n _
        rw [← neg_add, ← neg_add]
        exact Int.emod_eq_zero_of_dvd ((Int.dvd_neg).mpr (Int.dvd_of_emod_eq_zero (hcong.2 n))))
    intro i hi
    specialize h i hi
    dsimp [g] at h
    omega

/-- In a fixed endpoint/outside class, just the bounded finite prefixes of
the two primary tails distinguish profiles. -/
private theorem finite_primary_profiles {A : Type*} (v : A → Bool → ℕ → ℕ)
    (top : Bool → ℕ → ℕ) (e : Bool → ℕ)
    (hbound : ∀ a c i, v a c i ≤ top c i)
    (htop : ∀ c, ∃ N, ∀ i, N ≤ i → top c i ≤ 1)
    (he : ∀ c, e c ≤ 1)
    (hevent : ∀ a c, ∃ N, ∀ i, N ≤ i → v a c i = e c)
    (hcong : ∀ a b c, TripleCongruent (fun i => (v a c i : ℤ) - v b c i)) :
    (Set.range v).Finite := by
  classical
  by_cases ha : Nonempty A
  · let u : A := Classical.choice ha
    choose k hk using htop
    choose m hm using hevent u
    let N := fun c => 2 * max (k c) (m c) + 1
    have htail (a : A) (c : Bool) : ∀ i, N c ≤ i → v a c i = v u c i := by
      apply eq_tail_of_small_bound (e := e c)
      · intro i hi
        exact hm c i (by omega)
      · exact hevent a c
      · intro i hi
        exact (hbound a c i).trans (hk c i (by omega))
      · exact he c
      · exact hcong a u c
    let code (a : A) (c : Bool) (i : Fin (N c)) : Fin (top c i + 1) :=
      ⟨v a c i, Nat.lt_succ_of_le (hbound a c i)⟩
    apply ValuationProfiles.finite_range_of_finite_code v code
    intro a b hab
    funext c i
    by_cases hi : i < N c
    · exact congrArg Fin.val (congrFun (congrFun hab c) ⟨i, hi⟩)
    · exact (htail a c i (by omega)).trans (htail b c i (by omega)).symm
  · exact Set.finite_empty.subset (fun _ ⟨a, _⟩ => (ha ⟨a⟩).elim)

/-- Valuation data used to pass from the integer-profile box to common divisor
classes. The common divisibility and quotient congruences are in the given ring.
The outside places exclude both endpoints and both primary tails. -/
structure Orders (R : Type*) [CommRing R] [IsDomain R] (ι : Type*) where
  endpoint : R → Bool → ℕ
  primary : R → Bool → ℕ → ℕ
  outside : R → ι → ℕ
  eventually_primary : ∀ x, x ≠ 0 → ∀ c, ∃ N, ∀ i, N ≤ i → primary x c i = endpoint x c
  finite_outside : ∀ x, x ≠ 0 → {i | outside x i ≠ 0}.Finite
  le_of_dvd : ∀ {z x}, x ≠ 0 → z ∣ x →
    (∀ c, endpoint z c ≤ endpoint x c) ∧ (∀ c i, primary z c i ≤ primary x c i) ∧
    (∀ i, outside z i ≤ outside x i)
  difference_triple : ∀ z u, z ≠ 0 → u ≠ 0 → endpoint z = endpoint u → outside z = outside u →
    ∀ c, TripleCongruent (fun i => (primary z c i : ℤ) - primary u c i)
  associated_of_eq : ∀ z u, z ≠ 0 → u ≠ 0 → endpoint z = endpoint u → outside z = outside u →
    primary z = primary u → Associated z u

variable {R ι : Type*} [CommRing R] [IsDomain R]

/-- The common divisors of the whole family have finitely many
associate classes if *for each* colour some member has endpoint order at most
one. In particular the two members witnessing this hypothesis may differ. -/
theorem finite_common_divisor_classes (v : Orders R ι) (s : Finset R)
    (hs : ∀ x ∈ s, x ≠ 0) (hlow : ∀ c, ∃ x ∈ s, v.endpoint x c ≤ 1) :
    (Associates.mk '' {z : R | ∀ x ∈ s, z ∣ x}).Finite := by
  classical
  choose x hx hxe using hlow
  let Z := {z : R // ∀ y ∈ s, z ∣ y}
  have hle (z : Z) (c : Bool) := v.le_of_dvd (hs _ (hx c)) (z.property _ (hx c))
  have hnz (z : Z) : z.val ≠ 0 := ne_zero_of_dvd_ne_zero (hs _ (hx false)) (z.property _ (hx false))
  let I := {i : ι // v.outside (x false) i ≠ 0}
  let : Fintype I := (v.finite_outside _ (hs _ (hx false))).fintype
  let C := (Bool → Fin 2) × ((i : I) → Fin (v.outside (x false) i.val + 1))
  let : Fintype C := by unfold C; infer_instance
  let key (z : Z) : C :=
    (fun c => ⟨v.endpoint z.val c, Nat.lt_succ_of_le (((hle z c).1 c).trans (hxe c))⟩,
     fun i => ⟨v.outside z.val i.val, Nat.lt_succ_of_le ((hle z false).2.2 _)⟩)
  have hequal {a b : Z} (h : key a = key b) :
      v.endpoint a.val = v.endpoint b.val ∧ v.outside a.val = v.outside b.val := by
    constructor
    · funext c
      exact congrArg Fin.val (congrFun (congrArg Prod.fst h) c)
    · funext i
      by_cases hi : v.outside (x false) i = 0
      · have ha := (hle a false).2.2 i
        have hb := (hle b false).2.2 i
        omega
      · exact congrArg Fin.val (congrFun (congrArg Prod.snd h) ⟨i, hi⟩)
  let fiber (k : C) := {z : Z // key z = k}
  let cls (z : Z) := Associates.mk z.val
  have hfin (k : C) : (Set.range fun a : fiber k => cls a.val).Finite := by
    let p (a : fiber k) := v.primary a.val.val
    have hlim (a : fiber k) (c : Bool) : v.endpoint a.val.val c = (k.1 c).val :=
      congrArg Fin.val (congrFun (congrArg Prod.fst a.property) c)
    have hp : (Set.range p).Finite := by
      apply finite_primary_profiles p (fun c => v.primary (x c) c) (fun c => (k.1 c).val)
      · exact fun a c i => (hle a.val c).2.1 c i
      · intro c
        obtain ⟨N, hN⟩ := v.eventually_primary _ (hs _ (hx c)) c
        exact ⟨N, fun i hi => (hN i hi).le.trans (hxe c)⟩
      · exact fun c => Nat.le_of_lt_succ (k.1 c).isLt
      · intro a c
        obtain ⟨N, hN⟩ := v.eventually_primary _ (hnz a.val) c
        exact ⟨N, fun i hi => (hN i hi).trans (hlim a c)⟩
      · intro a b c
        have hab := hequal (a.property.trans b.property.symm)
        exact v.difference_triple _ _ (hnz a.val) (hnz b.val) hab.1 hab.2 c
    let : Finite (Set.range p) := hp.to_subtype
    apply ValuationProfiles.finite_range_of_finite_code _ (fun a : fiber k => Set.rangeFactorization p a)
    intro a b hab
    have hk := hequal (a.property.trans b.property.symm)
    exact Associates.mk_eq_mk_iff_associated.mpr (v.associated_of_eq _ _
      (hnz a.val) (hnz b.val) hk.1 hk.2 (congrArg Subtype.val hab))
  apply (Set.finite_iUnion hfin).subset
  rintro _ ⟨z, hz, rfl⟩
  let a : Z := ⟨z, hz⟩
  exact Set.mem_iUnion.mpr ⟨key a, ⟨⟨a, rfl⟩, rfl⟩⟩

/-- The two witness entries can have arbitrary orders at the opposite
endpoints. This specialization uses the two entries independently. -/
theorem finite_common_divisor_classes_pair (v : Orders R ι) {x y : R}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hleft : v.endpoint x false ≤ 1) (hright : v.endpoint y true ≤ 1) :
    (Associates.mk '' {z : R | z ∣ x ∧ z ∣ y}).Finite := by
  classical
  have h := finite_common_divisor_classes v {x, y} (by simp [hx, hy]) (by
    intro c
    cases c with
    | false => exact ⟨x, by simp, hleft⟩
    | true => exact ⟨y, by simp, hright⟩)
  simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using h

/-- The moving profile at either centre is an atom. A factor of endpoint
order zero there also vanishes at the opposite centre. Its only possible
primary support is on the designated tail, where the one-colour obstruction
eliminates it. -/
theorem irreducible_of_primaryAtomProfile (v : Orders R ι)
    (hendpoint_one : ∀ c, v.endpoint 1 c = 0)
    (hprimary_one : ∀ c j, v.primary 1 c j = 0)
    (houtside_one : ∀ i, v.outside 1 i = 0)
    (hadd : ∀ a b : R, a ≠ 0 → b ≠ 0 → ∀ c,
      v.endpoint (a * b) c = v.endpoint a c + v.endpoint b c)
    {x : R} (hx : x ≠ 0) (c : Bool) (n : ℕ)
    (hactive : v.endpoint x c = 1)
    (hinactive : ∀ d, d ≠ c → v.endpoint x d = 0)
    (hprimary : ∀ i, (v.primary x c i : ℤ) = primaryAtomProfile n i)
    (hother : ∀ d, d ≠ c → ∀ i, v.primary x d i = 0)
    (hout : ∀ i, v.outside x i = 0) : Irreducible x := by
  have hunit {z : R} (hzx : z ∣ x) (hzlimit : v.endpoint z c = 0) : IsUnit z := by
    have hz := ne_zero_of_dvd_ne_zero hx hzx
    obtain ⟨he, hp, ho⟩ := v.le_of_dvd hx hzx
    have hzend : v.endpoint z = v.endpoint 1 := by
      funext d
      rw [hendpoint_one d]
      by_cases h : d = c
      · simpa [h] using hzlimit
      · exact Nat.eq_zero_of_le_zero ((he d).trans (hinactive d h).le)
    have hzout : v.outside z = v.outside 1 := by
      funext i
      rw [houtside_one i]
      exact Nat.eq_zero_of_le_zero ((ho i).trans (hout i).le)
    have hc := v.difference_triple z 1 hz one_ne_zero hzend hzout c
    simp only [hprimary_one, Nat.cast_zero, sub_zero] at hc
    have hzero : EventuallyConstantProfile (fun j => (v.primary z c j : ℤ)) 0 := by
      obtain ⟨N, hN⟩ := v.eventually_primary z hz c
      exact ⟨N, fun j hj => by simp only [hN j hj, hzlimit, Nat.cast_zero]⟩
    have htail := eq_zero_of_le_primaryAtomProfile (fun j => (v.primary z c j : ℤ)) n
      hzero hc (fun _ => Int.natCast_nonneg _) (fun i => by
        rw [← hprimary]
        exact_mod_cast hp c i)
    have hzprim : v.primary z = v.primary 1 := by
      funext d i
      rw [hprimary_one]
      by_cases hd : d = c
      · subst d
        have hi := congrFun htail i
        exact_mod_cast (show (v.primary z c i : ℤ) = 0 from hi)
      · exact Nat.eq_zero_of_le_zero ((hp d i).trans (hother d hd i).le)
    exact (associated_one_iff_isUnit.mp (v.associated_of_eq _ _ hz one_ne_zero hzend hzout hzprim))
  constructor
  · intro h
    have he := (v.le_of_dvd one_ne_zero (h.dvd : x ∣ 1)).1 c
    rw [hactive, hendpoint_one] at he
    omega
  · intro a b hab
    have hne : a * b ≠ 0 := hab ▸ hx
    have h := hadd a b (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne) c
    rw [← hab, hactive] at h
    by_cases ha : v.endpoint a c = 0
    · exact Or.inl (hunit ⟨b, hab⟩ ha)
    · exact Or.inr (hunit ⟨a, hab.trans (mul_comm _ _)⟩ (by omega))

/-- Orders of the sequence of moving atoms belonging to one colour. -/
structure MovingProfiles (v : Orders R ι) (c : Bool) (a : ℕ → R) : Prop where
  ne_zero : ∀ n, a n ≠ 0
  endpoint : ∀ n, v.endpoint (a n) c = 1
  other_endpoint : ∀ n d, d ≠ c → v.endpoint (a n) d = 0
  primary : ∀ n i, (v.primary (a n) c i : ℤ) = primaryAtomProfile n i
  other_primary : ∀ n d, d ≠ c → ∀ i, v.primary (a n) d i = 0
  outside : ∀ n i, v.outside (a n) i = 0

/-- Converse to order monotonicity on nonzero elements. Each primary tail
and both horizontal endpoints are included in the test. -/
def Orders.DetectsDivisibility (v : Orders R ι) : Prop :=
  ∀ a b, a ≠ 0 → b ≠ 0 → v.endpoint a ≤ v.endpoint b →
    v.primary a ≤ v.primary b → v.outside a ≤ v.outside b → a ∣ b

/-- Every sufficiently late atom of colour `c` divides a given nonzero element
of order at least two at that centre. -/
theorem MovingProfiles.eventually_dvd {v : Orders R ι} (hdvd : v.DetectsDivisibility)
    {c : Bool} {a : ℕ → R} (h : MovingProfiles v c a) {x : R} (hx : x ≠ 0)
    (hhigh : 2 ≤ v.endpoint x c) : ∃ N : ℕ, ∀ n ≥ N, a n ∣ x := by
  obtain ⟨N, hN⟩ := v.eventually_primary x hx c
  refine ⟨N, fun n hn => hdvd _ _ (h.ne_zero n) hx ?_ ?_ ?_⟩
  · intro d
    by_cases heq : d = c
    · subst d
      exact (h.endpoint n).le.trans ((by decide : 1 ≤ 2).trans hhigh)
    · rw [h.other_endpoint n d heq]
      exact Nat.zero_le _
  · intro d i
    by_cases heq : d = c
    · subst d
      have hgoal : (v.primary (a n) c i : ℤ) ≤ (v.primary x c i : ℤ) := by
        rw [h.primary]
        by_cases hi : i < 2 * n
        · rw [primaryAtomProfile_of_lt hi]
          exact Int.natCast_nonneg _
        · rw [hN i (by omega)]
          unfold primaryAtomProfile
          split_ifs <;> omega
      exact_mod_cast hgoal
    · rw [h.other_primary n d heq]
      exact Nat.zero_le _
  · intro i
    rw [h.outside]
    exact Nat.zero_le _

/-- One cutoff for the whole family permits a subsequent choice of an atom
returning to 1 modulo an integer conductor. -/
theorem MovingProfiles.eventually_common_dvd {v : Orders R ι} (hdvd : v.DetectsDivisibility)
    {c : Bool} {a : ℕ → R} (h : MovingProfiles v c a) (s : Finset R)
    (hs : ∀ x ∈ s, x ≠ 0) (hhigh : ∀ x ∈ s, 2 ≤ v.endpoint x c) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, a n ∣ x := by
  classical
  have hcut (x : s) := h.eventually_dvd hdvd (hs _ x.property) (hhigh _ x.property)
  choose N hN using hcut
  refine ⟨s.attach.sup N, fun n hn x hx => hN ⟨x, hx⟩ n ?_⟩
  exact (Finset.le_sup (f := N) (Finset.mem_attach s ⟨x, hx⟩)).trans hn

end UnconditionalCounterexample.Variations.TwoChainBox
