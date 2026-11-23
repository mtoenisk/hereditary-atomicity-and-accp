import UnconditionalCounterexample.Variations.DyadicSplitCoefficients

/-!
# Extending a finite dyadic profile to the full set of sites

The regular sequences keep their two heights and finite deviations. Newly
indexed auxiliary, guard and horizontal sites receive zero. Signed masses,
field-column translations and the split inequalities are preserved by this
extension.
-/

noncomputable section
namespace UnconditionalCounterexample.DyadicDeviations
open DyadicProfiles (Site)
open Variations.DyadicLedger

variable {J J' : Bool → Type*} {G G' H H' : Type*}

structure ProfileEmbedding (J J' : Bool → Type*) (G G' H H' : Type*) where
  auxiliary : (k : Bool) → J k ↪ J' k
  lone : G ↪ G'
  horizontal : H ↪ H'

namespace ProfileEmbedding
variable (E : ProfileEmbedding J J' G G' H H')

def profile (p : Profile J G H) : Profile J' G' H' where
  height := p.height
  plusDeviation := p.plusDeviation
  minusDeviation := p.minusDeviation
  auxiliary k := (p.auxiliary k).embDomain (E.auxiliary k)
  guards := {
    plus := p.guards.plus
    minus := p.guards.minus
    auxiliary := fun k => (p.guards.auxiliary k).embDomain (E.auxiliary k)
    lone := p.guards.lone.embDomain E.lone }
  horizontal := p.horizontal.embDomain E.horizontal

def supplement : Supplement J G H → Supplement J' G' H'
  | .auxiliary k j => .auxiliary k (E.auxiliary k j)
  | .plusGuard k n => .plusGuard k n
  | .minusGuard k n => .minusGuard k n
  | .auxiliaryGuard k j => .auxiliaryGuard k (E.auxiliary k j)
  | .loneGuard g => .loneGuard (E.lone g)
  | .horizontal h => .horizontal (E.horizontal h)

theorem supplement_channel (i : Supplement J G H) : (E.supplement i).channel = i.channel := by
  cases i <;> rfl

theorem supplement_value (p : Profile J G H) (i : Supplement J G H) :
    (E.profile p).signedValues (.other (E.supplement i)) = p.signedValues (.other i) := by
  cases i <;> simp [Profile.signedValues,profile,supplement]

theorem supplement_cases (j : Supplement J' G' H') :
    (∃ i, E.supplement i = j) ∨ ∀ p : Profile J G H, (E.profile p).signedValues (.other j) = 0 := by
  classical
  cases j with
  | plusGuard k n => exact Or.inl ⟨.plusGuard k n,rfl⟩
  | minusGuard k n => exact Or.inl ⟨.minusGuard k n,rfl⟩
  | auxiliary k x | auxiliaryGuard k x =>
    by_cases h : x ∈ Set.range (E.auxiliary k)
    · obtain ⟨i,rfl⟩ := h
      first | exact Or.inl ⟨.auxiliary k i,rfl⟩ | exact Or.inl ⟨.auxiliaryGuard k i,rfl⟩
    · exact Or.inr (fun _ => Finsupp.embDomain_of_notMem_range _ _ _ h)
  | loneGuard x =>
    by_cases h : x ∈ Set.range E.lone
    · obtain ⟨i,rfl⟩ := h
      exact Or.inl ⟨.loneGuard i,rfl⟩
    · exact Or.inr (fun _ => Finsupp.embDomain_of_notMem_range _ _ _ h)
  | horizontal x =>
    by_cases h : x ∈ Set.range E.horizontal
    · obtain ⟨i,rfl⟩ := h
      exact Or.inl ⟨.horizontal i,rfl⟩
    · exact Or.inr (fun _ => Finsupp.embDomain_of_notMem_range _ _ _ h)

variable (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)
    (index' : (k : Bool) → J' k → ℕ) (sign' : (k : Bool) → J' k → ℤ)
    (hi : ∀ k j, index' k (E.auxiliary k j) = index k j)
    (hs : ∀ k j, sign' k (E.auxiliary k j) = sign k j)

include hi hs in
theorem transfer (k : Bool) (z : J k →₀ ℤ) :
    DyadicColumns.auxiliaryTransfer (index' k) (sign' k) (z.embDomain (E.auxiliary k)) =
      DyadicColumns.auxiliaryTransfer (index k) (sign k) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single j z => simp [DyadicColumns.auxiliaryTransfer,hi,hs]

include hi hs in
theorem signedMass (p : Profile J G H) (k : Bool) :
    (E.profile p).signedMass index' sign' k = p.signedMass index sign k := by
  unfold Profile.signedMass
  congr 2
  have he := (Finsupp.embDomain.addMonoidHom (E.auxiliary k)).map_sub (p.auxiliary k) (p.guards.auxiliary k)
  change (p.auxiliary k - p.guards.auxiliary k).embDomain (E.auxiliary k) =
    (p.auxiliary k).embDomain (E.auxiliary k) - (p.guards.auxiliary k).embDomain (E.auxiliary k) at he
  change DyadicColumns.auxiliaryTransfer (index' k) (sign' k)
    ((p.auxiliary k).embDomain (E.auxiliary k) - (p.guards.auxiliary k).embDomain (E.auxiliary k)) = _
  rw [← he, E.transfer index sign index' sign' hi hs]

include hi hs in
/-- A signed split on the preview remains a split on all permanent sites. -/
theorem split {p u v : Profile J G H} {M : ℕ} (s : SplitAt index sign p u v M) :
    SplitAt index' sign' (E.profile p) (E.profile u) (E.profile v) M := by
  refine ⟨?_,?_,fun k => (E.signedMass index sign index' sign' hi hs u k).trans (s.masses_left k),
    fun k => (E.signedMass index sign index' sign' hi hs v k).trans (s.masses_right k),
    s.heights,s.old_regular,?_,s.reserved⟩
  · rintro (⟨c⟩ | ⟨k,n⟩ | ⟨k,n⟩ | ⟨j⟩)
    · exact s.effective (.centre c)
    · exact s.effective (.plus k n)
    · exact s.effective (.minus k n)
    · rcases E.supplement_cases j with ⟨i,rfl⟩ | h
      · simpa only [E.supplement_value] using s.effective (.other i)
      · simp [h]
  · rintro (⟨c⟩ | ⟨k,n⟩ | ⟨k,n⟩ | ⟨j⟩)
    · exact s.values_sum (.centre c)
    · exact s.values_sum (.plus k n)
    · exact s.values_sum (.minus k n)
    · rcases E.supplement_cases j with ⟨i,rfl⟩ | h
      · simpa only [E.supplement_value] using s.values_sum (.other i)
      · simp [h]
  · intro j
    rcases E.supplement_cases j with ⟨i,rfl⟩ | h
    · simpa only [E.supplement_value,E.supplement_channel] using s.supplementary i
    · simp [h]

def columns (c : Columns J) : Columns J' :=
  (c.1,c.2.1,fun k => (c.2.2 k).embDomain (E.auxiliary k))

include hi hs in
theorem translate (p : Profile J G H) (c : Columns J) :
    (E.profile p).translate index' sign' (E.columns c) =
      E.profile (p.translate index sign c) := by
  apply Profile.ext
  · rfl
  · funext k
    simp [profile,columns,Profile.translate,Profile.addColumns,E.transfer index sign index' sign' hi hs]
  · rfl
  · funext k
    simp [profile,columns,Profile.translate,Profile.addColumns]
  · rfl
  · rfl

variable (prime : (Σ k, J k) ↪ GuardSupport.PrimeIndex) (positive : (k : Bool) → J k → Bool)
    (prime' : (Σ k, J' k) ↪ GuardSupport.PrimeIndex) (positive' : (k : Bool) → J' k → Bool)
    (hp : ∀ k j, prime' ⟨k,E.auxiliary k j⟩ = prime ⟨k,j⟩)
    (hpos : ∀ k j, positive' k (E.auxiliary k j) = positive k j)

include hi hp hpos in
/-- A word supported on preview labels acts in exactly the same way after
extending to all permanent indices. In particular no later auxiliary prime
can accidentally receive a nonzero coefficient. -/
theorem columnsOfRaw_eq (e : RawColumn →₀ ℤ)
    (he : ∀ c ∈ e.support, c ∈ Set.range (basisLabel prime index positive)) :
    columnsOfRaw prime' index' positive' e = E.columns (columnsOfRaw prime index positive e) := by
  classical
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  funext k
  ext j
  change e (.auxiliary (prime' ⟨k,j⟩) k (index' k j) (positive' k j)) =
    ((columnsOfRaw prime index positive e).2.2 k).embDomain (E.auxiliary k) j
  by_cases h : j ∈ Set.range (E.auxiliary k)
  · obtain ⟨z,rfl⟩ := h
    rw [Finsupp.embDomain_apply_self, hp, hi, hpos]
    rfl
  · rw [Finsupp.embDomain_of_notMem_range _ _ _ h]
    by_contra hn
    obtain ⟨g,hg⟩ := he _ (Finsupp.mem_support_iff.mpr hn)
    rcases g with (⟨_,_⟩ | ⟨_,_⟩) | ⟨l,z⟩
    · cases hg
    · cases hg
    · change RawColumn.auxiliary (prime ⟨l,z⟩) l _ _ = .auxiliary (prime' ⟨k,j⟩) k _ _ at hg
      have eq := RawColumn.auxiliary.inj hg
      have hl : l = k := eq.2.1
      subst l
      have hprime := prime'.injective ((hp k z).trans eq.1)
      exact h ⟨z,eq_of_heq (Sigma.mk.inj_iff.mp hprime).2⟩

include hi hs hp hpos in
theorem translate_raw (p : Profile J G H) (e : RawColumn →₀ ℤ)
    (he : ∀ c ∈ e.support, c ∈ Set.range (basisLabel prime index positive)) :
    (E.profile p).translate index' sign' (columnsOfRaw prime' index' positive' e) =
      E.profile (p.translate index sign (columnsOfRaw prime index positive e)) := by
  rw [E.columnsOfRaw_eq index index' hi prime positive prime' positive' hp hpos e he]
  exact E.translate index sign index' sign' hi hs p _

end ProfileEmbedding
end UnconditionalCounterexample.DyadicDeviations
