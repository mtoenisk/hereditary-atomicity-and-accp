import UnconditionalCounterexample.Variations.DyadicProfileExtension
import UnconditionalCounterexample.Variations.DyadicPrefixCoarse
import UnconditionalCounterexample.Variations.DyadicGeneratorColumns
import UnconditionalCounterexample.Variations.DyadicSignedField

/-!
# The actual inclusion of a finite prefix's site indices

Assigned auxiliary and guard primes keep their roles forever. Frozen monic
irreducibles stay retained. Thus the finite preview's three supplementary
index sets embed into the permanent coordinates of the calibrated domain.
-/

noncomputable section
namespace UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
open GuardSupport RecursivePrefix Univariate DyadicDeviations

variable (a : Policy) (n : ℕ)

abbrev oldAux := PrefixProfile.Aux ((driver a).assigned n) ((driver a).state n).role
abbrev oldLone := PrefixProfile.Lone ((driver a).assigned n) ((driver a).state n).role
abbrev oldHorizontal := PrefixProfile.Known ((driver a).state n).frozen
abbrev oldIndex := PrefixProfile.index ((driver a).assigned n) ((driver a).state n).role
abbrev oldSign := PrefixProfile.sign ((driver a).assigned n) ((driver a).state n).role
abbrev oldPositive := PrefixProfile.positive ((driver a).assigned n) ((driver a).state n).role
abbrev oldPrime := PrefixProfile.prime ((driver a).assigned n) ((driver a).state n).role
abbrev oldSigned := PrefixProfile.signed ((driver a).assigned n) ((driver a).state n).role
  (table (driver a).requirements n) ((driver a).state n).frozen

def includeAux (k : Bool) : oldAux a n k ↪ Aux a k where
  toFun j := {
    prime := j.val
    index := oldIndex a n k j
    positive := oldPositive a n k j
    role_eq := by
      obtain ⟨i,e,hr⟩ := j.property.2
      rw [← (driver a).role_eq_permanent j.val j.property.1,hr]
      cases e <;> simp [oldIndex,oldPositive,PrefixProfile.index,PrefixProfile.positive,
        Calibration.auxWeight,Calibration.auxSign,hr,FibreRole.index,FibreRole.sign] }
  inj' := fun _ _ h => Subtype.ext (congrArg Aux.prime h)

def prefixEmbedding : ProfileEmbedding (oldAux a n) (Aux a) (oldLone a n) (Lone a)
    (oldHorizontal a n) (Horiz a) where
  auxiliary := includeAux a n
  lone := {
    toFun := fun j => ⟨j.val,((driver a).role_eq_permanent j.val j.property.1).symm.trans j.property.2⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun z : Lone a => z.val) h) }
  horizontal := {
    toFun := fun j => ⟨j.val,by
      obtain ⟨t,_,hf⟩ := (driver a).frozen_iff.mp j.property.1
      exact (driver a).retained t _ hf,j.property.2⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun z : Horiz a => z.val) h) }

theorem includeAux_of_assigned (k : Bool) (j : Aux a k) (hj : j.prime ∈ (driver a).assigned n) :
    ∃ i, includeAux a n k i = j := by
  let i : oldAux a n k := ⟨j.prime,hj,j.index,j.positive,
    ((driver a).role_eq_permanent j.prime hj).trans j.role_eq⟩
  exact ⟨i,aux_prime_injective a k rfl⟩

theorem includeLone_of_assigned (j : Lone a) (hj : j.val ∈ (driver a).assigned n) :
    ∃ i, (prefixEmbedding a n).lone i = j := by
  let i : oldLone a n := ⟨j.val,hj,((driver a).role_eq_permanent j.val hj).trans j.property⟩
  exact ⟨i,Subtype.ext rfl⟩

theorem includeHorizontal_of_frozen (j : Horiz a) (hj : j.val.val ∈ ((driver a).state n).frozen) :
    ∃ i, (prefixEmbedding a n).horizontal i = j :=
  ⟨⟨j.val,hj,j.property.2⟩,Subtype.ext rfl⟩

theorem includeAux_sign (k : Bool) (j : oldAux a n k) :
    auxSign (auxPositive a) k (includeAux a n k j) = oldSign a n k j :=
  (PrefixProfile.sign_eq _ _ k j).symm

theorem extend_split {p u v : Profile (oldAux a n) (oldLone a n) (oldHorizontal a n)} {M : ℕ}
    (split : SplitAt (oldIndex a n) (oldSign a n) p u v M) :
    SplitAt (auxIndex a) (auxSign (auxPositive a)) ((prefixEmbedding a n).profile p)
      ((prefixEmbedding a n).profile u) ((prefixEmbedding a n).profile v) M :=
  (prefixEmbedding a n).split _ _ _ _ (fun _ _ => rfl) (includeAux_sign a n) split

theorem extend_word (p : Profile (oldAux a n) (oldLone a n) (oldHorizontal a n)) (e : RawColumn →₀ ℤ)
    (hs : ∀ c ∈ e.support, c ∈ Set.range (basisLabel (oldPrime a n) (oldIndex a n) (oldPositive a n))) :
    ((prefixEmbedding a n).profile p).translate (auxIndex a) (auxSign (auxPositive a))
        (columnsOfRaw (auxiliaryPrime a) (auxIndex a) (auxPositive a) e) =
      (prefixEmbedding a n).profile
        (p.translate (oldIndex a n) (oldSign a n) (columnsOfRaw (oldPrime a n) (oldIndex a n) (oldPositive a n) e)) :=
  (prefixEmbedding a n).translate_raw _ _ _ _ (fun _ _ => rfl) (includeAux_sign a n) _ _ _ _
    (fun _ _ => rfl) (fun _ _ => rfl) _ _ hs

end UnconditionalCounterexample.Variations.DyadicLedger.Calibrated
