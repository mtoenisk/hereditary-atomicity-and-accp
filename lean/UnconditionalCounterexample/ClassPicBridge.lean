import Mathlib.RingTheory.PicardGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Actual class and Picard groups from fractional-ideal profiles

For an arbitrary domain and a chosen fraction field, a profile equivalence on
actual invertible fractional ideals presents the actual class group as the
profile group modulo the literal image of nonzero principal fractional ideals.
The Picard presentation follows from mathlib's domain equivalence. There is no
Noetherian or Dedekind hypothesis and no replacement of the actual principal
image by an unverified relation subgroup.
-/

namespace UnconditionalCounterexample.ClassPicBridge

open scoped nonZeroDivisors

noncomputable section
universe u v w
variable (D : Type u) [CommRing D] [IsDomain D]
variable (K : Type v) [Field K] [Algebra D K] [IsFractionRing D K]
variable {G : Type w} [AddCommGroup G]

/-- The profile of the actual invertible principal fractional ideal generated
by a nonzero fraction. The source uses the additive form of K's unit group. -/
def principalProfileHom
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G) :
    Additive Kˣ →+ G :=
  e.toAddMonoidHom.comp (toPrincipalIdeal D K).toAdditive

/-- The actual subgroup of principal-ideal profiles, as the image of Kˣ. -/
def principalProfiles
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G) :
    AddSubgroup G := (principalProfileHom D K e).range

omit [IsDomain D] in
@[simp] theorem principalProfileHom_apply
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G) (a : Kˣ) :
    principalProfileHom D K e (Additive.ofMul a) =
      e (Additive.ofMul (toPrincipalIdeal D K a)) := rfl

omit [IsDomain D] in
/-- This subgroup contains precisely profiles of actual nonzero principal
fractional ideals, not an independently chosen relation subgroup. -/
theorem mem_principalProfiles_iff
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G) (g : G) :
    g ∈ principalProfiles D K e ↔
      ∃ a : Kˣ, e (Additive.ofMul (toPrincipalIdeal D K a)) = g := Iff.rfl

/-- An actual invertible-fractional-ideal profile equivalence presents the
actual ideal class group by its actual principal-profile subgroup. -/
def classGroupEquivQuotient
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G) :
    Additive (ClassGroup D) ≃+ G ⧸ principalProfiles D K e :=
  (ClassGroup.equiv K).toAdditive.trans
    (QuotientAddGroup.congr ((toPrincipalIdeal D K).range.toAddSubgroup)
      (principalProfiles D K e) e (by
        exact (AddMonoidHom.range_comp e.toAddMonoidHom (toPrincipalIdeal D K).toAdditive).symm))

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem classGroupEquivQuotient_mk
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G)
    (I : (FractionalIdeal (nonZeroDivisors D) K)ˣ) :
    classGroupEquivQuotient D K e (Additive.ofMul (ClassGroup.mk K I)) =
      QuotientAddGroup.mk (e (Additive.ofMul I)) := by
  have h : ClassGroup.equiv K (ClassGroup.mk K I) = QuotientGroup.mk I := by
    rw [ClassGroup.equiv_mk K K, FractionalIdeal.canonicalEquiv_self]
    rfl
  change (QuotientAddGroup.congr ((toPrincipalIdeal D K).range.toAddSubgroup)
    (principalProfiles D K e) e
      (by exact (AddMonoidHom.range_comp e.toAddMonoidHom
        (toPrincipalIdeal D K).toAdditive).symm))
    ((ClassGroup.equiv K).toAdditive (Additive.ofMul (ClassGroup.mk K I))) = _
  have h' : (ClassGroup.equiv K).toAdditive (Additive.ofMul (ClassGroup.mk K I)) =
      Additive.ofMul (QuotientGroup.mk I :
        (FractionalIdeal (nonZeroDivisors D) K)ˣ ⧸ (toPrincipalIdeal D K).range) :=
    congrArg Additive.ofMul h
  rw [h']
  rfl

/-- The same presentation for mathlib's actual Picard group of the domain. -/
def picardEquivQuotient
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G) :
    Additive (CommRing.Pic D) ≃+ G ⧸ principalProfiles D K e :=
  (ClassGroup.equivPic D).symm.toAdditive.trans (classGroupEquivQuotient D K e)

/-- A separately computed relation subgroup may be used after proving its
literal equality with the actual principal-profile image. -/
def classGroupEquivQuotientOfEq
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G)
    (P : AddSubgroup G) (hP : principalProfiles D K e = P) :
    Additive (ClassGroup D) ≃+ G ⧸ P :=
  (classGroupEquivQuotient D K e).trans (QuotientAddGroup.quotientAddEquivOfEq hP)

def picardEquivQuotientOfEq
    (e : Additive ((FractionalIdeal (nonZeroDivisors D) K)ˣ) ≃+ G)
    (P : AddSubgroup G) (hP : principalProfiles D K e = P) :
    Additive (CommRing.Pic D) ≃+ G ⧸ P :=
  (picardEquivQuotient D K e).trans (QuotientAddGroup.quotientAddEquivOfEq hP)

end
end UnconditionalCounterexample.ClassPicBridge
