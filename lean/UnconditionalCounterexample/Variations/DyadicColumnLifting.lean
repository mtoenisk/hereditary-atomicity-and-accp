import UnconditionalCounterexample.Variations.DyadicDeviations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Realization from individual dyadic generators

A raw rational function acts on every profile by one R, Q or S column.
Multiplication and inversion realize arbitrary finite integral column
combinations. Once the guards and horizontals of a target have been lifted,
the two mass equations therefore suffice to realize that target.
-/

noncomputable section

namespace UnconditionalCounterexample.DyadicDeviations

variable {J : Bool → Type*} {G H K : Type*}

/-- Signed exponents on balanced, adjacent and auxiliary columns, in both channels. -/
abbrev Columns (J : Bool → Type*) :=
  (Bool → ℕ →₀ ℤ) × (Bool → ℕ →₀ ℤ) × ((k : Bool) → J k →₀ ℤ)

variable (index : (k : Bool) → J k → ℕ) (sign : (k : Bool) → J k → ℤ)

/-- Translation by the indicated integral column combination. -/
def Profile.translate (p : Profile J G H) (e : Columns J) : Profile J G H :=
  p.addColumns index sign e.1 e.2.1 e.2.2

@[simp] theorem Profile.translate_zero (p : Profile J G H) : p.translate index sign 0 = p := by
  apply Profile.ext <;> simp [Profile.translate, Profile.addColumns]

@[simp] theorem Profile.translate_add (p : Profile J G H) (a b : Columns J) :
    (p.translate index sign a).translate index sign b = p.translate index sign (a + b) := by
  apply Profile.ext <;> simp [Profile.translate, Profile.addColumns] <;> funext k <;> abel

variable [Group K]

/-- Columns that are realized by multiplication with a fixed group element.
For rational functions one takes `K` to be the group of nonzero functions. -/
def liftableColumns (v : K → Profile J G H) : AddSubgroup (Columns J) where
  carrier := {e | ∃ b : K, ∀ x, v (x * b) = (v x).translate index sign e}
  zero_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨w, hw⟩
    exact ⟨u*w, fun x => by rw [← mul_assoc, hw, hu, Profile.translate_add]⟩
  neg_mem' := by
    rintro a ⟨u, hu⟩
    refine ⟨u⁻¹, fun x => ?_⟩
    have h := congrArg (fun p : Profile J G H => p.translate index sign (-a)) (hu (x*u⁻¹))
    simpa using h.symm

private def channelHom {A : Bool → Type*} [(k : Bool) → AddCommGroup (A k)]
    (k : Bool) : A k →+ (j : Bool) → A j where
  toFun := Pi.single k
  map_zero' := Pi.single_zero _
  map_add' := Pi.single_add _

/-- An additive homomorphism on finite signed data in the two channels lands in a
subgroup if it does so on every one-entry column. -/
private theorem mem_of_channel_singles {A : Type*} [AddCommGroup A] {I : Bool → Type*}
    (S : AddSubgroup A) (f : ((k : Bool) → I k →₀ ℤ) →+ A)
    (h : ∀ k i, f (Pi.single k (Finsupp.single i 1)) ∈ S)
    (w : (k : Bool) → I k →₀ ℤ) : f w ∈ S := by
  classical
  rw [← Finset.univ_sum_single w, map_sum]
  apply S.sum_mem
  intro k _
  let g := f.comp (channelHom (A := fun j => I j →₀ ℤ) k)
  change g (w k) ∈ S
  generalize w k = z
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add _ _ hu hv => rw [map_add]; exact S.add_mem hu hv
  | single i m =>
    let s := g.comp (Finsupp.singleAddHom i)
    have hs : s 1 ∈ S := h k i
    change s m ∈ S
    simpa using (show s (m • (1 : ℤ)) ∈ S by rw [map_zsmul]; exact S.zsmul_mem hs m)

private def balancedHom : (Bool → ℕ →₀ ℤ) →+ Columns J := AddMonoidHom.inl _ _

private def adjacentHom : (Bool → ℕ →₀ ℤ) →+ Columns J :=
  (AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _)

private def auxiliaryHom : ((k : Bool) → J k →₀ ℤ) →+ Columns J :=
  (AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _)

/-- It suffices to produce one group element for each individual R, Q and S.
This obtains negative exponents by inversion and all multi-column profiles by
finite multiplication. -/
theorem exists_column_multiplier (v : K → Profile J G H)
    (hR : ∀ k n, ∃ u : K, ∀ x, v (x*u) =
      (v x).addColumns index sign (Pi.single k (Finsupp.single n 1)) 0 0)
    (hQ : ∀ k n, ∃ u : K, ∀ x, v (x*u) =
      (v x).addColumns index sign 0 (Pi.single k (Finsupp.single n 1)) 0)
    (hS : ∀ k j, ∃ u : K, ∀ x, v (x*u) =
      (v x).addColumns index sign 0 0 (Pi.single k (Finsupp.single j 1)))
    (r q : Bool → ℕ →₀ ℤ) (s : (k : Bool) → J k →₀ ℤ) :
    ∃ u : K, ∀ x, v (x*u) = (v x).addColumns index sign r q s := by
  let L := liftableColumns index sign v
  have hr := mem_of_channel_singles L (balancedHom (J := J)) (fun k n => hR k n) r
  have hq := mem_of_channel_singles L (adjacentHom (J := J)) (fun k n => hQ k n) q
  have hs := mem_of_channel_singles L (auxiliaryHom (J := J)) (fun k n => hS k n) s
  have h := L.add_mem (L.add_mem hr hq) hs
  change (r, q, s) ∈ L
  simpa [balancedHom, adjacentHom, auxiliaryHom] using h

/-- A calibrated lift of the guard and horizontal coordinates of a compatible
signed profile extends to a lift of all its coordinates. -/
theorem exists_of_calibrated_columns (v : K → Profile J G H)
    (heq : ∀ x, (v x).MassEquations index sign)
    (hR : ∀ k n, ∃ u : K, ∀ x, v (x*u) =
      (v x).addColumns index sign (Pi.single k (Finsupp.single n 1)) 0 0)
    (hQ : ∀ k n, ∃ u : K, ∀ x, v (x*u) =
      (v x).addColumns index sign 0 (Pi.single k (Finsupp.single n 1)) 0)
    (hS : ∀ k j, ∃ u : K, ∀ x, v (x*u) =
      (v x).addColumns index sign 0 0 (Pi.single k (Finsupp.single j 1)))
    (t : Profile J G H) (ht : t.MassEquations index sign)
    (hbase : ∃ b : K, (v b).height = t.height ∧ (v b).guards = t.guards ∧
      (v b).horizontal = t.horizontal) : ∃ a : K, v a = t := by
  obtain ⟨b, hh, hg, hhor⟩ := hbase
  obtain ⟨q, hq⟩ :=
    (v b).exists_columns_of_massEquations t index sign (heq b) ht hh hg hhor
  obtain ⟨u, hu⟩ := exists_column_multiplier index sign v hR hQ hS
    (fun k => t.minusDeviation k - (v b).minusDeviation k) q
    (fun k => t.auxiliary k - (v b).auxiliary k)
  exact ⟨b*u, (hu b).trans hq⟩

/-- The actual field product translates its base profile by the indicated
combination of columns. Only labels with nonzero exponent in this word
require a singleton valuation identity. -/
theorem signed_word_translates {A L : Type*} [CommGroup L] (W : A → L)
    (columns : (A →₀ ℤ) →+ Columns J) (v : L → Profile J G H) (e : A →₀ ℤ)
    (hsingle : ∀ g ∈ e.support, ∀ x, v (x * W g) =
      (v x).translate index sign (columns (Finsupp.single g 1))) (x : L) :
    v (x * e.prod (fun g z => W g ^ z)) = (v x).translate index sign (columns e) := by
  classical
  let prod (a : A →₀ ℤ) := a.prod (fun g z => W g ^ z)
  have hadd (a b) : prod (a+b) = prod a * prod b :=
    Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add ..)
  let S : AddSubgroup (A →₀ ℤ) := {
    carrier := {a | ∀ y, v (y * prod a) = (v y).translate index sign (columns a)}
    zero_mem' := by simp [prod]
    add_mem' := by
      intro a b ha hb y
      rw [hadd, ← mul_assoc, hb, ha, Profile.translate_add, map_add]
    neg_mem' := by
      intro a ha y
      have he := ha (y * prod (-a))
      change v (y * prod (-a) * prod a) = _ at he
      rw [mul_assoc, ← hadd, neg_add_cancel, show prod 0 = 1 by simp [prod], mul_one] at he
      have hc := congrArg (fun p : Profile J G H => p.translate index sign (-(columns a))) he
      simpa using hc.symm }
  have mem : e ∈ S := by
    rw [← e.sum_single]
    apply S.sum_mem
    intro g hg
    change Finsupp.single g (e g) ∈ S
    have hu : Finsupp.single g 1 ∈ S := fun y => by simpa [prod] using hsingle g hg y
    have he : (Finsupp.singleAddHom g) (e g • (1 : ℤ)) ∈ S := by
      rw [map_zsmul]
      exact S.zsmul_mem hu (e g)
    simpa using he
  exact mem x

end UnconditionalCounterexample.DyadicDeviations
