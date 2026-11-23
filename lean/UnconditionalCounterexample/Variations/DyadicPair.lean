import UnconditionalCounterexample.Variations.DyadicProfiles
import UnconditionalCounterexample.Variations.DyadicRealization

/-!
# The dyadic pair conditional on realization

The supplementary coordinates include all guards, auxiliary sites and other
horizontals. They vanish on the two chosen elements and on every common
divisor of them. No principal-profile equation is assumed for the regular
coordinates alone when the supplementary coordinates are nonzero.
-/

namespace UnconditionalCounterexample.DyadicProfiles

inductive Site (E : Type*) where
  | centre (k : Bool)
  | plus (k : Bool) (n : ℕ)
  | minus (k : Bool) (n : ℕ)
  | other (i : E)

variable {E R : Type*}

/-- The coordinate map omits the cutoff used to compute a signed sum. -/
def Profile.values (p : Profile) (extra : E → ℕ) : Site E → ℕ
  | .centre k => p.height k
  | .plus k n => p.plus k n
  | .minus k n => p.minus k n
  | .other i => extra i

theorem Profile.values_le_iff {p q : Profile} {a b : E → ℕ} :
    p.values a ≤ q.values b ↔ p.Below q ∧ a ≤ b := by
  constructor
  · intro h
    exact ⟨⟨fun k => h (.centre k), fun k n => h (.plus k n), fun k n => h (.minus k n)⟩,
      fun i => h (.other i)⟩
  · rintro ⟨⟨hc, hp, hm⟩, ho⟩ i
    cases i with
    | centre k => exact hc k
    | plus k n => exact hp k n
    | minus k n => exact hm k n
    | other i => exact ho i

/-- The two coordinates of the balanced column at site `(0,n)`. -/
def balancedColumn (n : ℕ) : Profile where
  height _ := 0
  plus k i := balancedEntry false n k i
  minus k i := balancedEntry false n k i
  cutoff := n + 1
  plus_stable _ i hi := by simp [balancedEntry, show i ≠ n by omega]
  minus_stable _ i hi := by simp [balancedEntry, show i ≠ n by omega]

theorem balancedColumn_massEquations (n : ℕ) : (balancedColumn n).MassEquations := by
  intro k
  simp [Profile.signedMass, mass_eq_sum, Profile.difference, Profile.tailDifference, balancedColumn]

variable [CommRing R] [IsDomain R]

/-- Construction inputs for the pair. Realization is only required for pure
effective profiles (the supplementary coordinates are all zero). -/
structure Realization (R E : Type*) [CommRing R] [IsDomain R] where
  regular : R → Profile
  extra : R → E → ℕ
  mul_values : ∀ a b : R, a ≠ 0 → b ≠ 0 →
    (regular (a*b)).values (extra (a*b)) =
      (regular a).values (extra a) + (regular b).values (extra b)
  dvd_iff : ∀ a b : R, a ≠ 0 → b ≠ 0 → (a ∣ b ↔
    (regular a).values (extra a) ≤ (regular b).values (extra b))
  mass_of_pure : ∀ a : R, a ≠ 0 → extra a = 0 → (regular a).MassEquations
  realize : ∀ p : Profile, p.MassEquations →
    ∃ a : R, a ≠ 0 ∧ (regular a).values (extra a) = p.values 0

namespace Realization

variable (D : Realization R E)

/-- Values of a realized element at every site. -/
def values (x : R) : Site E → ℕ := (D.regular x).values (D.extra x)

theorem values_one : D.values 1 = 0 := by
  funext i
  have h := congrFun (D.mul_values 1 1 one_ne_zero one_ne_zero) i
  simp only [one_mul, Pi.add_apply] at h
  change (D.regular 1).values (D.extra 1) i = 0
  omega

/-- The elements with the early positive entries 2 at index 0 and 4 at
index 1, respectively. -/
noncomputable def pairEntry (second : Bool) : R :=
  (D.realize (witness second) (witness_massEquations second)).choose

theorem pairEntry_spec (second : Bool) : D.pairEntry second ≠ 0 ∧
    D.values (D.pairEntry second) = (witness second).values 0 :=
  (D.realize (witness second) (witness_massEquations second)).choose_spec

/-- Every divisor of both displayed entries extends by a nonunit in the
actual ring. The extending column is realized at an index beyond the
four regular supports of the divisor. -/
theorem pair_extension {e : R} (hex : e ∣ D.pairEntry false) (hey : e ∣ D.pairEntry true) :
    ∃ u : R, ¬ IsUnit u ∧ e * u ∣ D.pairEntry false ∧ e * u ∣ D.pairEntry true := by
  choose B hB hval using fun i => D.realize (balancedColumn i) (balancedColumn_massEquations i)
  apply Dyadic.exists_common_divisor_extension_of_profiles D.values D.values_one D.mul_values D.dvd_iff
    B hB _ (D.pairEntry_spec false).1 (D.pairEntry_spec true).1 _ hex hey
  · intro n h
    have hi := h (Site.plus false n)
    change (D.regular (B n)).values (D.extra (B n)) (.plus false n) ≤ 0 at hi
    rw [hval n] at hi
    simp [Profile.values, balancedColumn, balancedEntry] at hi
  · intro d hd hdx hdy
    rw [(D.pairEntry_spec false).2] at hdx
    rw [(D.pairEntry_spec true).2] at hdy
    obtain ⟨hpx, hdextra⟩ := Profile.values_le_iff.mp hdx
    obtain ⟨hpy, _⟩ := Profile.values_le_iff.mp hdy
    have hpure : D.extra d = 0 := le_antisymm hdextra (fun i => Nat.zero_le _)
    obtain ⟨n, _, hx, hy, _⟩ := common_profile_balanced_extension (D.regular d)
      (D.mass_of_pure d hd hpure) hpx hpy
    have hsum : D.values d + D.values (B n) =
        ((D.regular d).addBalanced false n).values 0 := by
      change (D.regular d).values (D.extra d) + (D.regular (B n)).values (D.extra (B n)) = _
      rw [hpure, hval n]
      funext i
      cases i <;> simp [Profile.values, Profile.addBalanced, balancedColumn]
    refine ⟨n, ?_⟩
    rw [hsum, (D.pairEntry_spec false).2, (D.pairEntry_spec true).2]
    exact ⟨Profile.values_le_iff.mpr ⟨hx, le_rfl⟩, Profile.values_le_iff.mpr ⟨hy, le_rfl⟩⟩

/-- The same realized pair witnesses failure of a pair MCD and hence failure
of strong atomicity and weak ACCP. -/
theorem pair_obstruction [DecidableEq R] :
    (¬ ∃ d : R, Factorization.IsMaximalCommonDivisor {D.pairEntry false, D.pairEntry true} d) ∧
      ¬ Factorization.IsStronglyAtomicDomain R ∧ ¬ Factorization.IsWeakACCP R :=
  Dyadic.obstruction_of_common_divisor_extensions (D.pairEntry_spec false).1
    (D.pairEntry_spec true).1 (fun _ => D.pair_extension)

end Realization

end UnconditionalCounterexample.DyadicProfiles
