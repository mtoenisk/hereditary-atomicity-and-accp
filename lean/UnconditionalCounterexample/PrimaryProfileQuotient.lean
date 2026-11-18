import UnconditionalCounterexample.PicardProfiles
import UnconditionalCounterexample.NormalizedWords
import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic.Ring

noncomputable section
namespace UnconditionalCounterexample.PrimaryProfileQuotient
open PicardProfiles NormalizedWords

abbrev FinitePrimary := ℕ →₀ ℤ

private theorem even_injective : Function.Injective (fun n : ℕ => 2 * n) := by
  intro a b h
  dsimp only at h
  omega
private theorem odd_injective : Function.Injective (fun n : ℕ => 2 * n + 1) := by
  intro a b h
  dsimp only at h
  omega

def even : FinitePrimary →+ FinitePrimary := Finsupp.mapDomain.addMonoidHom (fun n => 2 * n)
def odd : FinitePrimary →+ FinitePrimary := Finsupp.mapDomain.addMonoidHom (fun n => 2 * n + 1)
def shift : FinitePrimary →+ FinitePrimary := Finsupp.mapDomain.addMonoidHom (fun n => n + 1)
def evenPart : FinitePrimary →+ FinitePrimary := Finsupp.comapDomain.addMonoidHom even_injective
def oddPart : FinitePrimary →+ FinitePrimary := Finsupp.comapDomain.addMonoidHom odd_injective

@[simp] theorem even_even (a : FinitePrimary) (n : ℕ) : even a (2 * n) = a n :=
  Finsupp.mapDomain_apply_of_injective even_injective a n
@[simp] theorem even_odd (a : FinitePrimary) (n : ℕ) : even a (2 * n + 1) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩
  dsimp only at hj
  omega
@[simp] theorem odd_odd (a : FinitePrimary) (n : ℕ) : odd a (2 * n + 1) = a n :=
  Finsupp.mapDomain_apply_of_injective odd_injective a n
@[simp] theorem odd_even (a : FinitePrimary) (n : ℕ) : odd a (2 * n) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩
  dsimp only at hj
  omega
@[simp] theorem shift_zero (a : FinitePrimary) : shift a 0 = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩
  dsimp only at hj
  omega
@[simp] theorem shift_succ (a : FinitePrimary) (n : ℕ) : shift a (n + 1) = a n :=
  Finsupp.mapDomain_apply_of_injective (by intro i j h; dsimp only at h; omega) a n
@[simp] theorem evenPart_apply (a : FinitePrimary) (n : ℕ) : evenPart a n = a (2 * n) := rfl
@[simp] theorem oddPart_apply (a : FinitePrimary) (n : ℕ) : oddPart a n = a (2 * n + 1) := rfl

/-- The primary column sum of the signed q word. -/
def qVector : FinitePrimary →+ FinitePrimary := 2 • even + odd + 2 • even.comp shift

@[simp] theorem qVector_zero (u : FinitePrimary) : qVector u 0 = 2 * u 0 := by
  change (2 • even u + odd u + 2 • even (shift u)) 0 = _
  have he : even u 0 = u 0 := even_even u 0
  have ho : odd u 0 = 0 := odd_even u 0
  have hs : even (shift u) 0 = 0 := (even_even (shift u) 0).trans (shift_zero u)
  simp [he, ho, hs, nsmul_eq_mul]

@[simp] theorem qVector_odd (u : FinitePrimary) (n : ℕ) : qVector u (2 * n + 1) = u n := by
  change (2 • even u + odd u + 2 • even (shift u)) (2 * n + 1) = _
  simp

@[simp] theorem qVector_even_succ (u : FinitePrimary) (n : ℕ) :
    qVector u (2 * n + 2) = 2 * u (n + 1) + 2 * u n := by
  have heq : 2 * n + 2 = 2 * (n + 1) := by omega
  change (2 • even u + odd u + 2 • even (shift u)) (2 * n + 2) = _
  rw [heq]
  simp [nsmul_eq_mul]

/-- Subtracting q columns clears every odd entry and leaves this even tuple. -/
def residual : FinitePrimary →+ FinitePrimary := evenPart - 2 • oddPart - 2 • shift.comp oddPart

theorem decomposition (a : FinitePrimary) : a = even (residual a) + qVector (oddPart a) := by
  apply Finsupp.ext
  intro j
  obtain ⟨n, hj | hj⟩ : ∃ n : ℕ, j = 2 * n ∨ j = 2 * n + 1 := ⟨j / 2, by omega⟩
  · subst j
    cases n with
    | zero =>
      change a 0 = even (residual a) 0 + qVector (oddPart a) 0
      rw [show even (residual a) 0 = residual a 0 from even_even _ 0, qVector_zero]
      change a 0 = (evenPart a - 2 • oddPart a - 2 • shift (oddPart a)) 0 + 2 * oddPart a 0
      simp [nsmul_eq_mul]
    | succ n =>
      change a (2 * (n + 1)) = even (residual a) (2 * (n + 1)) + qVector (oddPart a) (2 * (n + 1))
      rw [even_even, show 2 * (n + 1) = 2 * n + 2 by omega, qVector_even_succ]
      change a (2 * n + 2) =
        (evenPart a - 2 • oddPart a - 2 • shift (oddPart a)) (n + 1) + _
      simp [nsmul_eq_mul, Nat.mul_add]
  · subst j
    simp

theorem represents_columns (s u : FinitePrimary) : Represents s u (3 • even s + qVector u) := by
  constructor
  · change (3 • even s + qVector u) 0 = _
    have he : even s 0 = s 0 := even_even _ 0
    simp [he, nsmul_eq_mul]
  · intro n
    change (3 • even s + qVector u) (2 * n + 1) = _
    simp
  · intro n
    change (3 • even s + qVector u) (2 * n + 2) = _
    have he : even s (2 * n + 2) = s (n + 1) := by
      rw [show 2 * n + 2 = 2 * (n + 1) by omega, even_even]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, qVector_even_succ, he, nsmul_eq_mul]
    ring

/-- A principal relation supported on even coordinates has no q exponents. -/
theorem represents_even_iff (a : FinitePrimary) :
    (∃ s u : FinitePrimary, Represents s u (even a)) ↔ ∃ s : FinitePrimary, a = 3 • s := by
  constructor
  · rintro ⟨s, u, h⟩
    have hu : u = 0 := by
      apply Finsupp.ext
      intro n
      simpa only [even_odd, Finsupp.zero_apply] using (h.odd n).symm
    refine ⟨s, ?_⟩
    apply Finsupp.ext
    intro n
    cases n with
    | zero =>
      have hh := h.initial
      have he : even a 0 = a 0 := even_even _ 0
      simpa [he, hu, nsmul_eq_mul] using hh
    | succ n =>
      have hh := h.even_succ n
      have he : even a (2 * n + 2) = a (n + 1) := by
        rw [show 2 * n + 2 = 2 * (n + 1) by omega, even_even]
      simpa [he, hu, nsmul_eq_mul] using hh
  · rintro ⟨s, rfl⟩
    refine ⟨s, 0, ?_⟩
    simpa using represents_columns s 0

/-- Coefficientwise reduction of the free even-coordinate group modulo three. -/
def modThree : FinitePrimary →+ (ℕ →₀ ZMod 3) :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod 3))

theorem modThree_surjective : Function.Surjective modThree :=
  Finsupp.mapRange_surjective _ (map_zero (Int.castAddHom (ZMod 3))) ZMod.intCast_surjective

theorem modThree_eq_zero_iff (a : FinitePrimary) :
    modThree a = 0 ↔ ∃ s : FinitePrimary, a = 3 • s := by
  constructor
  · intro ha
    have ha' : a ∈ Set.range (Finsupp.mapRange (fun z : ℤ => 3 * z) (by norm_num)) := by
      rw [Finsupp.range_mapRange]
      intro j
      have hj : (a j : ZMod 3) = 0 := congrArg (fun x : ℕ →₀ ZMod 3 => x j) ha
      obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a j) 3).mp hj
      exact ⟨z, hz.symm⟩
    obtain ⟨s, hs⟩ := ha'
    refine ⟨s, ?_⟩
    rw [← hs]
    ext j
    simp
  · rintro ⟨s, rfl⟩
    ext j
    change ((3 • s) j : ZMod 3) = 0
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((3 • s) j) 3).mpr
    refine ⟨s j, ?_⟩
    simp

variable {O : Type*}

/-- The map from free even coordinates into the full profile quotient. -/
def evenClass (P : AddSubgroup (Profile O)) : FinitePrimary →+ Profile O ⧸ P :=
  (QuotientAddGroup.mk' P).comp (primary.comp even)

/-- Clearing horizontal, guard and E entries, then subtracting q columns,
shows that even coordinates generate every class. -/
theorem evenClass_surjective (P : AddSubgroup (Profile O))
    (hclear : ∀ x : Profile O, ∃ a : FinitePrimary, x - primary a ∈ P)
    (hrel : ∀ a : FinitePrimary,
      primary a ∈ P ↔ ∃ s u : FinitePrimary, Represents s u a) :
    Function.Surjective (evenClass P) := by
  intro z
  induction z using Quotient.inductionOn' with
  | h x =>
    obtain ⟨a, ha⟩ := hclear x
    have hq : primary (O := O) (qVector (oddPart a)) ∈ P := by
      apply (hrel _).mpr
      refine ⟨0, oddPart a, ?_⟩
      simpa using represents_columns 0 (oddPart a)
    have hx : (QuotientAddGroup.mk' P) x = (QuotientAddGroup.mk' P) (primary a) :=
      QuotientAddGroup.eq_iff_sub_mem.mpr ha
    have hy : (QuotientAddGroup.mk' P) (primary a) = evenClass P (residual a) := by
      calc
        (QuotientAddGroup.mk' P) (primary a) =
            (QuotientAddGroup.mk' P) (primary (even (residual a) + qVector (oddPart a))) :=
          congrArg (fun z => (QuotientAddGroup.mk' P) (primary z)) (decomposition a)
        _ = evenClass P (residual a) := by
          rw [map_add, map_add, show (QuotientAddGroup.mk' P) (primary (qVector (oddPart a))) = 0 from
            (QuotientAddGroup.eq_zero_iff _).mpr hq, add_zero]
          rfl
    exact ⟨residual a, (hx.trans hy).symm⟩

/-- The only relations among even classes are the independent triples. -/
theorem evenClass_ker (P : AddSubgroup (Profile O))
    (hrel : ∀ a : FinitePrimary,
      primary a ∈ P ↔ ∃ s u : FinitePrimary, Represents s u a) :
    (evenClass P).ker = modThree.ker := by
  ext a
  change (QuotientAddGroup.mk' P) (primary (even a)) = 0 ↔ modThree a = 0
  exact (QuotientAddGroup.eq_zero_iff (primary (even a))).trans
    ((hrel _).trans ((represents_even_iff a).trans (modThree_eq_zero_iff a).symm))

/-- Exact Picard-profile algebra: after the actual elimination and principal
representation inputs, the quotient is the countable direct sum of Z/3Z. -/
def quotientEquiv (P : AddSubgroup (Profile O))
    (hclear : ∀ x : Profile O, ∃ a : FinitePrimary, x - primary a ∈ P)
    (hrel : ∀ a : FinitePrimary,
      primary a ∈ P ↔ ∃ s u : FinitePrimary, Represents s u a) :
    Profile O ⧸ P ≃+ (ℕ →₀ ZMod 3) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (evenClass P)
    (evenClass_surjective P hclear hrel)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (evenClass_ker P hrel)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective modThree modThree_surjective))

end UnconditionalCounterexample.PrimaryProfileQuotient
