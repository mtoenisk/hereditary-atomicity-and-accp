import UnconditionalCounterexample.Variations.DyadicProfiles

/-!
# Permanent weights of fresh dyadic fibres

A paired primary is a regular plus or minus site, or an auxiliary correction.
Its guard contributes the opposite signed weight on the same channel.
-/

namespace UnconditionalCounterexample.Variations.DyadicLedger

inductive FibreRole where
  | regular (centre channel : Bool) (index : ℕ)
  | auxiliary (channel : Bool) (index : ℕ) (positive : Bool)
  deriving DecidableEq

namespace FibreRole

def channel : FibreRole → Bool
  | .regular _ k _ | .auxiliary k _ _ => k

def index : FibreRole → ℕ
  | .regular _ _ n | .auxiliary _ n _ => n

def sign : FibreRole → ℤ
  | .regular false _ _ | .auxiliary _ _ true => 1
  | .regular true _ _ | .auxiliary _ _ false => -1

/-- Paired values cancel on rational prime scalars since both orders agree. -/
def contribution (role : FibreRole) (k : Bool) (primary guard : ℤ) : ℚ :=
  if role.channel = k then
    (role.sign : ℚ) * DyadicProfiles.weight role.index * (primary - guard) else 0

@[simp] theorem contribution_same (role : FibreRole) (k : Bool) (z : ℤ) :
    role.contribution k z z = 0 := by simp [contribution]

theorem contribution_add (role : FibreRole) (k : Bool) (a b c d : ℤ) :
    role.contribution k (a+c) (b+d) = role.contribution k a b + role.contribution k c d := by
  by_cases h : role.channel = k
  · simp [contribution, h]
    ring
  · simp [contribution, h]

end FibreRole
end UnconditionalCounterexample.Variations.DyadicLedger
