import Mathlib.Data.Nat.Gcd
import Mathlib.Algebra.Group.Defs

structure Rat := mk' ::
num : Int
denom : Nat
pos : 0 < denom
cop : num.natAbs.coprime denom

namespace Rat

protected def toString : Rat → String
| ⟨n, d, _, _⟩ => 
  if d = 1 
  then s!"{n}"
  else s!"{n}" ++ "/" ++ s!"{d}"

instance : ToString Rat := ⟨Rat.toString⟩

def ofInt (n : Int) : Rat :=
  ⟨n, 1, Nat.one_pos, Nat.coprime_one_right _⟩

def mkPnat (n : Int) : { d : Nat // 0 < d } → Rat
| ⟨d, dpos⟩ =>
  let n' := n.natAbs
  let g := n'.gcd d
  ⟨n / g, d / g, sorry, sorry⟩ 

instance : OfNat Rat n where
  ofNat := ofInt (Int.ofNat n)
  
instance : Inhabited Rat := ⟨0⟩

def mkNat (n : Int) (d : Nat) : Rat :=
if d0 : d = 0 then 0 else mkPnat n ⟨d, Nat.pos_of_ne_zero d0⟩

def mk : Int → Int → Rat
| n, Int.ofNat d => mkNat n d
| n, Int.negSucc d => mkPnat (-n) ⟨d+1, Nat.succ_pos _⟩

infix:70 " /. " => mk

theorem mk_pnat_eq : mkPnat n ⟨d, h⟩ = n /. d := by simp [mk, mkNat, ne_of_gt h]

theorem mk_nat_eq : mkNat n d = n /. d := rfl

@[simp] theorem mk_zero (n) : n /. 0 = 0 := rfl

protected def add : Rat → Rat → Rat
| ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => mkPnat (n₁ * d₂ + n₂ * d₁) ⟨d₁ * d₂, Nat.mul_pos h₁ h₂⟩

instance : HAdd Rat Rat Rat where
  hAdd := Rat.add

@[simp] theorem add_def {a b c d : Int} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b + c /. d = (a * d + c * b) /. (b * d) := sorry

protected def neg (r : Rat) : Rat :=
⟨-r.num, r.denom, r.pos, by sorry⟩

instance : Neg Rat := ⟨Rat.neg⟩

@[simp] theorem neg_def {a b : Int} : -(a /. b) = -a /. b := sorry

protected def mul : Rat → Rat → Rat
| ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => mkPnat (n₁ * n₂) ⟨d₁ * d₂, Nat.mul_pos h₁ h₂⟩

instance : Mul Rat := ⟨Rat.mul⟩

@[simp] theorem mul_def {a b c d : Int} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  (a /. b) * (c /. d) = (a * c) /. (b * d) := sorry

protected def inv : Rat → Rat
| ⟨Int.ofNat (n+1), d, h, c⟩ => ⟨d, n+1, n.succ_pos, c.symm⟩
| ⟨Int.ofNat 0, d, h, c⟩ => 0
| ⟨Int.negSucc n, d, h, c⟩ => ⟨-d, n+1, n.succ_pos, Nat.coprime.symm $ sorry⟩

instance : Inv Rat := ⟨Rat.inv⟩

@[simp] theorem inv_def {a b : ℤ} : (a /. b)⁻¹ = b /. a := sorry

instance : HDiv Rat Rat Rat where
  hDiv r₁ r₂ := r₁ * (r₂⁻¹)

instance : DecidableEq Rat
| ⟨n₁, d₁, pos₁, cop₁⟩, ⟨n₂, d₂, pos₂, cop₂⟩ => 
  if hn : n₁ = n₂ 
  then 
    if hd : d₁ = d₂
    then by rw [Rat.mk'.injEq]; exact isTrue ⟨hn, hd⟩
    else isFalse <| fun hf => Rat.noConfusion hf (fun _ dEq => False.elim (hd dEq))
  else isFalse <| fun hf => Rat.noConfusion hf (fun nEq _ => False.elim (hn nEq))

instance : HSub Rat Rat Rat where
  hSub r₁ r₂ := r₁ + (-r₂)

theorem sub_def {a b c d : Int} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b - c /. d = (a * d - c * b) /. (b * d) := sorry

@[reducible]
protected def nonneg (r : Rat) : Prop := 0 <= r.num

protected def le (a b : Rat) := Rat.nonneg (b - a)

instance : LE Rat where
  le := Rat.le

instance decidable_le : DecidableRel ((.<=.) : Rat → Rat → Prop)
| a, b => inferInstanceAs (Decidable (Rat.nonneg (b - a)))

protected theorem le_def {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d) :
  a /. b <= c /. d ↔ a * d <= c * b := sorry

protected theorem le_refl (a : Rat) : a <= a := sorry

protected theorem le_total (a b : Rat) : a <= b ∨ b <= a := sorry

protected theorem le_antisymm {a b : Rat} (hab : a <= b) (hba : b <= a) : a = b := sorry

protected theorem le_trans {a b c : Rat} (hab : a <= b) (hbc : b <= c) : a <= c := sorry

instance : LinearOrder Rat where
  le              := Rat.le
  le_refl         := Rat.le_refl
  le_trans        := @Rat.le_trans
  le_antisymm     := @Rat.le_antisymm
  le_total        := Rat.le_total
  decidable_eq    := inferInstance
  decidable_le    := inferInstance
  lt_iff_le_not_le := sorry

end Rat


