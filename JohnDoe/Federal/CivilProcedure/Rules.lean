import Mathlib.Data.Option.Basic
import UsCourts.Defs
import UsCourts.Federal.Defs
import Timelib.Date.Basic
import Timelib.Date.ScalarDate
import Timelib.NanoPrecision.DateTime.DateTime
import Timelib.NanoPrecision.Duration.SignedDuration
import JohnDoe.Util
import JohnDoe.Federal.CivilProcedure.Entities
import JohnDoe.Federal.CivilProcedure.Diversity
import JohnDoe.Federal.CivilProcedure.Pleading.Claim
import JohnDoe.Federal.CivilProcedure.Pleading.Complaint
import JohnDoe.Federal.CivilProcedure.Pleading.Service
import JohnDoe.Federal.CivilProcedure.Pleading.Answer
import JohnDoe.Federal.CivilProcedure.Motion
import JohnDoe.Federal.CivilProcedure.Period
import JohnDoe.Federal.CivilProcedure.CivilAction

open Std (HashMap AssocList)

set_option autoImplicit false

structure Document where
  contents : String
  dateTime : TaiDateTime
deriving Repr

structure Store where
  documents : List Document
  status : Status
  dateTime : TaiDateTime
  venue : District
  parties : HashMap Party PartyStatus
  claims : List Claim
  complaint : FiledComplaint
  removedByDefendant : Bool
  motions : List Motion
  summonses : Unit

structure ComInfo where
  dateTime : TaiDateTime
  label : String
  document : Option (String × TaiDateTime)

structure DCom extends ComInfo where
  -- Must be true before `f` can be executed.
  pre : Store → Prop
  f : ∀ (store : Store), pre store → Store
  -- Must be true after `f` for `EvalR`.
  post : Store → Prop

inductive BinTree
| leaf (com : DCom)
| node (l r : BinTree) 

inductive EvalR : BinTree → Store → Store → Prop
| leaf 
  (com : DCom)
  (store store' : Store)
  (hPre : com.pre store)
  (hPost : com.post store') 
  (h : com.f store hPre = store') : 
    EvalR (.leaf com) store store'
| node 
  (l r : BinTree)
  (store₀ store₁ store₂ : Store)
  (hL : EvalR l store₀ store₁)
  (hR : EvalR r store₁ store₂) 
  (hTimeMonoL : store₀.dateTime <= store₁.dateTime)
  (hTImeMonoR : store₁.dateTime <= store₂.dateTime) : 
    EvalR (.node l r) store₀ store₂ 

@[reducible]
def BinTree.pre : BinTree → (Store → Prop)
| leaf com => com.pre
| node l _ => l.pre

@[reducible]
def BinTree.post : BinTree → (Store → Prop)
| leaf com => com.post
| node _ r => r.post

/-
if `EvalR t s s'`, then the precondition is true of s
-/
theorem EvalRPre 
  (t : BinTree) 
  (store store' : Store) 
  (h : EvalR t store store') : t.pre store := by
  cases h with
  | leaf c s s' hPre h hpost => 
    simp [BinTree.pre]
    exact hPre
  | node l r s0 s1 s2 h0 h1 => 
    simp [BinTree.pre]
    exact EvalRPre l store s1 h0

/-
If (EvalR t s s'), then t's post-condition is true of s'.
-/
theorem EvalRPost 
  (t : BinTree) 
  (store store' : Store) 
  (h : EvalR t store store') : t.post store' := by
  cases h with
  | leaf c s s' hpre h hpost => simp [BinTree.post]; assumption
  | node l r s0 s1 s2 h0 h1 => exact EvalRPost r s1 store' h1

theorem evalDeterministic : 
  ∀ (pgm : BinTree) 
    (store storeA : Store),
    EvalR pgm store storeA 
    → (∀ storeB : Store, EvalR pgm store storeB → storeA = storeB) 
| (.leaf com), s, storeA, EvalR.leaf _ _ _ _ _ f, sB, EvalR.leaf _ _ _ _ _ i => by rw [← f, ← i]
| (.node l r), s, storeA, EvalR.node _ _ _ s1 _ P Q _ _, storeB, EvalR.node _ _ _ s1' _ T U _ _ =>
  have ihl := evalDeterministic l s s1 P s1' T
  evalDeterministic r s1 storeA Q storeB (ihl ▸ U)

-- S₀ ⊆ S
def Complaint.file (complaint : Complaint) : ∀ (filedOn : TaiDateTime) (caseNum : Nat), Store
| filedOn, caseNum =>
  {
    status := .complaintFiled
    venue := complaint.venue
    dateTime := filedOn
    parties := sorry
    complaint := {
      complaint with
      header := sorry
      filedOn
      h := sorry
    }
    claims := complaint.claims
    removedByDefendant := false
    motions := []
    summonses := ()
    documents := [
      --(Document.mk (contents := complaint.text) (dateTime := filedOn))
    ]
}

theorem inversionLeaf (com : DCom) (store store' : Store) :
  EvalR (.leaf com) store store' ↔ (∃ hPre, com.f store hPre = store' ∧ com.post store') := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro h; 
    cases h with
    | leaf _ _ _ a4 a5 a6 =>
      exact Exists.intro a4 (And.intro a6 a5)
  case mpr =>
    intro h
    cases h with
    | intro w p =>
      exact EvalR.leaf com store store' w p.right p.left

theorem inversionNode (l r : BinTree) (store store' : Store) :
  EvalR (.node l r) store store' ↔ (∃ store_x, EvalR l store store_x ∧ EvalR r store_x store' ∧ store.dateTime <= store_x.dateTime ∧ store_x.dateTime <= store'.dateTime) :=  by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro h;
    cases h with
    | node a1 a2 a3 store_x a5 a6 a7 a8 =>
      refine Exists.intro store_x ?r
      refine And.intro a6 ?r0
      refine And.intro a7 ?r1
      refine And.intro a8 ?r2
      assumption
  case mpr =>
    intro h
    cases h with
    | intro w p =>
      apply EvalR.node l r store w store'
      exact p.left
      exact p.right.left
      exact p.right.right.left
      exact p.right.right.right

def validInitialStates : Set Store :=
    { store | ∃ (complaint : Complaint) (filedOn : TaiDateTime) (caseNum : Nat), store = complaint.file filedOn caseNum }

def EvalRBinary : Store → Store → Prop := fun s s' => ∃ (c : BinTree), EvalR c s s'

def RTC : {α : Type _} → (α → α → Prop) → α → α → Prop := sorry

def Store.reachable (s : Store) := ∃ s₀, s₀ ∈ validInitialStates ∧ @RTC Store EvalRBinary s₀ s
