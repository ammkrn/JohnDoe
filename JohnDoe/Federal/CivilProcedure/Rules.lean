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

set_option autoImplicit false

open Std (HashMap AssocList)

structure Document where
  contents : String
  timeStamp : TaiDateTime
deriving Repr

structure Config where
  documents : List Document
  status : Status
  dateTime : TaiDateTime
  venue : District
  parties : HashMap Party PartyStatus
  claims : List Claim
  complaint : FiledComplaint
  removedByDefendant : Bool
  motions : List Motion
  summonses : List SummonsOrWaiver

abbrev CivilActionState := Config

structure ComInfo where
  /- taken at -/
  dateTime : TaiDateTime
  /- The accompanying document (if it exists) -/
  document : Option Document
  /- Additional information -/
  label : String

-- Com
structure Com extends ComInfo where
  pre : Config → Prop
  f : ∀ (store : Config), pre store → Config
  post : Config → Prop
  preErrorMsg (cfg : Config) (h : ¬pre cfg) : String
  postErrorMsg (cfg : Config) (hPre : pre cfg) (hPost : ¬post (f cfg hPre)) : String
  [decidablePre : DecidablePred pre]
  [decidablePost : DecidablePred post]
  --postErrorMsg+ : ∀ cfg cfg', (pre cfg) → (cfg' = f cfg) → ¬post cfg' → Error

instance : ∀ (com : Com), DecidablePred (com.pre) := Com.decidablePre 
instance : ∀ (com : Com), DecidablePred (com.post) := Com.decidablePost

-- Pgm/ProceduralHistory
inductive BinTree
| leaf (com : Com)
| node (l r : BinTree) 

abbrev ProceduralHistory := BinTree

inductive BinTree.EvalR : BinTree → Config → Config → Prop
| leaf 
  (com : Com)
  (store store' : Config)
  (hPre : com.pre store)
  (h : com.f store hPre = store')
  (hPost : com.post store') 
  (hTime : store.dateTime <= store'.dateTime) :
    EvalR (.leaf com) store store'
| node 
  (l r : BinTree)
  (store₀ store₁ store₂ : Config)
  (hL : EvalR l store₀ store₁)
  (hR : EvalR r store₁ store₂) :
    EvalR (.node l r) store₀ store₂ 

/-
Inversion rule for leaves
-/
theorem BinTree.EvalR.leaf_inversion (com : Com) (store store' : Config) :
  EvalR (.leaf com) store store' ↔ (∃ hPre, com.f store hPre = store' ∧ com.post store' ∧ store.dateTime <= store'.dateTime) := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro h; 
    cases h with
    | leaf _ _ _ a4 a5 a6 a7 =>
      exact Exists.intro a4 ⟨a5, a6, a7⟩
  case mpr =>
    intro h
    cases h with
    | intro w p =>
      exact EvalR.leaf com store store' w p.left p.right.left p.right.right

/-
Inversion rule for nodes
-/
theorem BinTree.EvalR.node_inversion (l r : BinTree) (store store' : Config) :
  EvalR (.node l r) store store' ↔ (∃ store_x, EvalR l store store_x ∧ EvalR r store_x store') :=  by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro h
    cases h with
    | node a1 a2 a3 store_x a5 a6 a7 =>
      exact Exists.intro store_x ⟨a6, a7⟩
  case mpr =>
    intro h
    cases h with
    | intro w p =>
      exact EvalR.node l r store w store' p.left p.right


theorem timeMono (t : BinTree) (s s' : Config) : 
  t.EvalR s s' → s.dateTime <= s'.dateTime
| BinTree.EvalR.leaf _ s s' _ _ _ hTime => hTime
| BinTree.EvalR.node l r s0 s1 s2 hL hR => 
  le_trans (timeMono l s0 s1 hL) (timeMono r s1 s2 hR)

abbrev ErrString := String

def BinTree.eval : BinTree → EStateM ErrString Config Unit
| leaf com => do
  let cfg ← get
  if hPre : com.pre cfg
  then 
    let cfg' := com.f cfg hPre
    if ¬cfg.dateTime <= cfg'.dateTime 
    then 
      throw "time error"
    else if ¬com.post cfg'
    then 
      throw "failedPostError"
    else
      set cfg'
  else
    throw "failedPrestateError"
| node l r => do eval l; eval r


theorem BinTree.evalsEquivMp (t : BinTree) (cfg cfg' : Config) :
  t.EvalR cfg cfg' → t.eval.run cfg = EStateM.Result.ok () cfg'
| EvalR.leaf c s s' hPre h hPost hT => by
  simp [BinTree.eval, EStateM.run]
  simp at hT
  simp [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hPre, h, hPost, hT, set, EStateM.set]
| EvalR.node l r _ cfgX _ hL hR => by
  have ihL := evalsEquivMp l cfg cfgX hL
  have ihR := evalsEquivMp r cfgX cfg' hR
  simp [EStateM.run] at ihL ihR
  simp [BinTree.eval, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, ihL, ihR]
  done

theorem evalsEquivMpr : 
  ∀ 
  (t : BinTree)
  (cfg cfg' : Config), 
  t.eval.run cfg = EStateM.Result.ok () cfg' → t.EvalR cfg cfg'
| BinTree.leaf c, cfg, cfg' => by
  sorry
| BinTree.node l r, cfg, cfg' => by
  sorry

@[reducible]
def BinTree.pre : BinTree → (Config → Prop)
| leaf com => com.pre
| node l _ => l.pre

@[reducible]
def BinTree.post : BinTree → (Config → Prop)
| leaf com => com.post
| node _ r => r.post

/-
if `EvalR t s s'`, then the precondition is true of s
-/
theorem BinTree.EvalR_pre (t : BinTree) (store store' : Config) :
  t.EvalR store store' → t.pre store
| EvalR.leaf _ s s' hPre _ _ _ => hPre
| EvalR.node l _ s0 s1 s2 hL _ => EvalR_pre l s0 s1 hL

/-
If (EvalR t s s'), then t's post-condition is true of s'.
-/
theorem BinTree.EvalR_post (t : BinTree) (store store' : Config) :
  t.EvalR store store' → t.post store'
| EvalR.leaf _ s s' _ _ hpost _ => hpost 
| EvalR.node _ r s0 s1 s2 _ ih1 => EvalR_post r s1 s2 ih1

private theorem BinTree.EvalR_deterministicAux : 
  ∀ (pgm : BinTree) 
    (store storeA : Config),
    pgm.EvalR store storeA 
    → (∀ storeB : Config, pgm.EvalR store storeB → storeA = storeB) 
| (.leaf com), s, storeA, EvalR.leaf _ _ _ _ f _ _, sB, EvalR.leaf _ _ _ _ i _ _ => by rw [← f, ← i]
| (.node l r), s, storeA, EvalR.node _ _ _ s1 _ P Q, storeB, EvalR.node _ _ _ s1' _ T U =>
  have ihl := EvalR_deterministicAux l s s1 P s1' T
  EvalR_deterministicAux r s1 storeA Q storeB (ihl ▸ U)

theorem BinTree.EvalR_deterministic (pgm : BinTree) (store storeA storeB : Config) :
  pgm.EvalR store storeA → pgm.EvalR store storeB → storeA = storeB :=
  fun hA hB => BinTree.EvalR_deterministicAux pgm store storeA hA storeB hB

-- S₀ ⊆ S
def Complaint.file (complaint : Complaint) : ∀ (filedOn : TaiDateTime) (caseNum : Nat), Config
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
    summonses := []
    documents := [
      --(Document.mk (contents := complaint.text) (dateTime := filedOn))
    ]
}

/-
I think because of the monotonicity of time,
but I don't think it will be necessary to extend the rule discussions to `Store2`.
-/
@[reducible]
def validInitialStates : Set Config :=
    { cfg | ∃ (complaint : Complaint) (filedOn : TaiDateTime) (caseNum : Nat), cfg = complaint.file filedOn caseNum }

@[reducible]
def Config.isValidInitialConfig : Config → Prop := (. ∈ validInitialStates)

def EvalRBinary : Config → Config → Prop := fun s s' => ∃ (c : BinTree), c.EvalR s s'

def RTC : {α : Type _} → (α → α → Prop) → α → α → Prop := sorry

@[reducible]
def validTriple (c : BinTree) (s s' : Config) := 
  s ∈ validInitialStates ∧ c.EvalR s s'

@[reducible]
def Config.reachable (s : Config) := 
  ∃ s₀, s₀ ∈ validInitialStates ∧ RTC EvalRBinary s₀ s

@[reducible]
def Config.reachable' (s : Config) := 
  ∃ (c : BinTree) (s₀ : Config), validTriple c s₀ s

class Compiler (A : Type) where
  compile : A → Com

class SerializableCompiler (A : Type) (B : Type) extends Compiler A where
  encode : A → B
  decode : B → Option A
  encodeOk : ∀ a, decode (encode a) = some a
  
@[reducible]
def BinTree.mem (c : Com) : BinTree → Prop
| leaf x => x = c
| node l r => mem c l ∨ mem c r

instance : Membership Com BinTree where
  mem c t := BinTree.mem c t

instance {A : Type} [Compiler A] : Membership A BinTree where
  mem a t := (Compiler.compile a) ∈ t

