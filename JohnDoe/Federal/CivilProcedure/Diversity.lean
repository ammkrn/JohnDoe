import Mathlib.Data.List.Basic
import Mathlib.Init.Data.List.Instances
import Mathlib.Tactic.SolveByElim
import Mathlib.Logic.Basic
import UsCourts.Defs
import UsCourts.Federal.Defs
import UsCourts.Federal.Basic
import JohnDoe.Util

open Std (HashMap)

structure DiversityCitizenship where
  name : String
  /- for 1441 removal -/
  nameIsFictitious : Bool
  stateCitizenships : List StateOrTerritoryTag
  foreignCitizenships : List String
  permanentResidentDomiciledIn : Option StateOrTerritoryTag
  isStatelessUsCitizen : Bool
  isForeignState : Bool
  h0 : 
    (isStatelessUsCitizen.xor isForeignState).xor 
    (!stateCitizenships.isEmpty || !foreignCitizenships.isEmpty || permanentResidentDomiciledIn.isSome) := by decide
  h1 : (!stateCitizenships.isEmpty).nand isStatelessUsCitizen := by decide
  h2 : (!stateCitizenships.isEmpty).nand permanentResidentDomiciledIn.isSome := by decide
deriving DecidableEq, Hashable, Repr

class HasDiversityCitizenship (A : Type u) where
  diversityCitizenship : A → DiversityCitizenship

instance : HasDiversityCitizenship DiversityCitizenship := ⟨id⟩ 

@[reducible]
def DiversityCitizenship.allStates (p : DiversityCitizenship) : List StateOrTerritoryTag :=
  let permRes := 
  match p.permanentResidentDomiciledIn with
  | none => []
  | some s => [s]
  p.stateCitizenships ++ permRes
  
@[reducible]
def completeDiversity1 (p₁ p₂ : DiversityCitizenship) : Prop :=
  ∀ pr ∈ (p₁.allStates.product p₂.allStates), pr.fst ≠ pr.snd

@[reducible]
def DiversityCitizenship.completeDiversity (ps ds : List DiversityCitizenship) :=
  ∀ pr ∈ ps.product ds, completeDiversity1 pr.fst pr.snd

@[reducible]
def DiversityCitizenship.isNoncitizen (p : DiversityCitizenship) : Prop :=
  p.stateCitizenships.isEmpty ∧ ¬p.isStatelessUsCitizen

structure DiversityInterpretation where
  isCitizenOfAState : DiversityCitizenship → Prop
  isForeignCitizenOrSubject : DiversityCitizenship → Prop
  inst1 : DecidablePred isCitizenOfAState
  inst2 : DecidablePred isForeignCitizenOrSubject

instance {i : DiversityInterpretation} : DecidablePred (i.isCitizenOfAState) := i.inst1
instance {i : DiversityInterpretation} : DecidablePred (i.isForeignCitizenOrSubject) := i.inst2

@[reducible]
def DiversityInterpretation.isDualCitizen (i : DiversityInterpretation) (p : DiversityCitizenship) : Prop :=
  i.isCitizenOfAState p ∧ i.isForeignCitizenOrSubject p

@[reducible]
def DiversityInterpretation.a1 (i : DiversityInterpretation) (ps ds : List DiversityCitizenship) : Prop :=
  ∀ p ∈ ps, i.isCitizenOfAState p ∧ ∀ d ∈ ds, i.isCitizenOfAState d

@[reducible]
def DiversityInterpretation.a2 (i : DiversityInterpretation) (ps ds : List DiversityCitizenship) : Prop :=
  let oneSide (ps ds : List DiversityCitizenship) :=
    ∀ p ∈ ps, i.isCitizenOfAState p
    ∧ ∀ d ∈ ds, i.isForeignCitizenOrSubject d
  (oneSide ps ds ∨ oneSide ds ps) 

@[reducible]
def DiversityInterpretation.a3 (i : DiversityInterpretation) (ps ds : List DiversityCitizenship) : Prop :=
  (∃ p ∈ ps, i.isCitizenOfAState p)
  ∧ (∃ d ∈ ds, i.isCitizenOfAState d)
  ∧ ((∃ p ∈ ds, i.isForeignCitizenOrSubject p) ∨ (∃ d ∈ ds, i.isForeignCitizenOrSubject d))
  ∧ (∀ p ∈ ps, i.isCitizenOfAState p ∨ i.isForeignCitizenOrSubject p)
  ∧ (∀ d ∈ ds, i.isCitizenOfAState d ∨ i.isForeignCitizenOrSubject d)
  ∧ (ps.length > 1 ∨ ds.length > 1)

@[reducible]
def DiversityInterpretation.a4 (i : DiversityInterpretation) : List DiversityCitizenship → List DiversityCitizenship → Prop
| [p], ds => p.isForeignState ∧ ∀ d ∈ ds, i.isCitizenOfAState d
| _, _ => False

@[reducible]
def DiversityInterpretation.«a1_4»
  (i : DiversityInterpretation) 
  (ps ds : List DiversityCitizenship) : Prop :=
  i.a1 ps ds ∨ i.a2 ps ds ∨ i.a3 ps ds ∨ i.a4 ps ds

@[reducible]
def DiversityInterpretation.test1332Inner 
  (i : DiversityInterpretation) 
  (ps ds : List DiversityCitizenship) : Prop :=
    (i.«a1_4»  ps ds)
  ∧ (DiversityCitizenship.completeDiversity ps ds)
  ∧ ¬(∀ p ∈ ps, p.isNoncitizen ∧ ∀ d ∈ ds, d.isNoncitizen)
  ∧ (¬ps.isEmpty ∧ ¬ds.isEmpty)

@[reducible]
def DiversityInterpretation.test1332 
  {A : Type} 
  {B : Type}
  [HasDiversityCitizenship A]
  [HasDiversityCitizenship B]
  (i : DiversityInterpretation) 
  (ps : List A) 
  (ds : List B) : Prop := 
  let ps := ps.map HasDiversityCitizenship.diversityCitizenship
  let ds := ds.map HasDiversityCitizenship.diversityCitizenship
  i.test1332Inner ps ds

instance 
  (i : DiversityInterpretation) 
  (ps ds : List DiversityCitizenship) : Decidable (i.a4 ps ds) := by
  simp [DiversityInterpretation.a4]; split <;> exact inferInstance
  
instance 
  {A : Type} 
  {B : Type}
  [HasDiversityCitizenship A]
  [HasDiversityCitizenship B]
  (i : DiversityInterpretation) 
  (ps : List A) 
  (ds : List B) : Decidable (i.test1332 ps ds) := 
  inferInstance

def conservative : DiversityInterpretation := {
  /- Allows only US citizens domiciled in a state; No dual citizenship, no permanent residents -/
  isCitizenOfAState := 
    fun p => 
      ¬p.stateCitizenships.isEmpty 
      ∧ p.foreignCitizenships.isEmpty 
      ∧ p.permanentResidentDomiciledIn.isNone
      ∧ ¬p.isStatelessUsCitizen
  /- Allows only purely foreign citizens or subject (no dual citizenship), or permanent residents -/
  isForeignCitizenOrSubject := 
    fun p => ¬p.foreignCitizenships.isEmpty ∨ p.permanentResidentDomiciledIn.isSome
  inst1 := inferInstance
  inst2 := inferInstance
}


def interp1 : DiversityInterpretation := {
  /- Considers anyone (even dual citizens) domiciled in a US state to be a "citizen of a state" -/
  isCitizenOfAState := fun p => 
    ¬p.stateCitizenships.isEmpty
  isForeignCitizenOrSubject := fun p => 
    ¬p.foreignCitizenships.isEmpty ∨ p.permanentResidentDomiciledIn.isSome
  inst1 := inferInstance
  inst2 := inferInstance
}

structure LawfulDiversityInterpretation extends DiversityInterpretation where
  hr1 (a b : DiversityCitizenship) : 
    toDiversityInterpretation.isForeignCitizenOrSubject a
    → toDiversityInterpretation.isDualCitizen b 
    → ¬toDiversityInterpretation.a1_4 [a] [b] ∧ ¬toDiversityInterpretation.a1_4 [b] [a]
  hr2 
    (a b : DiversityCitizenship) 
    (s : StateOrTerritoryTag)
    (ha : s ∈ a.stateCitizenships)
    (hb : s ∈ b.stateCitizenships) :
    toDiversityInterpretation.isDualCitizen b 
    → ¬toDiversityInterpretation.a1_4 [a] [b] ∧ ¬toDiversityInterpretation.a1_4 [b] [a]
  constitutionA3S2 
    (xs ys : List DiversityCitizenship) 
    (hx : ∀ x ∈ xs, x.isNoncitizen) 
    (hy : ∀ y ∈ ys, y.isNoncitizen) 
    : ¬toDiversityInterpretation.a1_4 xs ys

