import Mathlib.Data.List.Basic
import Mathlib.Init.Data.List.Instances
import Mathlib.Logic.Basic
import UsCourts.Defs
import UsCourts.Federal.Defs
import JohnDoe.Util
import JohnDoe.Federal.CivilProcedure.Diversity

class HasResidency (A : Type u) where
  residencyAsPlaintiff : A → List District
  residencyAsDefendant : A → List District

structure UnincorporatedAssociationMember where
  name : String
  diversityCitizenship : DiversityCitizenship
deriving DecidableEq, Hashable, Repr

instance : HasDiversityCitizenship UnincorporatedAssociationMember where
  diversityCitizenship c := c.diversityCitizenship

class AssociationWithCapacityToBeSued where
  globalPrincipalPlaceOfBusinessMaintainedIn : District
  domesticPrincipalPlaceOfBusinessMaintainedIn : Option District

structure NaturalPerson where
  name : String
  nameIsFictitious : Bool
  domicile : Option District
  isUsCitizen : Bool
  /-- Is this person a foreign citizen with permanent resident status -/
  isForeignPermanentResident : Bool
  /-- Any foreign states of which the person is a citizen or subject -/
  foreignCitizenships : List String
deriving DecidableEq, Hashable, Repr

instance : HasDiversityCitizenship NaturalPerson where
  diversityCitizenship p :=
    {
      name := p.name
      nameIsFictitious := p.nameIsFictitious
      stateCitizenships :=
        match p.isUsCitizen, p.domicile with
        | true, some s => [s.stateOrTerritory]
        | _, _ => []
      foreignCitizenships := p.foreignCitizenships
      permanentResidentDomiciledIn := 
        if p.isForeignPermanentResident 
        then p.domicile.map District.stateOrTerritory 
        else none
      isStatelessUsCitizen := p.isUsCitizen ∧ p.domicile.isNone
      isForeignState := false
      h0 := sorry
      h1 := sorry
      h2 := sorry
    }

instance : HasResidency NaturalPerson := 
  let residencyAsPlaintiff := fun (p : NaturalPerson) =>
    match p.domicile with
    | none => []
    | some d => [d]
  {
    residencyAsPlaintiff
    residencyAsDefendant := residencyAsPlaintiff
  }

structure Corporation where
  name : String
  nameIsFictitious : Bool
  incorporatedIn : List StateOrForeignState
  globalPrincipalPlaceOfBusinessMaintainedIn : StateOrForeignState
  domesticPrincipalPlaceOfBusinessMaintainedIn : Option District
  contactsSufficientForPersonalJurisdictionForThisAction : List District
  mostSignificantContacts : List District
deriving DecidableEq, Hashable, Repr

instance : HasDiversityCitizenship Corporation where
  diversityCitizenship c :=
    let l := c.globalPrincipalPlaceOfBusinessMaintainedIn :: c.incorporatedIn
    let stateCitizenships := l.filterMap StateOrForeignState.getState
    let foreignCitizenships := l.filterMap StateOrForeignState.getForeignState
    {
      name := c.name
      nameIsFictitious := c.nameIsFictitious
      stateCitizenships
      foreignCitizenships
      permanentResidentDomiciledIn := none
      isStatelessUsCitizen := false
      isForeignState := false
      h0 := sorry
      h1 := by simp [Bool.nand]
      h2 := by simp [Bool.nand]
    }

instance : HasResidency Corporation where
  residencyAsDefendant c :=
    if ¬c.contactsSufficientForPersonalJurisdictionForThisAction.isEmpty
    then c.contactsSufficientForPersonalJurisdictionForThisAction
    else c.mostSignificantContacts
  residencyAsPlaintiff c :=
    match c.domesticPrincipalPlaceOfBusinessMaintainedIn with
    | none => []
    | some d => [d]

structure UnincorporatedAssociation (A : Type) where
  name : String
  nameIsFictitious : Bool
  globalPrincipalPlaceOfBusinessMaintainedIn : StateOrForeignState
  domesticPrincipalPlaceOfBusinessMaintainedIn : Option District
  contactsSufficientForPersonalJurisdictionForThisAction : List District
  members : List A
deriving DecidableEq, Hashable, Repr

instance {A : Type} [HasDiversityCitizenship A] : HasDiversityCitizenship (UnincorporatedAssociation A) where
  diversityCitizenship a :=
    let memberCitizenships := a.members.map HasDiversityCitizenship.diversityCitizenship
    let stateCitizenships := memberCitizenships.bind DiversityCitizenship.stateCitizenships
    let foreignCitizenships := memberCitizenships.bind DiversityCitizenship.foreignCitizenships
    let isStatelessUsCitizen := memberCitizenships.any DiversityCitizenship.isStatelessUsCitizen
    {
      name := a.name
      nameIsFictitious := a.nameIsFictitious
      stateCitizenships
      foreignCitizenships
      permanentResidentDomiciledIn := none
      isStatelessUsCitizen
      isForeignState := false
      h0 := sorry
      h1 := sorry
      h2 := sorry
    }

instance {A : Type} : HasResidency (UnincorporatedAssociation A) where
  residencyAsPlaintiff a := 
    match a.domesticPrincipalPlaceOfBusinessMaintainedIn with
    | none => []
    | some d => [d]
  residencyAsDefendant a := 
    a.contactsSufficientForPersonalJurisdictionForThisAction

structure InsurerDirectClaim (A : Type) (B : Type) where
  insurer : A
  insured : B
  val : Unit

structure ClassMember where
deriving DecidableEq, Repr

structure InRem where
deriving DecidableEq, Repr

structure Representative (A : Type) (B : Type) where
  representative : A
  represented : B

structure UnitedStates where
  immunityWaiver : Option String
deriving DecidableEq, Repr

structure State' where
  immunityWaiver : Option String
  immunityAbrogated : Option String
deriving DecidableEq, Repr

structure ForeignState where
  name : String
  immunityWaiver : Option String
  districts_f2 : List District
  districts_f3 : List District
deriving DecidableEq, Hashable, Repr

instance : HasDiversityCitizenship ForeignState where
  diversityCitizenship c :=
    {
      name := c.name
      nameIsFictitious := false
      stateCitizenships := []
      foreignCitizenships := []
      permanentResidentDomiciledIn := none
      isStatelessUsCitizen := false
      isForeignState := true
      h0 := sorry 
      h1 := sorry 
      h2 := sorry 
    }

inductive Party
| naturalPerson (p : NaturalPerson)
| corporation (c : Corporation)
| unincorporatedAssociation (a : UnincorporatedAssociation UnincorporatedAssociationMember)
| foreignState (s : ForeignState)
--| inRem (i : InRem)
--| classMember (c : ClassMember)
--| state (s : State')
--| unitedStates (u : UnitedStates)
deriving DecidableEq, Hashable, Repr

def Party.name : Party → String
| naturalPerson p => p.name
| corporation p => p.name
| unincorporatedAssociation p => p.name
| foreignState p => p.name

instance : HasDiversityCitizenship Party where
  diversityCitizenship :=
    fun 
    | .naturalPerson p => HasDiversityCitizenship.diversityCitizenship p
    | .corporation c => HasDiversityCitizenship.diversityCitizenship c
    | .unincorporatedAssociation a => HasDiversityCitizenship.diversityCitizenship a
    | .foreignState c => HasDiversityCitizenship.diversityCitizenship c
    --| .classMember c => []
    --| .inRem c => []
    --| .state c => []
    --| .unitedStates c => []

instance : HasResidency Party where
  residencyAsPlaintiff := 
    fun 
    | .naturalPerson p => HasResidency.residencyAsPlaintiff p
    | .corporation c => HasResidency.residencyAsPlaintiff c
    | .unincorporatedAssociation a => HasResidency.residencyAsPlaintiff a
    | .foreignState c => []
    --| .classMember c => []
    --| .inRem c => []
    --| .state c => []
    --| .unitedStates c => []
  residencyAsDefendant := 
    fun 
    | .naturalPerson p => HasResidency.residencyAsDefendant p
    | .corporation c => HasResidency.residencyAsDefendant c
    | .unincorporatedAssociation a => HasResidency.residencyAsDefendant a
    | .foreignState c => []
    --| .classMember c => []
    --| .inRem c => []
    --| .state c => []
    --| .unitedStates c => []
