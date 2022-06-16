import UsCourts.Defs
import UsCourts.Federal.Defs
import JohnDoe.Util
import JohnDoe.Federal.CivilProcedure.Entities
import JohnDoe.Federal.CivilProcedure.Diversity

open Std (HashMap)

structure Relief where
  p : Party
  d : Party
  amount : Nat
  description : String
deriving DecidableEq, Hashable, Repr

inductive JurisdictionalGrant
| federalQuestion
| foreignState
-- US as plaintiff
| s1345
-- Banking association as party 
| s1348
-- Multiparty, multiforum jurisdiction
| s1369
| diversity
-- s1441
| diversityRemoval
| federalQuestionRemoval
| supplemental (supplementing : JurisdictionalGrant)
| supplemental'
| scOriginal
deriving DecidableEq, Hashable, Repr

@[reducible]
def JurisdictionalGrant.federalSjm : JurisdictionalGrant → Prop
| diversity => False
| supplemental _ => False
| _ => True

structure AttorneyInfo where
  name : String
  qualifications : String
  title : String
  address : String
  telephoneNumber : String
deriving DecidableEq, Hashable, Repr

inductive ClaimKind
| direct
| cross
| counter
| thirdParty
deriving DecidableEq, Hashable, Repr

structure Claim where
  probateOrFamilyCase : Bool
  kind : ClaimKind
  description : String
  /-
  For keeping track of which claims represent "alternative claims"
  as in FRCP 18(a)
  -/
  altGroup : Option Nat
  plaintiff : Party
  defendant : Party
  reliefAmount : Nat
  reliefDescription : String
  causeOfAction : String
  defendantSubjectToPersonalJurisdictionIn : List District
  substantialPartDistricts : List District
  isFederalClaim : Bool
  realPropertyInvolvedInAction : Bool
  againstOfficerOrEmployeeOfTheUs : Bool
deriving DecidableEq, Hashable, Repr

@[reducible]
def sortClaimsByDescription (claims : List Claim) : HashMap String (List Claim) :=
  claims.foldl (init := HashMap.empty)
  fun sink next => 
    match sink.find? next.description with
    | none => sink.insert next.description [next]
    | some l => sink.insert next.description (next :: l)
  
@[reducible]
abbrev Claim.defendantResidencies (c : Claim) : List District :=
  HasResidency.residencyAsDefendant c.defendant

@[reducible]
abbrev Claim.plaintiffResidencies (c : Claim) : List District :=
  HasResidency.residencyAsPlaintiff c.plaintiff

@[reducible]
def Claim.againstForeignStateDefendant (c : Claim) : Prop :=
  match c.defendant with
  | .foreignState _ => True
  | _ => False
