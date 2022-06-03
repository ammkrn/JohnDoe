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
-- United States as plaintiff
| s1345
-- Banking association as party 
| s1348
-- Multiparty, multiforum jurisdiction
| s1369
| diversity
| supplemental
| scOriginal
deriving DecidableEq, Hashable, Repr

@[reducible]
def JurisdictionalGrant.federalSjm : JurisdictionalGrant → Prop
| diversity => False
| supplemental => False
| _ => True

structure AttorneyInfo where
  name : String
  qualifications : String
  title : String
  address : String
  telephoneNumber : String
deriving DecidableEq, Hashable, Repr

structure Claim where
  namedPlaintiff : Party
  namedDefendant : Party
  plaintiffs : List Party
  defendants : List Party
  reliefRequested : List Relief
  causeOfAction : String
  explanation : List String
  defendantsSubjectToPersonalJurisdictionIn : List District
  substantialPartDistricts : List District
  realPropertyInvolvedInAction : Bool
  againstOfficerOrEmployeeOfTheUs : Bool
  jurisdiction : JurisdictionalGrant
  hp : namedPlaintiff ∈ plaintiffs := by decide
  hd : namedDefendant ∈ defendants := by decide
deriving DecidableEq, Hashable, Repr

@[reducible]
def allAmountsInControversy (claims : List Claim) : HashMap (Party × Party) Nat := 
  (claims.bind Claim.reliefRequested).foldl (init := HashMap.empty)
    (fun sink relief =>
      sink.insert (relief.p, relief.d) ((sink.find? (relief.p, relief.d)).getD 0))
  
@[reducible]
def groupOfDiversityClaimsOk (i : DiversityInterpretation) (claims : List Claim) : Prop :=
  let pairsGtThreshold := 
    (allAmountsInControversy claims).toList.filterMap
      (fun ⟨pd, amt⟩ => if amt > 75000 then some pd else none)
  (∀ c ∈ claims, ∃ p ∈ c.plaintiffs, (∀ d ∈ c.defendants, (p, d) ∈ pairsGtThreshold))
  ∧ i.test1332 (claims.bind Claim.plaintiffs) (claims.bind Claim.defendants)


@[reducible]
def diversityIntact (claims : List Claim) : Prop := 
  let ps := (claims.bind (Claim.plaintiffs)).map HasDiversityCitizenship.diversityCitizenship
  let ds := (claims.bind (Claim.defendants)).map HasDiversityCitizenship.diversityCitizenship
  DiversityCitizenship.completeDiversity ps ds

@[reducible]
def initialJurisdictionsOk (i : DiversityInterpretation) (claims : List Claim) : Prop :=
  let diversityClaims := claims.filter fun x => x.jurisdiction = .diversity
  let diversityOk := 
    diversityClaims.isEmpty ∨ (groupOfDiversityClaimsOk i diversityClaims ∧ diversityIntact claims)
  (∃ c ∈ claims, c.jurisdiction ≠ .supplemental) ∧ diversityOk

@[reducible]
def Claim.foreignStateDefendant (c : Claim) : Prop :=
  c.defendants.any
    fun
    | .foreignState _ => True
    | _ => False

@[reducible]
def Claim.foreignStateDefendantVenues (c : Claim) : List District := Id.run do
  let mut venues := []
  for d in c.defendants do
    match d with
    | .foreignState f =>
      venues := venues ++ f.districts_f2 ++ f.districts_f3
      continue
    | _ => continue
  venues

@[reducible]
def Claim.defendantResidencies (c : Claim) : List District :=
  c.defendants.bind HasResidency.residencyAsDefendant

@[reducible]
def Claim.allDefendantsResideInSameState (c : Claim) : Prop :=
  match c.defendantResidencies with
  | [] => False
  | h :: t =>
    ∀ l ∈ c.defendants.map HasResidency.residencyAsDefendant,
      (∃ x ∈ l, x.stateOrTerritory = h.stateOrTerritory)

instance (c : Claim) : Decidable (c.allDefendantsResideInSameState) := by
  simp [Claim.allDefendantsResideInSameState]; split <;> exact inferInstance
