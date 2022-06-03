import Mathlib.Data.List.Basic
import Mathlib.Init.Data.List.Instances
import Mathlib.Logic.Basic
import UsCourts.Defs
import UsCourts.Federal.Defs
import UsCourts.Federal.Basic
import JohnDoe.Util
import JohnDoe.Federal.CivilProcedure.Pleading.Claim

class HasVenue where
  properVenues : ∀ (d : Party), Complaint → List District

@[reducible]
def Claim.b1 (c : Claim) : List District :=
  if c.allDefendantsResideInSameState
  then c.defendantResidencies
  else []

@[reducible]
def Claim.b2 (c : Claim) : List District :=
  c.substantialPartDistricts

@[reducible]
def Claim.officerOrEmployeeOfTheUsVenue (c : Claim) : List District :=
  c.defendantResidencies
  ++ c.substantialPartDistricts
  ++ if ¬c.realPropertyInvolvedInAction then HasResidency.residencyAsPlaintiff c.namedPlaintiff else []

def Claim.foreignStateDefendantVenue (c : Claim) : List District :=
  c.substantialPartDistricts
  ++ c.foreignStateDefendantVenues
  ++ [DistrictOfColumbia]

def Claim.properVenues (c : Claim) : List District := 
  let base := 
    if c.againstOfficerOrEmployeeOfTheUs
    then c.foreignStateDefendantVenue
    else if c.foreignStateDefendant
    then c.foreignStateDefendantVenue
    else c.b1 ++ c.b2
  if base.isEmpty
  -- b3 fallback
  then c.defendantsSubjectToPersonalJurisdictionIn.dedup
  else base.dedup

def properVenues (cs : List Claim) : List District :=
  (cs.map Claim.properVenues).Inter

def Claim.properVenues' (c : Claim) : StateT Log Id (List String) := do
  return (c.properVenues).map District.fullName

