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

structure AgainstUs where
  plaintiff : Party
  substantialPartDistricts : List District
  realPropertyInvolvedInAction : Bool
  claims : List Claim
  h : ∃ c ∈ claims, c.plaintiff = plaintiff := by decide
  h' : ∃ c ∈ claims, c.againstOfficerOrEmployeeOfTheUs := by decide
  
def AgainstUs.properVenues (x : AgainstUs) : List District :=
  let base := 
    (x.claims.bind Claim.defendantResidencies)
    ++ x.substantialPartDistricts
    ++ if !x.realPropertyInvolvedInAction then HasResidency.residencyAsPlaintiff x.plaintiff else []
  base.dedup

structure AgainstForeignState where
  plaintiff : Party
  foreignStateDefendant : ForeignState
  substantialPartDistricts : List District
  --claims : List Claim
  --h : ∃ c ∈ claims, c.plaintiff = plaintiff := by decide
  --h' : ∃ c ∈ claims, c.defendant = Party.foreignState foreignStateDefendant := by decide

def AgainstForeignState.properVenues (x : AgainstForeignState) : List District :=
  x.substantialPartDistricts
  ++ x.foreignStateDefendant.districts_f2
  ++ x.foreignStateDefendant.districts_f3
  ++ [DistrictOfColumbia]

/-
Not against the US/employee/agent,
and not against a foreign state.

This is for claims that have the same common base, but can be against
multiple defendants.
-/
structure RegularVenue where
  claims : List Claim
  substantialPartDistricts : List District
  realPropertyDistricts : List District
  --h0 : ¬∃ c ∈ claims, c.defendant matches Party.foreignState _ := by decide
  --h1 : ¬∃ c ∈ claims, c.againstOfficerOrEmployeeOfTheUs := by decide


@[reducible]
abbrev RegularVenue.b1 (r : RegularVenue) : List District :=
  /- All districts in which the defendants reside -/
  let defendantResidencies := r.claims.map Claim.defendantResidencies
  /- All states in which the defendants reside -/
  let defendantResidenciesStates := defendantResidencies.map (fun l => l.map District.stateOrTerritory)
  /- The state or states in which all defendants reside -/
  let inter := defendantResidenciesStates.Inter
  (defendantResidencies.join.filter (fun x => x.stateOrTerritory ∈ inter)).dedup

@[reducible]
abbrev RegularVenue.b2 (r : RegularVenue) := r.substantialPartDistricts ++ r.realPropertyDistricts

@[reducible]
abbrev RegularVenue.b3 (r : RegularVenue) := 
  r.claims.bind Claim.defendantSubjectToPersonalJurisdictionIn 

def RegularVenue.properVenues (r : RegularVenue) : List District :=
  List.dedup <| 
    match r.b1 ++ r.b2 with
    | [] => r.b3
    | owise => owise

def RegularVenue.properVenues' (r : RegularVenue) : StateT Log Id (List District) := do
  let base := r.b1 ++ r.b2
  if !base.isEmpty
  then
    info s!"Under 28 U.S.C. § 1391(b)(1-2), venue is proper in these districts: {base.map District.fullName}"
    return base
  else
    let b3 := r.b3
    info s!"Under 28 U.S.C. § 1391(b)(3), venue is proper in these districts: {b3.map District.fullName}"
    return b3

def properVenuesAux (claims : List Claim) : List District := 
  sorry

def properVenues (claims : List Claim) : List District :=
  let x := (sortClaimsByDescription claims).toList.map (fun pr => pr.snd)
  (x.map properVenuesAux).Inter

  