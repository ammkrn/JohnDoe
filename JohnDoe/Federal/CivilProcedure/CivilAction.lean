import Mathlib.Data.Option.Basic
import Mathlib.Init.Algebra.Order
import UsCourts.Defs
import UsCourts.Federal.Defs
import Timelib.Date.Basic
import Timelib.Date.ScalarDate
import Timelib.NanoPrecision.DateTime.NaiveDateTime
import Timelib.NanoPrecision.DateTime.DateTime
import Timelib.NanoPrecision.Duration.SignedDuration
import JohnDoe.Util
import JohnDoe.Federal.CivilProcedure.Entities
import JohnDoe.Federal.CivilProcedure.Diversity
import JohnDoe.Federal.CivilProcedure.Pleading.Claim
import JohnDoe.Federal.CivilProcedure.Pleading.Complaint
import JohnDoe.Federal.CivilProcedure.Pleading.Service
import JohnDoe.Federal.CivilProcedure.Motion
import JohnDoe.Federal.CivilProcedure.Deadline

open Std (HashMap RBTree)


/-
The transition has to go from 
complaintFiled to summonsesIssued,
such that issueSummonses is the only available step
after filing the complaint; or you can do request waiver I guess.
-/
inductive Status
/- An action is -/
| uninitiated
| complaintFiled
| summonsesIssued
| serviceWaiverSent
| servedOrWaived
| answered
| pleadingsClosed
| pretrialClosed
| finalJudgmentEntered
| appealClosed
| enforcementComplete
| dismissedWithoutPrejudice
| dismissedWithPrejudice
| dismissed
| transferred
| remanded
| settled
deriving Repr, DecidableEq, Ord

instance : LE Status := leOfOrd
instance : LT Status := ltOfOrd
instance (t₁ t₂ : Status) : Decidable (t₁ <= t₂) := inferInstance
instance (t₁ t₂ : Status) : Decidable (t₁ < t₂) := inferInstance

@[simp]
theorem Status.lt_irrefl (s : Status) : ¬s < s := sorry

abbrev Status.pleading (s : Status) := s < pleadingsClosed
abbrev Status.pretrial (s : Status) := pleadingsClosed <= s ∧ s < pretrialClosed
abbrev Status.trial (s : Status) := pretrialClosed <= s ∧ s < finalJudgmentEntered
abbrev Status.appeal (s : Status) := finalJudgmentEntered <= s ∧ s < appealClosed
abbrev Status.enforcement (s : Status) := finalJudgmentEntered <= s ∧ s < enforcementComplete

inductive MeansOfJoinder where
| complaint
-- Required joinder of parties.
| rule14
| rule18
| rule19 (joinderSpoilsVenue : Bool)
| rule20
-- intervention
| rule24
deriving DecidableEq, Hashable, Repr

inductive PartyStatus_ 
| notServed
| dismissed
| servedOn
| waivedOn
deriving DecidableEq, Hashable, Repr

structure PartyStatus where
  meansOfJoinder : MeansOfJoinder
  status : PartyStatus_
deriving DecidableEq, Hashable, Repr

inductive ComplaintServiceStatus
| served : Summons → ComplaintServiceStatus
| waived : ServiceWaiverResponse → ComplaintServiceStatus
| extended 
| stock 
| dismissed
deriving Repr

structure ComplaintServiceMap (parties :  HashMap Party PartyStatus) (c : FiledComplaint) where
  map : HashMap Party ComplaintServiceStatus

structure CivilAction where
  status : Status
  venue : District
  dateTime : NaiveDateTime
  parties : HashMap Party PartyStatus
  complaint : FiledComplaint
  summonses : List Summons
  serviceWaiverResponses : List ServiceWaiverResponse
  claims : List Claim
  removedByDefendant : Bool
  motionsPending : List Motion
  motionsGranted : List Motion
  motionsDenied : List Motion
  upcomingDeadlines : List (FrcpPeriod venue)
  /-
  Need this for e.g. rule 71.1 service of process; special proceeding for condemnation by eminent domain.
  APPLICABILITY OF OTHER RULES. These rules govern proceed-
  ings to condemn real and personal property by eminent domain,
  except as this rule provides otherwise.
  -/
  isSpecialProceeding : Bool


def CivilAction.empty (venue : District) : CivilAction := 
sorry
--{
--  status := .uninitiated
--  venue
--  dateTime := Inhabited.default
--  parties := ∅ 
--  complaint := Inhabited.default
--  summonses := []
--  serviceWaiverResponses := []
--  claims := []
--  removedByDefendant := false
--  motionsPending := []
--  motionsGranted := []
--  motionsDenied := []
--  upcomingDeadlines := []
--}

@[reducible]
def CivilAction.partyStatus (action : CivilAction) (party : Party) : Option PartyStatus :=
  action.parties.find? party

@[reducible]
def CivilAction.dismissedOrRemanded (action : CivilAction) : Prop :=
  match action.status with
  | .dismissedWithoutPrejudice | .dismissedWithPrejudice | .remanded => True
  | _ => False


@[reducible]
def CivilAction.servedOrWaived (action : CivilAction) (p : Party) : Prop :=
  (∃ su ∈ action.summonses, su.servedParty = p)
  ∨ (∃ waiver ∈ action.serviceWaiverResponses, waiver.servedParty = p)


@[reducible]
def CivilAction.dismissAgainstDefendant (action : CivilAction) (d : Party) (withPrejudice : Bool) : CivilAction :=
  {
    action with
    claims := action.claims.filter (fun c => c.defendant != d)
  }
