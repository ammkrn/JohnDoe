import Mathlib.Data.Option.Basic
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

open Std (HashMap)

inductive Status
| complaintUnfiled
| complaintFiled
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
| transferred
| remanded
| settled
deriving Repr, DecidableEq, Ord

instance : LE Status := leOfOrd
instance : LT Status := ltOfOrd
instance (t₁ t₂ : Status) : Decidable (t₁ <= t₂) := inferInstance
instance (t₁ t₂ : Status) : Decidable (t₁ < t₂) := inferInstance

abbrev Status.pleading (s : Status) := s < pleadingsClosed
abbrev Status.pretrial (s : Status) := pleadingsClosed <= s ∧ s < pretrialClosed
abbrev Status.trial (s : Status) := pretrialClosed <= s ∧ s < finalJudgmentEntered
abbrev Status.appeal (s : Status) := finalJudgmentEntered <= s ∧ s < appealClosed
abbrev Status.enforcement (s : Status) := finalJudgmentEntered <= s ∧ s < enforcementComplete

inductive MeansOfJoinder where
| original
-- Required joinder of parties.
| rule14
| rule18
| rule19
| rule20
-- intervention
| rule24
deriving DecidableEq, Hashable, Repr

structure CivilAction where
  i : DiversityInterpretation
  status : Status
  parties : HashMap Party MeansOfJoinder
  claims : List Claim
  complaint : Complaint i
  summonses : List Summons

@[reducible]
def CivilAction.isNew (action : CivilAction) : Prop :=
  action.status = .complaintUnfiled
  ∧ action.parties = HashMap.empty
  ∧ action.claims = []
  ∧ action.summonses = []

def CivilAction.plaintiffs (s : CivilAction) : List Party :=
  (s.claims.bind Claim.plaintiffs).dedup

def CivilAction.defendants (s : CivilAction) : List Party :=
  (s.claims.bind Claim.defendants).dedup

--def CivilAction.joinDefendantToClaim
--  (s : CivilAction)
--  (d : Party)
--  (c : Claim)
--  (means : MeansOfJoinder)
--  (h0 : c ∈ s.claims := by decide)
--  (h1 : (s.parties.find? d).isNone := by decide)
--  (h2 : means ≠ .rule20 := by decide)
--  : CivilAction :=
--  {
--    s with
--    claims := s.claims.replace c { c with defendants := d :: c.defendants }
--    parties :=  s.parties.insert d means
--  }

def CivilAction.joinClaim 
  (s : CivilAction) 
  (c : Claim) 
  (h0 : ¬c ∈ s.claims := by decide) : CivilAction :=
  --let pMeans := 
  let withPlaintiff := 
    if (s.parties.find? c.namedPlaintiff).isSome 
    then s.parties
    else s.parties.insert c.namedPlaintiff .rule20
  let defendantsInClaimNotYetJoined := c.defendants.filter (fun d => (s.parties.find? d).isNone)
  let withDefendants :=
    defendantsInClaimNotYetJoined.foldl (fun sink next => sink.insert next .rule20) withPlaintiff
  {
    s with
    claims := c :: s.claims
    /- If this plaintiff isn't already in the mix, join them via 20a1. -/
    parties := withDefendants
  }

def CivilAction.joinRequired (s : CivilAction) (party : Party) (h : ¬s.parties.contains party := by decide) :=
  { s with parties := s.parties.insert party .rule19 }


