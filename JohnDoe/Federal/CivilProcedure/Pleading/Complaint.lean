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
import JohnDoe.Federal.CivilProcedure.Venue
import JohnDoe.Federal.CivilProcedure.Pleading.Defs
import JohnDoe.Federal.CivilProcedure.Pleading.Claim

open Std (HashMap)

structure Complaint where
  venue : District
  division : Option { d : Division // d ∈ venue.divisions }
  claims : List Claim
  namedPlaintiff : Party
  plaintiffsAttorneys : List AttorneyInfo
  namedDefendant : Party
  intro : String
  jurisdictionStatement : String
  venueStatement : String
  facts : List String
  prayerForRelief : List String
  requestingJuryTrial : Bool
deriving DecidableEq, Repr

@[reducible]
def Complaint.plaintiffs (c : Complaint) : List Party :=
  (c.claims.map (Claim.plaintiff)).dedup

@[reducible]
def Complaint.defendants (c : Complaint) : List Party :=
  (c.claims.map (Claim.defendant)).dedup

structure FiledComplaint extends Complaint where
  header : PleadingHeader
  filedOn : NaiveDateTime 
  h : header.pleadingDesignation = .complaint := by decide
deriving DecidableEq, Repr

@[reducible]
def FiledComplaint.caseNum (c : FiledComplaint) : Nat := 
  c.header.caseNum

instance : Inhabited FiledComplaint where
  default := sorry
--{
--  venue
--  division := none
--  claims := []
--  namedPlaintiff := []
--  plaintiffsAttorneys := []
--  namedDefendant := johnDoe
--  intro := ""
--  jurisdictionStatement := ""
--  venueStatement := ""
--  facts := []
--  prayerForRelief := []
--  requestingJuryTrial := false
--}

inductive addInitialClaim (i : DiversityInterpretation) : Claim → Complaint → Complaint → Prop
| mk cl c c' : addInitialClaim i cl c c'
