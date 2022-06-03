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
import JohnDoe.Federal.CivilProcedure.Venue
import JohnDoe.Federal.CivilProcedure.Pleading.Claim

open Std (HashMap)

structure Complaint (i : DiversityInterpretation) where
  /- Filed in -/
  district : District
  division : Option { d : Division // d ∈ district.divisions }
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
  caseNum : Option Nat  
  filedOn : Option ScalarDate
  hJurisdiction : initialJurisdictionsOk i claims
  hVenue : district ∈ properVenues claims
deriving DecidableEq, Repr

def Complaint.isFiled (i : DiversityInterpretation) (c : Complaint i) := c.caseNum.isSome ∧ c.filedOn.isSome
