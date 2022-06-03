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
import JohnDoe.Federal.CivilProcedure.Pleading.Complaint

/-
Rule 4
-- (e) is serving an individual within a judicial district of the US
-- (f) is the 'service in a foreign country' stuff.
-- (g) is serving a minor or incompetent person
-- (h) is serving a corporation or unincorporated association
-- (i) is serving the US, agencies, employees
-- (j) is serving a foreign, state, or local government.
-/
inductive ServiceKind
| e1
| e2a
| e2b
| e2c
| f1
| f2A
| f2B
| f2Ci
| f2Cii
| f3
| g
| h1A
| h1B
| h2
| i1
| i2
| i3
| j1
| j2A
| j2B
| condemnation -- AKA «71.1d3a» 
deriving DecidableEq, Hashable, Repr

structure ServiceWaiverRequest (i : DiversityInterpretation) where
  complaint : Complaint i
  h : complaint.isFiled
  /- Defendant (or recipient if different) -/
  recipient : String
  defendantIsInUsJudicialDistrict : Bool
  originationDate : ScalarDate
  plaintiffOrPlaintiffsAttorneyName : String
  address : String
  email : String
  phone : String
deriving Repr

def ServiceWaiverRequest.formNumber : String := "AO 398"

section Service
variable {i : DiversityInterpretation} 

instance : ToString (ServiceWaiverRequest i) where
  toString request :=
    s!"UNITED STATES DISTRICT COURT FOR THE {request.complaint.district.fullName}\n"++
    s!"Civil Action No. {request.complaint.caseNum}\n\n"++
    s!"To {request.recipient}:\n" ++
    "Why are you getting this?\n" ++
    "A lawsuit has been filed against you, or the entity you represent, in this court under the number shown above. A copy of the complaint is attached.\n" ++
    s!"This is not a summons, or an official notice from the court. It is a request that, to avoid expenses, you waive formal service of a summons by signing and returning the enclosed waiver. To avoid these expenses, you must return the signed waiver within {if request.defendantIsInUsJudicialDistrict then 30 else 60} days from the date shown below, which is the date this notice was sent. Two copies of the waiver form are enclosed, along with a stamped, self-addressed envelope or other prepaid means for returning one copy. You may keep the other copy.\n" ++
    "What happens next?\n" ++
    "If you return the signed waiver, I will file it with the court. The action will then proceed as if you had been served on the date the waiver is filed, but no summons will be served on you and you will have 60 days from the date this notice is sent (see the date below) to answer the complaint (or 90 days if this notice is sent to you outside any judicial district of the United States).\n" ++
    "If you do not return the signed waiver within the time indicated, I will arrange to have the summons and complaint served on you. And I will ask the court to require you, or the entity you represent, to pay the expenses of making service.\n" ++
    "Please read the enclosed statement about the duty to avoid unnecessary expenses.\n" ++
    "I certify that this request is being sent to you on the date below.\n\n" ++
    s!"Date: {reprStr request.originationDate}\n" ++
    s!"{request.plaintiffOrPlaintiffsAttorneyName}\n" ++
    s!"{request.address}\n" ++
    s!"{request.email}\n" ++
    s!"{request.phone}"

structure ServiceWaiverResponse where
  request : ServiceWaiverRequest i
  date : ScalarDate
  defendantOrAttorneyName : String
  address : String
  email : String
  phone : String
deriving Repr

def ServiceWaiverResponse.formNumber : String := "AO 399"

instance : ToString (@ServiceWaiverResponse i) where
  toString response := 
    s!"UNITED STATES DISTRICT COURT FOR THE {response.request.complaint.district.fullName}\n"++
    s!"Civil Action No. {response.request.complaint.caseNum}\n\n"++
    s!"To {response.request.complaint.namedPlaintiff.name}:\n" ++
    s!"I have received your request to waive service of a summons in this action along with a copy of the complaint, two copies of this waiver form, and a prepaid means of returning one signed copy of the form to you.\n" ++
    s!"I, or the entity I represent, agree to save the expense of serving a summons and complaint in this case.\n" ++
    s!"I understand that I, or the entity I represent, will keep all defenses or objections to the lawsuit, the court’s jurisdiction, and the venue of the action, but that I waive any objections to the absence of a summons or of service.\n" ++
    s!"I also understand that I, or the entity I represent, must file and serve an answer or a motion under Rule 12 within 60 days from {reprStr response.request.originationDate}, the date when this request was sent (or 90 days if it was sent outside the United States). If I fail to do so, a default judgment will be entered against me or the entity I represent.\n\n" ++
    s!"Date: {reprStr response.date}\n" ++
    s!"{response.defendantOrAttorneyName}\n" ++
    s!"{response.address}\n" ++
    s!"{response.email}\n" ++
    s!"{response.phone}"

inductive ServiceTimeLimit
| standard : ServiceTimeLimit
| serviceInForeignCountry : ServiceTimeLimit
| condemnation : ServiceTimeLimit

structure Summons where
  complaint : FiledComplaint
  defendant : PartyInfo
  appearanceWindow : ScalarDate × ScalarDate
  defaultWarning : String

end Service

