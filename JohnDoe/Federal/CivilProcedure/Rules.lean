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
import JohnDoe.Federal.CivilProcedure.Pleading.Answer
import JohnDoe.Federal.CivilProcedure.Motion
import JohnDoe.Federal.CivilProcedure.Deadline
import JohnDoe.Federal.CivilProcedure.CivilAction

open Std (HashMap)

set_option autoImplicit false

structure SjmCheck where
  identifier : String
  check : CivilAction → Prop
  inst : DecidablePred check 

instance : Repr SjmCheck := ⟨fun x => reprPrec x.identifier⟩
instance (ck : SjmCheck) : DecidablePred ck.check := ck.inst

@[reducible]
def trueSjmCheck : SjmCheck := {
  identifier := "true"
  check := fun _ => True
  inst := inferInstance
}


inductive RuleTag
| fileComplaint
| serveProcess
| waiveService
| extendSummonsDeadline
| dismissParty
--| fileAnswer
--| fileReply
--| rule12Motion
--| fileMotion

structure FileComplaint where
  complaint : Complaint
  filedOn : NaiveDateTime
  header : PleadingHeader
  h : header.pleadingDesignation = .complaint := by decide
deriving Repr

structure DismissParty where
  dateTime : NaiveDateTime
  party : Party

structure ExtendSummonsDeadline where
  dateTime : NaiveDateTime
  defendant : Party
  goodReason : Option String
  extension : Option Bool
  
structure ServeProcess where
  dateTime : NaiveDateTime
  summons : Summons
  kind : ServiceKind
deriving Repr

structure WaiveService where
  dateTime : NaiveDateTime
  waiver : ServiceWaiverResponse
deriving Repr

structure FileAnswer where
  dateTime : NaiveDateTime
  answer : Answer

/- Not sure what hte proper way to do this is. -/
structure Rule12Motion where
  dateTime : NaiveDateTime
  answer : Answer

structure FileCounterclaim where
  dateTime : NaiveDateTime
  val : Bool

@[reducible]
def RuleTag.ctorArgType : RuleTag → Type
| .fileComplaint => FileComplaint
| .serveProcess => ServeProcess
| .waiveService => WaiveService
| .extendSummonsDeadline => ExtendSummonsDeadline
| .dismissParty => DismissParty


@[reducible]
def StepRecord := Sigma RuleTag.ctorArgType

--PGM is the whole thing
--σ is (past steps × currentStateSummary), which is `History`.
structure History where
  /- Transactions already executed -/
  priorSteps : List StepRecord
  /- The current state -/
  civilAction : CivilAction
  sjmCheck : SjmCheck

class Step (A : Type) where
  dateTime (args : A) : NaiveDateTime
  precondition (args : A) (history : History) : Prop
  inst0 (args) (history) : Decidable (precondition args history)
  takeStep (args : A) (history : History) (h : precondition args history) : CivilAction

instance : Step FileComplaint where
  dateTime := FileComplaint.filedOn
  precondition (args) (history) := 
    history.civilAction.status = .uninitiated 
    ∧ args.complaint.venue ∈ properVenues (args.complaint.claims)
  inst0 := inferInstance
  takeStep (args) _ _ := 
    {
      dateTime := args.filedOn
      status := .complaintFiled
      venue := args.complaint.venue
      complaint := { 
        args.complaint with 
        header := args.header
        filedOn := args.filedOn 
        h := args.h
      }
      claims := args.complaint.claims
      parties := 
        (args.complaint.plaintiffs ++ args.complaint.defendants).foldl 
        (init := HashMap.empty) 
        (fun sink next => sink.insert next { meansOfJoinder := .complaint, status := .notServed })
      summonses := []
      serviceWaiverResponses := []
      upcomingDeadlines := []
      isSpecialProceeding := false
      removedByDefendant := false
      motionsPending := []
      motionsGranted := []
      motionsDenied := []
    }

instance : Step ServeProcess where
  dateTime := ServeProcess.dateTime
  precondition (args) (history) := 
    history.civilAction.status >= .complaintFiled
  inst0 := inferInstance
  takeStep args history h := sorry

instance : Step ExtendSummonsDeadline where
  dateTime := ExtendSummonsDeadline.dateTime
  precondition (args) (history) :=  sorry
  inst0 := sorry
  takeStep (args) history h := sorry

instance : Step DismissParty where
  dateTime := DismissParty.dateTime
  precondition (args) (history) :=
    history.civilAction.status >= .complaintFiled
  inst0 := inferInstance
  takeStep (args) history h := 
    {
      history.civilAction with
      parties := history.civilAction.parties.erase args.party
      claims := 
        history.civilAction.claims.filter 
        (fun c => ¬(c.plaintiff = args.party ∨ c.plaintiff = args.party))
    }

instance : Step WaiveService where
  dateTime := WaiveService.dateTime
  precondition (args) (history) :=
    history.civilAction.status >= .complaintFiled

  inst0 := sorry
  takeStep (args) history h := sorry

instance {t : RuleTag} : Step (t.ctorArgType) := by cases t <;> exact inferInstance

@[reducible]
abbrev StepRecord.dateTime (r : StepRecord) : NaiveDateTime := Step.dateTime r.snd

@[reducible]
abbrev StepRecord.precondition (r : StepRecord) (hist : History) : Prop :=
  Step.precondition r.snd hist ∧ hist.civilAction.dateTime <= r.dateTime

instance (r : StepRecord) (hist : History) : Decidable (Step.precondition r.snd hist) :=
  Step.inst0 r.snd hist

instance (r : StepRecord) (hist : History) : Decidable (r.precondition hist) := by 
  simp [StepRecord.precondition]; 
  exact inferInstance


@[reducible]
def StepRecord.takeStep (r : StepRecord) (hist : History) (hPre : r.precondition hist) : History :=
  {
    hist with
    priorSteps := r :: hist.priorSteps
    civilAction := 
      {
        Step.takeStep r.snd hist hPre.left
        with dateTime := r.dateTime
      }
  }
  
/-
This would have to be like on a transaciton, defining its relation
within a single txn.
-/
@[reducible]
def singleStepOperational (r : StepRecord) (hist hist' : History) : Prop :=
  ∃ (hPre : r.precondition hist), hist' = r.takeStep hist hPre

@[reducible]
def singleStepBinary (hi hi' : History) : Prop :=
  ∃ r, singleStepOperational r hi hi'

@[reducible]
def denote (r : StepRecord) : Set (History × History) :=
  { pr | ∃ r, singleStepOperational r pr.fst pr.snd }

@[reducible]
def stepsOk : List StepRecord → History → History → Prop
| [], hist, hist' => hist = hist'
| r :: tl, hist, hist' => ∃ (hPre : r.precondition hist), stepsOk tl (r.takeStep hist hPre) hist'

/- Not sure why this won't reduce. -/
instance (rs : List StepRecord) (hi hi' : History) : Decidable (stepsOk rs hi hi') := by
  simp [stepsOk]; sorry

@[reducible]
def rule4mAux (r : StepRecord) (d : Party) : Prop :=
  match r with
  | ⟨.dismissParty, args⟩ => args.party = d
  | ⟨.extendSummonsDeadline, args⟩ => args.defendant = d
  | ⟨.serveProcess, args⟩ => args.summons.servedParty = d
  | ⟨.waiveService, args⟩ => args.waiver.servedParty = d
  | _ => False

instance (r : StepRecord) (p : Party)  : Decidable (rule4mAux r p) := by
  simp [rule4mAux]; split <;> exact inferInstance

/-
The invariant imposed by rule 4(m); within 90 days of the complaint being
filed, all defendants mentioned therein must be served (unless they need to be served
in a manner required by service in a foreign country), dismissed, or the deadline extended.

Rule 4(m)
Three day mail doesn't apply to this since nobody's been served yet.
-/
@[reducible]
def History.rule4m (hist : History) : Prop :=
  let deadline := 
    @FrcpPeriod.mk 
      hist.civilAction.venue 
      (setOn := ⟨hist.civilAction.complaint.filedOn⟩)
      (direction := .forward) 
      (.days (numDays := 90) (isElectronicFiling := false) (lastDayEnds := .midnight))
      (threeDayMail := false)
  deadline.lapsedRelativeTo hist.civilAction.dateTime ∧ 
    ∀ d ∈ hist.civilAction.complaint.defendants, d.foreignService ∨ ∃ r ∈ hist.priorSteps, rule4mAux r d

@[reducible]
def History.blanketPrecondition (hist : History) : Prop := 
  /- subject matter jurisdiction OK -/
  hist.sjmCheck.check hist.civilAction
  ∧ hist.rule4m

instance : DecidablePred History.blanketPrecondition := inferInstance

inductive WfPred : History → Prop
| mk
  (steps : List StepRecord) 
  (hist hist' : History)
  (h0 : WfPred hist)
  (h1 : stepsOk steps hist hist')
  (h2 : hist'.blanketPrecondition)
  : WfPred hist'

def WfH := { hist : History // WfPred hist }

@[reducible]
def doSteps : List StepRecord → EStateM String History Unit
| [] => pure ()
| r :: tl => fun hist =>
  if hPre : r.precondition hist
  then 
    doSteps tl (r.takeStep hist hPre)
  else 
    EStateM.Result.error "precondition not satisfied" hist

/- doSteps won't reduce. -/
theorem doStepsIff (rs : List StepRecord) (hist hist' : History) : 
  ((doSteps rs).run hist = EStateM.Result.ok () hist') → stepsOk rs hist hist' := by
  simp [doSteps, stepsOk]; sorry

@[reducible]
def doStepsWf : List StepRecord → EStateM String WfH Unit
| rs, wf@⟨hist, property⟩ => 
  match h0 : (doSteps rs).run hist with
  | EStateM.Result.ok _ hist' => 
    if h1 : hist'.blanketPrecondition
    then 
      have h2 := doStepsIff rs hist hist' h0
      have out : WfH := ⟨hist', WfPred.mk rs hist hist' property h2 h1⟩
      EStateM.Result.ok () out
    else EStateM.Result.error "failed precondition" wf
  | EStateM.Result.error e _ => EStateM.Result.error e wf

def fileComplaintM (args : FileComplaint) : EStateM String WfH FiledComplaint := do
  doStepsWf [⟨.fileComplaint, args⟩];
  let hist' ← get
  return hist'.val.civilAction.complaint


