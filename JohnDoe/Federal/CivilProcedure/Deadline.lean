import Mathlib.Data.Option.Basic
import UsCourts.Defs
import UsCourts.Federal.Defs
import Timelib.Date.Basic
import Timelib.Date.ScalarDate
import Timelib.NanoPrecision.DateTime.NaiveDateTime
import Timelib.NanoPrecision.DateTime.DateTime
import Timelib.NanoPrecision.ClockTime.ClockTime
import Timelib.NanoPrecision.Duration.SignedDuration
import JohnDoe.Util
import JohnDoe.Federal.CivilProcedure.Entities
import JohnDoe.Federal.CivilProcedure.Diversity
import JohnDoe.Federal.CivilProcedure.Pleading.Claim
import JohnDoe.Federal.CivilProcedure.Pleading.Complaint
import JohnDoe.Federal.CivilProcedure.Pleading.Service
import JohnDoe.Federal.CivilProcedure.Motion

section Deadlines

/-
If add three day mail applies, you do it in days for `InDays` and 
as 72 hours for the ones in hours.
-/
inductive LastDayEnds (δ : District)
| midnight
| clerksOfficeClosing
| other (clockTime : ClockTime δ.timeZone)
deriving DecidableEq, Repr


/- 
To accommodate FRCP 6(a)(5). The two kinds of "next day" are for forward and
backward deadlines; forward is "P must be completed no more than 30 days after Q". 
Backward is "Y must be completed no fewer than 30 days before Z". These are treated
very differently in the federal rules.
-/
inductive Direction
| forward
| backward
deriving DecidableEq, Repr



inductive Period (δ : District)
| days 
  (numDays : Nat)
  (isElectronicFiling : Bool := false)
  /- For FRCP 6(a)(4) -/
  (lastDayEnds : LastDayEnds δ := 
    if isElectronicFiling 
    /- 6(a)(4)(A) -/
    then .midnight 
    /- 6(a)(4)(B) -/
    else .clerksOfficeClosing) 

| hours (numHours : Nat) : Period δ 
deriving DecidableEq, Repr

structure FrcpPeriod (δ : District) where
  setOn : DateTime δ.timeOffset
  direction : Direction
  period : Period δ 
  /- Rule 6(d) -/
  threeDayMail : Bool

section DeadlineStuff
variable {δ : District}

def LastDayEnds.set {δ : District} (d : DateTime δ.timeOffset) (l : LastDayEnds δ) : DateTime δ.timeOffset :=
  match l with
  -- 23:59:59
  | .midnight => sorry
  | .clerksOfficeClosing => sorry
  | .other t => sorry

abbrev DateTime.passHolidaysAndWeekends
  (d : DateTime δ.timeOffset) 
  (nextDay : SignedDuration)
  (holidays : List Holiday)
  --(clerksOfficeInacessible : List DateTime δ.timeOffset)
  (gas : Nat := 366) : DateTime δ.timeOffset :=
  match gas with
  | 0 => panic! "unreachable"
  | gas+1 => 
    if 
      /- Has to be local scalar date -/
      (holidays.map (fun h => h.date d.localYear)).contains d.localScalarDate
      ∨ d.localScalarDate.dayOfWeek = saturday 
      ∨ d.localScalarDate.dayOfWeek = sunday
    then 
      passHolidaysAndWeekends (d + nextDay) nextDay holidays gas
    else d

def DateTime.federalTimeAgnostic 
  (date : DateTime δ.timeOffset) 
  (duration : UnsignedDuration) 
  (direction : Direction) : DateTime δ.timeOffset :=
    match direction with
    | .forward => passHolidaysAndWeekends (date + duration) (SignedDuration.fromHours 24) federalHolidays
    | .backward => passHolidaysAndWeekends (date - duration) (SignedDuration.fromHours (-24)) δ.allRelevantHolidays

/-
FRCP 6(a)(3) has to be dealt with on a case by case basis since the clerks
office being inacessible during specific hours isn't going to be known 
in advance. 6(a)(3) is strictly lenient even for backward calculations, since 
it says that the time for filing is extended if the clerk's office is 
unavailable on the "last day" which is a defined term.
-/
def FrcpPeriod.okOnOrBefore6a (p : FrcpPeriod δ) : DateTime δ.timeOffset :=
    match p.period with
    /- FRCP 6(a)(1) -/
    | .days numDays _ lastDayEnds => 
      let lastDay := p.setOn.federalTimeAgnostic (UnsignedDuration.fromDays numDays) p.direction
      /- FRCP 6(a)(4) -/
      lastDayEnds.set lastDay
    /- FRCP 6(a)(2) -/
    | .hours numHours =>  p.setOn.federalTimeAgnostic (UnsignedDuration.fromHours numHours) p.direction
  
def FrcpPeriod.okOnOrBefore (p : FrcpPeriod δ) : DateTime δ.timeOffset :=
  if p.threeDayMail
  then p.okOnOrBefore6a.federalTimeAgnostic (UnsignedDuration.fromDays 3) .forward
  else p.okOnOrBefore6a

@[reducible]
def FrcpPeriod.lapsedRelativeTo (p : FrcpPeriod δ) (t : NaiveDateTime) : Prop :=
  p.okOnOrBefore.naive < t


end DeadlineStuff