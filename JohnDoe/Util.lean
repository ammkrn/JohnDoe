import UsCourts.Defs
import UsCourts.Federal.Defs

instance : Repr Offset := ⟨fun x n => reprPrec x.identifier n⟩

instance (ω : Offset) : Repr (DateTime ω) := ⟨fun x n => reprPrec x.naive n⟩

theorem List.of_mem_filter {α : Type u} {p : α → Prop} [DecidablePred p] {l : List α} :
  ∀ a, a ∈ List.filter p l → p a := sorry

def List.Inter {A : Type} [DecidableEq A] : List (List A) → List A
| [] => []
| h :: t =>
  t.foldl (fun sink next => sink.inter next) h

def List.dedup {A : Type} [DecidableEq A] (l : List A) : List A :=
  l.foldl (fun sink next => if sink.contains next then sink else sink ++ [next]) []

structure Log where
  trace : List String
  info : List String
  warn : List String
  error : List String
deriving Repr

def Log.new : Log := {
    trace := []
    info := []
    warn := []
    error := []
}

instance : EmptyCollection Log where
  emptyCollection := Log.new

abbrev WriterT := StateT Log
abbrev Writer := StateT Log Id

abbrev trace (s : String) : Writer Unit := 
  modify (fun log => { log with trace := log.trace ++ [s] })

abbrev info (s : String) : Writer Unit := 
  modify (fun log => { log with info := log.info ++ [s] })

abbrev warn (s : String) : Writer Unit := 
  modify (fun log => { log with warn := log.warn ++ [s] })

abbrev error (s : String) : Writer Unit := 
  modify (fun log => { log with error := log.error ++ [s] })


inductive StateOrForeignState
| state : StateOrTerritoryTag → StateOrForeignState
| foreignState : String → StateOrForeignState
deriving DecidableEq, Hashable, Repr

def StateOrForeignState.getState : StateOrForeignState → Option StateOrTerritoryTag
| state t => some t
| _ => none

def StateOrForeignState.getForeignState: StateOrForeignState → Option String
| foreignState s => some s
| _ => none

instance : Coe StateOrTerritoryTag StateOrForeignState := ⟨.state⟩ 
instance : Coe String StateOrForeignState := ⟨.foreignState⟩

@[reducible]
def Bool.xor : Bool → Bool → Bool
| true, false => true
| false, true => true
| _, _ => false

@[reducible]
def Bool.nand  : Bool → Bool → Bool
| true, true => false
| _, _ => true

-- Rule 6
--(1) Period Stated in Days or a Longer Unit. When the period is
--stated in days or a longer unit of time:
--(A) exclude the day of the event that triggers the period;
--(B) count every day, including intermediate Saturdays,
--Sundays, and legal holidays; and
--(C) include the last day of the period, but if the last day
--is a Saturday, Sunday, or legal holiday, the period con-
--tinues to run until the end of the next day that is not a
--Saturday, Sunday, or legal holiday.

/-
(d.addDays n).isWeekendOrHoliday → (d.addDaysFederal n) = (d.addDays n).nextDayThatIsNotAWeekendOrLegalHoliday
-/

/-
∃ d ∈ year, ¬day is holiday ∧ ¬day.isWeekday
There's at least one day that is not a saturday or sunday,
and is not a federal holiday

2nd monday of January
-/
/- The base federal holidays defined by FRCP rule 6 -/
/-
The day you're actually at is the last day; the amount of time has already elapsed
(April, 16, 2022)

∀ (y : Year), ∃ d ∈ year, ¬weekend ∧ ¬holiday
-/


/-
Cycle through `federalHolidays`
-/

/-
rotate federalHolidays 1
rotate federalHolidays 2
-/

/-
saturday or sunday ↔ % 7 = 6 ∨ % 7 = 0 
-/
/-
The forward and backward distinctions come from the definition of "next day".

(5) ‘‘Next Day’’ Defined. The ‘‘next day’’ is determined by
continuing to count forward when the period is measured after
an event and backward when measured before an event.

E.g. "A has 90 days after being served with X" is forward.
"B must file at least 90 days before event Y" is backward.
-/
/-
∃ stopDay, ¬weekday ∧ ¬holiday ∧ d <= stopDay 
then well founded by (stopDay - d)
-/
abbrev ScalarDate.nextDayThatIsNotAWeekendOrHolidayForward (d : ScalarDate) (holidays : List Holiday) (gas : Nat := 366) : ScalarDate :=
  match gas with
  | 0 => panic! "unreachable"
  | gas+1 => 
    if 
      (holidays.map (fun h => h.date d.year)).contains d 
      ∨ d.dayOfWeek = saturday 
      ∨ d.dayOfWeek = sunday
    then nextDayThatIsNotAWeekendOrHolidayForward (d.addDays 1) holidays gas
    else d

/-
State Holidays Are Only Relevant to Forward-Counting Deadlines
A state holiday that is not also a holiday under federal law is counted as a legal 
holiday only for forward-counting deadlines (FRCP 6(a)(6)(C)). The purpose of this 
rule is to protect parties who are unsure of the effect of state holidays when they
 are computing time periods (FRCP 6 advisory committee's note to 2009 amendment).
-/
abbrev ScalarDate.nextDayThatIsNotAWeekendOrHolidayBackward (d : ScalarDate) (holidays : List Holiday) (gas : Nat := 366) : ScalarDate :=
  match gas with
  | 0 => panic! "unreachable"
  | gas+1 => 
    if 
      (holidays.map (fun h => h.date d.year)).contains d 
      ∨ d.dayOfWeek = saturday 
      ∨ d.dayOfWeek = sunday
    then nextDayThatIsNotAWeekendOrHolidayBackward (d.subDays 1) holidays gas
    else d

def ScalarDate.addFederalDaysForward (date : ScalarDate) (days : Nat) (holidays : List Holiday) : ScalarDate :=
  (date.addDays days).nextDayThatIsNotAWeekendOrHolidayForward holidays

def NaiveDateTime.mkEndOfDayDeadlineForward (start : NaiveDateTime) (days : Nat) (venue : District) : NaiveDateTime := sorry

abbrev NaiveDateTime.nextDayThatIsNotAWeekendOrHolidayForward (d : NaiveDateTime) (holidays : List Holiday) (gas : Nat := 366) : NaiveDateTime :=
  match gas with
  | 0 => panic! "unreachable"
  | gas+1 => 
    if 
      (holidays.map (fun h => h.date d.year)).contains d.toScalarDate
      ∨ d.dayOfWeek = saturday 
      ∨ d.dayOfWeek = sunday
    then nextDayThatIsNotAWeekendOrHolidayForward (d + UnsignedDuration.fromHours 24) holidays gas
    else d

def NaiveDateTime.addFederalDaysForward (date : NaiveDateTime) (days : Nat) (holidays : List Holiday) : NaiveDateTime :=
  (date + UnsignedDuration.fromDays days).nextDayThatIsNotAWeekendOrHolidayForward holidays

def DateTime.midnightDeadline {ω : Offset} (d : DateTime ω) : DateTime ω :=
  sorry


lemma bowles_lemma : 
  (ScalarDate.fromYmd 2004 .february 10).addFederalDaysForward 14 federalHolidays 
  = (ScalarDate.fromYmd 2004 .february 24) := by rfl


def DateTime.addIgnoringLeapSeconds (t : DateTime ω) (d : SignedDuration) : DateTime ω :=
  /- The number of leap seconds applied to t -/
  let leap₁ := ω.leapSecondsToApply t.naive
  let sum := t + d
  /- The number of leap seconds applied to the sum -/
  let leap₂ := ω.leapSecondsToApply sum.naive
  /- Any "new" leap seconds that were inserted -/
  sum + (leap₁ - leap₂)




abbrev DateTime.nextDayThatIsNotAWeekendOrHolidayForward {ω : Offset} (d : DateTime ω) (holidays : List Holiday) (gas : Nat := 366) : DateTime ω :=
  match gas with
  | 0 => panic! "unreachable"
  | gas+1 => 
    if 
      /- Has to be local scalar date -/
      (holidays.map (fun h => h.date d.localYear)).contains d.localScalarDate
      ∨ d.localScalarDate.dayOfWeek = saturday 
      ∨ d.localScalarDate.dayOfWeek = sunday
    then nextDayThatIsNotAWeekendOrHolidayForward (d + UnsignedDuration.fromHours 24) holidays gas
    else d

def DateTime.addFederalTimeForward {ω : Offset} (date : DateTime ω) (duration : UnsignedDuration) (holidays : List Holiday) : DateTime ω :=
  (date + duration).nextDayThatIsNotAWeekendOrHolidayForward holidays

abbrev DateTime.nextDayThatIsNotAWeekendOrHolidayBackward {ω : Offset} (d : DateTime ω) (holidays : List Holiday) (gas : Nat := 366) : DateTime ω :=
  match gas with
  | 0 => panic! "unreachable"
  | gas+1 => 
    if 
      (holidays.map (fun h => h.date d.localYear)).contains d.localScalarDate
      ∨ d.localScalarDate.dayOfWeek = saturday 
      ∨ d.localScalarDate.dayOfWeek = sunday
    then nextDayThatIsNotAWeekendOrHolidayBackward (d - SignedDuration.fromHours 24) holidays gas
    else d

def DateTime.subFederalTimeBackward {ω : Offset} (date : DateTime ω) (duration : SignedDuration) : DateTime ω :=
  (date - duration).nextDayThatIsNotAWeekendOrHolidayBackward federalHolidays

