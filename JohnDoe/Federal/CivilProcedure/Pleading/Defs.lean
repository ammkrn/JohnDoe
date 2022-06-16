/- Rule 7(a) -/
--inductive Pleading
--| complaint : Complaint → Pleading
--| answer : Answer → Pleading
--| answerToCounterclaim : Answer → Pleading
--| answerToCrossclaim : Answer → Pleading
--| thirdPartyComplaint : Complaint → Pleading
--| answerToThirdPartyComplaint : Answer → Pleading
--| replyToAnswer (courtOrder : String) : Reply → Pleading

/- Rule 7(a); e.g. the form requires that all pleadings carry a 7(a) designation by rule 10 -/
inductive PleadingDesignation
| complaint
| answer
| answerToCounterclaim
| answerToCrossclaim
| thirdPartyComplaint
| answerToThirdPartyComplaint
| replyToAnswer
deriving DecidableEq, Repr

/-
The title of the complaint must name all the parties;
the title of other pleadings, after naming the first party on each
side, may refer generally to other parties.
-/
structure PleadingHeader where
  courtName : String
  title : String
  pleadingDesignation : PleadingDesignation
  /- For the complaint, this will be done by the clerk's office. -/
  caseNum : Nat
deriving DecidableEq, Repr