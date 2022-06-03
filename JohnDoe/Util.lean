import UsCourts.Defs
import UsCourts.Federal.Defs

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