module

public import FlatShuffler.Unit.Defs
import all FlatShuffler.Unit.Defs
public import FlatShuffler.FlatSurplus
import all FlatShuffler.FlatSurplus
public import FlatShuffler.Sep.ExitContract
import all FlatShuffler.Sep.ExitContract

@[expose] public section

namespace FlatShuffler.Unit

open FlatShuffler.Sep

/-- The model reports an assertion error and gives the memory at the exit boundary. -/
def ExitRes (f : Flat.St → Flat.Status × Flat.St) (g g' : G) : Prop :=
  Keep g g' ∧ flat g' = (f (flat g)).2 ∧ (f (flat g)).1 = .assertionFailed

abbrev UnitThmWithExit [Host] [FunDecls] (prog : Program) (A : G → MachineData → Prop)
    (d : Nat) (Q X : G → G → MachineData → MachineData → Prop) : Prop :=
  ∀ S g F, BodyWithExit prog (Sep.Pre S g F A d)
    (fun s t => Sep.Post S F d (fun g' t => Q g g' s t) s t)
    (fun s t => Sep.Post S F d (fun g' t => X g g' s t) s t)

abbrev UnitThmWWithExit [Host] [FunDecls] (prog : Program) (W : MachineData → MProp 64)
    (A : G → MachineData → Prop) (d : Nat)
    (Q X : G → G → MachineData → MachineData → Prop) : Prop :=
  ∀ S g F, BodyWithExit prog (fun s => Sep.Pre S g (W s ∗ F) A d s)
    (fun s t => Sep.Post S (W s ∗ F) d (fun g' t => Q g g' s t) s t)
    (fun s t => Sep.Post S (W s ∗ F) d (fun g' t => X g g' s t) s t)

def pushX (g g' : G) (s _t : MachineData) : Prop :=
  ExitRes (Flat.push · (StackSlot.ofWord (rsi s)) (rdx s)) g g'

def dupX (g g' : G) (s _t : MachineData) : Prop :=
  ExitRes (Flat.dup · (rsi s) (rdx s)) g g'

def produceX (g g' : G) (s _t : MachineData) : Prop :=
  ExitRes (Flat.produce · (rsi s)) g g'

def generateX (g g' : G) (s _t : MachineData) : Prop :=
  ExitRes (Flat.generate · (rsi s)) g g'

def permuteX (p : Vector Word MAX_N) (g g' : G) (_s _t : MachineData) : Prop :=
  ExitRes (Flat.permute · p) g g'

def loopX (g g' : G) (_s _t : MachineData) : Prop :=
  ExitRes Flat.buildBottomUp g g'

def surplusX (g g' : G) (_s _t : MachineData) : Prop :=
  ExitRes Flat.removeSurplus g g'

end FlatShuffler.Unit
