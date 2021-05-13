Counter = {get:Unit -> Nat, inc:Unit -> Unit};
CounterRep = {x: Ref Nat};

counterClass = lambda r:CounterRep.
{get = lambda _:Unit. !(r.x),
inc = lambda _:Unit. r.x:=succ(!(r.x))};

newCounter =
lambda _:Unit. let r = {x=ref 1} in
                       counterClass r;

resetCounterClass = lambda r:CounterRep.
      let super = counterClass r in
        {get   = super.get,
         inc   = super.inc,
reset = lambda _:Unit. r.x:=1};

newResetCounter =
lambda _:Unit. let r = {x=ref 1} in resetCounterClass r;

BackupCounter = {get:Unit -> Nat, inc:Unit -> Unit, reset:Unit -> Unit, backup: Unit -> Unit};
BackupCounterRep = {x: Ref Nat, b: Ref Nat};

backupCounterClass = lambda r:BackupCounterRep.
              let super = resetCounterClass r in
                 {get    = super.get,
inc = super.inc,
reset = lambda _:Unit. r.x:=!(r.b), backup = lambda _:Unit. r.b:=!(r.x)};

SetCounter = {get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit};

setCounterClass = lambda r:CounterRep.
lambda self: Unit -> SetCounter.
lambda _:Unit. {get = lambda _:Unit. !(r.x),
set = lambda i:Nat. r.x:=i,
inc = lambda _:Unit. (self unit).set(succ((self unit).get unit))};

newSetCounter =
lambda _:Unit. let r = {x=ref 1} in
fix (setCounterClass r) unit;

InstrCounter = {get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat};
InstrCounterRep = {x: Ref Nat, a: Ref Nat};

/* 18.11.1.1 rewrite to support counting get */

instrCounterClass = lambda r:InstrCounterRep. lambda self: Unit -> InstrCounter.
lambda _:Unit.
let super = setCounterClass r self unit in
{get = lambda _:Unit. (r.a:=succ(!(r.a)); super.get unit),
set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i), inc = super.inc,
accesses = lambda _:Unit. !(r.a)};

newInstrCounter =
lambda _:Unit. let r = {x=ref 1, a=ref 0} in
fix (instrCounterClass r) unit;

ic = newInstrCounter unit;

/* 18.11.1.2 begin to implement InstrResetCounter */

InstrResetCounter = {get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat, reset:Unit -> Unit};

instrResetCounterClass = lambda r:InstrCounterRep.
lambda self: Unit -> InstrCounter.
lambda _:Unit.
let super = instrCounterClass r self unit in
{get = super.get, set = super.set, inc = super.inc, accesses = super.accesses,
reset = lambda _:Unit. r.x := 1};

newInstrResetCounter =
lambda _:Unit. let r = {x=ref 1, a=ref 0} in
fix (instrResetCounterClass r) unit;

irc = newInstrResetCounter unit;

/* 18.11.1.3 begin to implement InstrBackupCounter */

InstrBackupCounter = {get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat, backup: Unit -> Unit};
InstrBackupCounterRep = {x: Ref Nat, a: Ref Nat, b: Ref Nat};

instrBackupCounterClass = lambda r:InstrBackupCounterRep.
lambda self: Unit -> InstrCounter.
lambda _:Unit.
let super = instrCounterClass r self unit in
{get = super.get, set = super.set, inc = super.inc, accesses = super.accesses,
reset = lambda _:Unit. r.x:=!(r.b), backup = lambda _:Unit. r.b:=!(r.x)};

newInstrBackupCounter =
lambda _:Unit. let r = {x=ref 1, a=ref 0, b=ref 0} in
fix (instrBackupCounterClass r) unit;

ibc = newInstrBackupCounter unit;
