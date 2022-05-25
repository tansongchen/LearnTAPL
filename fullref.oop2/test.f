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

DoubleBackupCounter = {get:Unit -> Nat, inc:Unit -> Unit, reset:Unit -> Unit, backup: Unit -> Unit, reset2:Unit -> Unit, backup2: Unit -> Unit};
DoubleBackupCounterRep = {x: Ref Nat, b: Ref Nat, b2: Ref Nat};

doubleBackupCounterClass = lambda r:DoubleBackupCounterRep.
  let super = backupCounterClass r in {
    get = super.get,
    inc = super.inc,
    reset = super.reset,
    backup = super.backup,
    reset2 = lambda _:Unit. r.x:=!(r.b2),
    backup2 = lambda _:Unit. r.b2:=!(r.x)
  };

newDoubleBackupCounter = lambda _:Unit. let r = {x=ref 1, b=ref 1, b2=ref 1} in doubleBackupCounterClass r;

db = newDoubleBackupCounter unit;

db.inc unit;
db.get unit;
db.backup unit;
db.inc unit;
db.get unit;
db.backup2 unit;
db.inc unit;
db.reset2 unit;
db.get unit;
db.reset unit;
db.get unit;
