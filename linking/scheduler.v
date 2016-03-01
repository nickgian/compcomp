Require Import AST.

(*THREADS*)
Module Type ThreadID.
  Parameter tid: Set.
End ThreadID.

Module NatTID <: ThreadID.
  Definition tid:= nat.
End NatTID.

(*SCHEDULERS*)
Module Type Scheduler (TID:ThreadID).
  Import TID.
  Parameter schedule : Type.
  Parameter schedPeek: schedule -> option tid.
  Parameter schedSkip: schedule -> schedule.
End Scheduler.

Module ListScheduler (TID:ThreadID) <: Scheduler TID .
  Import TID.
  Definition schedule:= list tid.
  Definition schedPeek (sc:schedule):= @List.hd_error tid sc.
  Definition schedSkip (sc:schedule): schedule:= @List.tl tid sc.
End ListScheduler.