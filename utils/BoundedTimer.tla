---- MODULE BoundedTimer ----
\* Decreasing bounded timer.
\* Can have a value of maximum MaxTimer, where 0 means timeout and MaxTimer
\* means disabled.
EXTENDS Naturals

CONSTANT MaxTimer

ASSUME MaxTimer \in Nat /\ MaxTimer > 1

Timer == 0..MaxTimer

TimedOut(tim) == tim = 0

Disabled(tim) == tim = MaxTimer

Enabled(tim) == ~Disabled(tim) /\ ~TimedOut(tim)

TimerTick(tim) ==
    IF TimedOut(tim) \/ Disabled(tim)
    THEN tim
    ELSE tim - 1
====
