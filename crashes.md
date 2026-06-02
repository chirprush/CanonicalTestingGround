Not sure I'll be able to reproduce, but during testing I got this panic:
```
PANIC at Canonical.fromTerm Canonical.FromCanonical:69:6: assertion violation: xs.size == t.params.size
```
I don't know which exact theorem it was from though. That being said, I would be
able to narrow it down to three if I took the set difference of all 86 constants
in the two modules with the 83 constants that actually got a benchmark entry
saved. 