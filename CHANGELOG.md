0.5.1
---

Compatibility with GHC 9.4 and 9.6


0.5.0.1
---

Compatibility with GHC 9.2.1

0.5
---

The typing rules for delay, functions, and guarded recursion have been
simplified and generalised. Instead of just one tick, Rattus now
allows an arbitrary number of ticks as well as function definitions in
the scope of ticks. In practical terms, this means the following:

- As before, delays can be nested arbitrarily and function definitions
  may occur under arbitrarily many delays.
- But now the scope of a delay is no longer interrupted by a nested
  delay or function definition.

0.4
---

More general typing rules for delay, functions, and guarded recursion:

- delay and function definitions may now occur under a delay.
- Guarded recursive calls may occur at any time in the future -- not
  only exactly one time step into the future.
- As before, adv and recursive calls may only occur directly in the
  scope of delay. The scope of a delay is interrupted by adv, box,
  guarded recursive definitions, and function definitions.

Changes in the library:

- Rename applicative-style operators to avoid clash with Haskell's <*>
  operator.
- Rename types: Event -> Future; Events -> Event



0.3.1
-----

Guarded recursive types Str and Event are now fully strict (i.e. in
particular, they are strict in the component that is of a later type)
as they should be.

0.3
---

Rattus code is now checked just after GHC's type checking phase
(instead of after desugaring to Core). As a consequence, error
messages for some corner cases are much improved and we don't need
to use the -g2 compiler option anymore to get good error messages.

0.2
---

- the use of lazy data structures will now cause a warning (can be
  disabled by 'AllowLazyData' annotation); this check for lazy data is
  rather ad hoc and needs to be refined
- allow functions under ticks (but with limitations, see paper)
- strictness transformation is now similar to the 'Strict' language
  extension
- optimisations using custom rewrite rules

0.1.1.0
-------

- allow mutual guarded recursion
- improve type error messages

0.1.0.0
-------
initial release
