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
