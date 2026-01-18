CRealsFast: executable computable reals (dyadic + ball arithmetic)
===============================================================

`CReals/CRealsFast.lean` provides a **purely executable** core under `namespace Computable.Fast`:

- `Dyadic`: an exact dyadic rational (`man : Int`, `exp : Int`, meaning `man * 2^exp`)
- `Ball`: interval/ball arithmetic `[mid ± rad]` over dyadics
- `FastReal`: a precision-indexed oracle `ℕ → Ball`

Design notes
------------

- **No quotients, no `noncomputable`**: the core is designed to be usable with `#eval`.
- **Directed rounding**: `Dyadic.roundDown/roundUp` and `Dyadic.divDown/divUp` are used to build
  safe interval enclosures where needed.
- **Explicit partiality where required**: some operations are not computable as total functions on
  all computable reals (notably reciprocal/division and functions with discontinuities such as
  `log` and `tan`). These are exposed as partial approximators returning `Option`:
  - `Ball.inv?`, `Ball.div?`, `Ball.log?`, `Ball.tan?`
  - `FastReal.inv?`, `FastReal.div?`, `FastReal.log?`, `FastReal.tan?` (each is `ℕ → Option Ball`)

Quick smoke test
----------------

See `CReals/CRealsFastExamples.lean` for end-to-end `#eval` and `decide` usage.

For exact (non-`Float`) output in `#eval`, use:

- `FastReal.toDecimal`
- `FastReal.toDecimalInterval`
