import HopfieldNet.CReals.CRealsFast

/-!
# FastReal embeddings for rationals (executable)

This file provides an executable embedding of `ℚ` into `Computable.Fast.FastReal`
as certified *interval enclosures*.

At requested precision index `n`, we produce a dyadic interval `[lo, hi]` such that
`lo ≤ q < hi` and the width is exactly one ulp at the chosen internal precision.

This is a pragmatic bridge for making TwoState examples over `ℚ` immediately runnable.
-/

namespace Computable.Fast
namespace FastReal

open Computable.Fast

/-!
`FastReal` is `ℕ → Ball`. We use `Dyadic.approxRat` (flooring) and add one ulp.

Note: we deliberately use an internal `k = n + 6` to give breathing room for later operations.
-/
def ofRat (q : ℚ) : FastReal := fun n =>
  let k : Nat := n + 6
  let prec : Int := -((n : Int) + 2)
  let lo : Dyadic := Dyadic.approxRat q k
  let ulp : Dyadic := ⟨1, -((k : Int))⟩
  let hi : Dyadic := lo + ulp
  Ball.ofInterval lo hi prec

end FastReal
end Computable.Fast
