import NeuralNetwork.NeuralNetwork.ComputableRealsBridge
import HopfieldNet.CReals.SOTA

/-!
# NeuralNetwork ↔ SOTA CReals integration

This file provides the missing instances so that the implementation-parametric computable reals
(`Computable.CRealAQ AQ`) can be used as a scalar type in NeuralNetwork developments that
only require a principled bridge into `ℝ` for analysis (via `HasToReal` / `HasToRealOrder`).
-/

namespace NeuralNetwork

open Computable

noncomputable instance {AQ : Type} [ApproxRationals AQ] :
    HasToReal (Computable.CRealAQ AQ) where
  toRealRingHom := Computable.CRealsSOTA.toRealRingHom (AQ := AQ)

noncomputable instance {AQ : Type} [ApproxRationals AQ] :
    HasToRealOrder (Computable.CRealAQ AQ) where
  mono_toReal := by
    intro a b hab
    -- Delegate to the monotonicity lemma in the SOTA façade.
    simpa using (Computable.CRealsSOTA.toReal_mono (AQ := AQ) hab)

end NeuralNetwork
