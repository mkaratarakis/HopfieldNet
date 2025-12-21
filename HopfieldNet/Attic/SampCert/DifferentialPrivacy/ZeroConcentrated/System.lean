/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import HopfieldNet.SampCert.DifferentialPrivacy.Abstract
import HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Basic
import HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.AdaptiveComposition
import HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing
import HopfieldNet.SampCert.DifferentialPrivacy.ZeroConcentrated.Const

/-!
# zCDP System

This file contains an instance of an abstract DP system associated to the discrete gaussian mechanisms.
-/

namespace SLang

variable { T : Type }

/--
Instance of a DP system for zCDP, using the discrete Gaussian as a noising mechanism.
-/
noncomputable instance gaussian_zCDPSystem : DPSystem T where
  prop := zCDP
  prop_adp := zCDP_ApproximateDP
  prop_mono := zCDP_mono
  noise := privNoisedQuery
  noise_prop := privNoisedQuery_zCDP
  adaptive_compose_prop := privComposeAdaptive_zCDP
  postprocess_prop := privPostProcess_zCDP
  const_prop := privConst_zCDP

end SLang
