/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.ContinuityAssembly
import QuantumChannelContinuity.StateOrder

/-!
# Theorem 1 for finite-dimensional quantum channels

The two-sided order-one limit holds for every pair of CPTP channels between
nonzero finite-dimensional complex Hilbert spaces. All state, order, support,
slack-attainment, Stinespring/filter, Schatten, and regularization ingredients
are proved. There are no additional quantum-information premises.

The regularized quantities use positive-block suprema; the theorems
`blockRenyi_tendsto_regularized` and `blockRelative_tendsto_regularized`
identify these with the manuscript's normalized block limits, including infinity.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

theorem inputRenyi_monotoneOn_left (N M : CPTP H K) (i : BlockInput H) :
    MonotoneOn (fun α => inputRenyi N M α i) (Ioo (1 / 2) 1) := by
  intro α hα β hβ hαβ
  exact ENNReal.div_le_div_right (EReal.toENNReal_le_toENNReal
    (stateRenyi_monotoneOn_left
      (amplifiedOutput (channelPower N i.1.val) i.2.density)
      (amplifiedOutput (channelPower M i.1.val) i.2.density) hα hβ hαβ)) _

theorem inputRenyi_monotoneOn_right (N M : CPTP H K) (i : BlockInput H) :
    MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1) := by
  intro α hα β hβ hαβ
  exact ENNReal.div_le_div_right (EReal.toENNReal_le_toENNReal
    (stateRenyi_monotoneOn_right
      (amplifiedOutput (channelPower N i.1.val) i.2.density)
      (amplifiedOutput (channelPower M i.1.val) i.2.density) hα hβ hαβ)) _

/-- Every field of the earlier finite-case interface is now constructed
from the sole finite-case condition on the actual relative entropy. -/
noncomputable def quantumThresholdInputs (N M : CPTP H K)
    (hfin : regularizedRelative N M ≠ ⊤) : QuantumThresholdInputs N M :=
  quantumThresholdInputs_of_mono N M hfin (inputRenyi_monotoneOn_right N M)

/-- Theorem 1: unconditional two-sided continuity at order one for actual
regularized, stabilized sandwiched Rényi channel divergence, in bits.
The value may be finite or infinite; no support or finiteness hypothesis is needed. -/
theorem theorem_one (N M : CPTP H K) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) :=
  theorem_one_of_input_order N M
    (inputRenyi_monotoneOn_left N M) (inputRenyi_monotoneOn_right N M)

end QuantumChannelContinuity
