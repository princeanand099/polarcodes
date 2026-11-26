/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.OperationalCorollary55
import PolarCodes.DivergenceCharacterizations
import PolarCodes.RankDeficientFrenkel
import PolarCodes.ChannelDualityEquiv
import PolarCodes.Refinements
import PolarCodes.MainTheorem

/-!
# Kernel Axiom Audit

Verifies that every headline theorem in `PolarCodes` depends strictly on the three standard
Lean 4 / Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) with zero `sorryAx` or
custom axioms.
-/

#print axioms PolarCodes.theorem_1_1_quantum_polar_poly_blocklength
#print axioms PolarCodes.theorem_1_1_coding_poly_blocklength
#print axioms PolarCodes.wilde_guha_qsc_avg_bound
#print axioms PolarCodes.wilde_guha_qsc_bound
#print axioms PolarCodes.theorem_1_2_a_bhattacharyya_contraction
#print axioms PolarCodes.theorem_1_2_b_entropy_contraction
#print axioms PolarCodes.theorem_1_3_dephasing_sdpi
#print axioms PolarCodes.theorem_1_3_equatorial_equality
#print axioms PolarCodes.theorem_1_3_dephasing_sdpi_relEntropy
#print axioms PolarCodes.theorem_1_3_equatorial_equality_relEntropy
#print axioms PolarCodes.corollary_5_5_quantum_private_polar_coding
#print axioms PolarCodes.corollary_5_5_operational_quantum_private_polar_coding
#print axioms PolarCodes.exists_wiretap_frozen_good
#print axioms PolarCodes.exists_coherent_css_decoder
#print axioms PolarCodes.lemma_3_2_hockeyStick_measure
#print axioms PolarCodes.lemma_3_2_hockeyStick_measure_equalSupport
#print axioms PolarCodes.lemma_4_1_gram_dephasing
#print axioms PolarCodes.lemma_4_1_gram_dephasing_relEntropy
#print axioms PolarCodes.fuchs_van_de_graaf
#print axioms PolarCodes.hockeyStick_variational_eq
#print axioms PolarCodes.relEntropy_frenkel_integral_suppSubset
#print axioms PolarCodes.relEntropy_hockeyStick_integral_suppSubset
#print axioms PolarCodes.qjs_eq_avg_relEntropy
#print axioms PolarCodes.relEntropy_eq_zero_iff
#print axioms PolarCodes.qjs_mem_Icc
#print axioms PolarCodes.qjs_eq_zero_iff
#print axioms PolarCodes.qjs_eq_one_iff
#print axioms PolarCodes.rootFidelity_block_diagonal
#print axioms PolarCodes.prop_2_2_D2_var_isoEquiv
