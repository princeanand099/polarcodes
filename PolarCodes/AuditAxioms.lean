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
import PolarCodes.PhiAndFuchs
import PolarCodes.MrsGerberEquality

/-!
# Axiom Audit

Prints the axiom dependencies of the main theorems in `PolarCodes`.
-/

#print axioms PolarCodes.theorem_1_1_quantum_polar_poly_blocklength
#print axioms PolarCodes.theorem_1_1_coding_poly_blocklength
#print axioms PolarCodes.wilde_guha_qsc_avg_bound
#print axioms PolarCodes.wilde_guha_qsc_bound
#print axioms PolarCodes.theorem_1_2a_pure
#print axioms PolarCodes.theorem_1_2a_bsc
#print axioms PolarCodes.theorem_1_2a_classical
#print axioms PolarCodes.theorem_1_2a_bsc_equality
#print axioms PolarCodes.theorem_1_2a_pure_equality
#print axioms PolarCodes.theorem_1_2b_linear_splitting
#print axioms PolarCodes.theorem_1_2b_potential_contraction
#print axioms PolarCodes.prop_4_3_asymptotic
#print axioms PolarCodes.theorem_1_3_dephasing_sdpi
#print axioms PolarCodes.theorem_1_3_equatorial_equality
#print axioms PolarCodes.theorem_1_3_dephasing_sdpi_relEntropy
#print axioms PolarCodes.theorem_1_3_equatorial_equality_relEntropy
#print axioms PolarCodes.corollary_5_5_simultaneous_css_polarization
#print axioms PolarCodes.corollary_5_5_quantum_private_polar_coding
#print axioms PolarCodes.corollary_5_5_operational_quantum_private_polar_coding
#print axioms PolarCodes.exists_wiretap_frozen_good
#print axioms PolarCodes.exists_coherent_css_decoder
#print axioms PolarCodes.lemma_3_2_hockeyStick_measure
#print axioms PolarCodes.lemma_3_2_hockeyStick_measure_equalSupport
#print axioms PolarCodes.prop_3_3_qjjs
#print axioms PolarCodes.prop_3_3_qjjs_classical_equality
#print axioms PolarCodes.lemma_4_1_gram_dephasing
#print axioms PolarCodes.lemma_4_1_gram_dephasing_relEntropy
#print axioms PolarCodes.one_sub_rootFidelity_le_traceDist
#print axioms PolarCodes.traceDist_le_sqrt_one_sub_rootFidelity_sq
#print axioms PolarCodes.hockeyStick_isGreatest
#print axioms PolarCodes.hockeyStick_eq_sSup
#print axioms PolarCodes.vonNeumannEntropy_mem_Icc
#print axioms PolarCodes.posPartMat_mul_negPartMat
#print axioms PolarCodes.relEntropy_frenkel_integral_of_suppSubset
#print axioms PolarCodes.relEntropy_hockeyStick_integral_of_suppSubset
#print axioms PolarCodes.qjs_eq_avg_relEntropy
#print axioms PolarCodes.relEntropy_eq_zero_iff
#print axioms PolarCodes.qjs_mem_Icc
#print axioms PolarCodes.qjs_eq_zero_iff
#print axioms PolarCodes.qjs_eq_one_iff
#print axioms PolarCodes.rootFidelity_block_diagonal
#print axioms PolarCodes.prop_2_2_D2_var_isoEquiv
#print axioms PolarCodes.prop_2_2_D2_channelEquiv
#print axioms PolarCodes.prop_2_2_D3_channelEquiv
#print axioms PolarCodes.hasDerivAt_phi_cParam
#print axioms PolarCodes.continuousOn_phi
#print axioms PolarCodes.strictMonoOn_phi
#print axioms PolarCodes.strictConvexOn_phi
