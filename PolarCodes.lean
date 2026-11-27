/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import PolarCodes.ArikanTransform
import PolarCodes.AuditAxioms
import PolarCodes.Bhattacharyya
import PolarCodes.BinaryEntropy
import PolarCodes.ChannelDuality
import PolarCodes.ChannelDualityEquiv
import PolarCodes.ChannelEquiv
import PolarCodes.Channels
import PolarCodes.CoherentQuantumPolarCoding
import PolarCodes.DataProcessing
import PolarCodes.DephasingSDPI
import PolarCodes.DivergenceCharacterizations
import PolarCodes.FrenkelHelpers
import PolarCodes.FrenkelIntegral
import PolarCodes.GramDephasing
import PolarCodes.HockeyStick
import PolarCodes.HockeyStickMeasure
import PolarCodes.MainTheorem
import PolarCodes.MrsGerber
import PolarCodes.MrsGerberClassical
import PolarCodes.MrsGerberEquality
import PolarCodes.MrsGerberHybrid
import PolarCodes.NoncommutativeUnion
import PolarCodes.OperationalCorollary55
import PolarCodes.PhiAndFuchs
import PolarCodes.PolarCoding
import PolarCodes.Polarization
import PolarCodes.PolarizationFine
import PolarCodes.PrivatePolarCoding
import PolarCodes.QJJS
import PolarCodes.QuantumChannels
import PolarCodes.QuantumPolarCoding
import PolarCodes.QuantumPolarCodingBase
import PolarCodes.QuantumProps
import PolarCodes.QuantumStates
import PolarCodes.RankDeficientFrenkel
import PolarCodes.Refinements
import PolarCodes.SanityChecks
import PolarCodes.ScalarSupplements
import PolarCodes.SpectralTrace
import PolarCodes.SplittingBounds

/-!
# Polynomial-Blocklength Quantum Polar Codes

Root library module importing the Lean 4 formalization of
*Polynomial-Blocklength Quantum Polar Codes via Nonlinear Dephasing Contraction*
(Prince Anand, 2026).
-/
