import LeanHaar.Applications.ClassicalShadows.Observation59
import LeanHaar.Applications.ClassicalShadows.SnapshotEnsemble
import LeanHaar.Applications.ClassicalShadows.UnitarySnapshots
import LeanHaar.Applications.MagicMonotone.BrickworkLayers
import LeanHaar.Applications.MagicMonotone.Equation24
import LeanHaar.Applications.MagicMonotone.SingleGateMoment
import LeanHaar.Applications.QML.CostFunction
import LeanHaar.Applications.QML.Observation56
import LeanHaar.Applications.QML.Observation57
import LeanHaar.Commutation
import LeanHaar.DCT
import LeanHaar.Examples.EulerAngleIntegral
import LeanHaar.Examples.PauliTwirling
import LeanHaar.Examples.UnitaryCommutant
import LeanHaar.Haar
import LeanHaar.Moments.k1Moment
import LeanHaar.Moments.k2Moment
import LeanHaar.Moments.k4Moment
import LeanHaar.PermutationCentralizer
import LeanHaar.PolyIndep
import LeanHaar.SchurWeyl
import LeanHaar.SupportingDocs.DepolarizingChannel
import LeanHaar.SupportingDocs.HaarInvariance
import LeanHaar.SupportingDocs.HaarMomentBridge
import LeanHaar.SupportingDocs.HaarMoments
import LeanHaar.SupportingDocs.RankOneCalculus
import LeanHaar.SupportingDocs.Swap
import LeanHaar.SupportingDocs.TensorPowerBasics
import LeanHaar.SupportingDocs.TensorPowerTraces
import LeanHaar.SupportingDocs.TraceContractions
import LeanHaar.SupportingDocs.Vectorization
import LeanHaar.TensorPower
import LeanHaar.TensorPower.Matrix
import LeanHaar.Weingarten
import LeanHaar.WeingartenInverse

/-!
# Schur–Weyl duality and Haar integration

This umbrella imports the core library, computed moments, shared application support,
applications, and the three standalone examples. Import a specific `LeanHaar` module
when only one part of the library is needed.
-/
