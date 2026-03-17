;;; xiPLN - calibrated multi-carrier PLN layer (discrete + continuous)
;;;
;;; Design goals:
;;;   1. Keep nuPLN exact evidence algebra for binary/Beta-Bernoulli carriers.
;;;   2. Separate exact semantic bridges from operational calibration layers.
;;;   3. Add a first-class continuous carrier interface (Normal sufficient stats).
;;;
;;; This is the "xiPLN" evolution path while preserving nuPLN compatibility.

!(import! &self lib_pln_nu)
!(import! &self ../pln_inference/pln_continuous_evidence)
!(import! &self ../pln_inference/normal_normal)

;;; ============================================================================
;;; Shared calibration defaults (tunable per task)
;;; Exact evidence operations should still prefer explicit parameters when possible.
;;; ============================================================================

;;; Conservative defaults for projections and control-layer policies.
(= (xiPLN.defaultKappa) 10.0)
(= (xiPLN.defaultGlobalWeight) 0.05)

;;; ============================================================================
;;; Discrete (Beta-Bernoulli evidence carrier)
;;; ============================================================================

(= (xiPLN.discrete.Evidence $nPos $nNeg) (nuPLN.Evidence $nPos $nNeg))
(= (xiPLN.discrete.hplus $e1 $e2) (nuPLN.hplus $e1 $e2))
(= (xiPLN.discrete.tensor $e1 $e2) (nuPLN.tensor $e1 $e2))
(= (xiPLN.discrete.power $e $w) (nuPLN.power $e $w))

(= (xiPLN.discrete.toStrength $e) (nuPLN.toStrength $e))
(= (xiPLN.discrete.toConfidence $e $kappa) (nuPLN.toConfidence $e $kappa))

(= (xiPLN.discrete.toSTV $e)
   (nuPLN.toSTVWithKappa $e (xiPLN.defaultKappa)))
(= (xiPLN.discrete.toSTV $e $kappa)
   (nuPLN.toSTVWithKappa $e $kappa))

(= (xiPLN.discrete.fromSTV $tv)
   (nuPLN.fromSTVWithKappa $tv (xiPLN.defaultKappa)))
(= (xiPLN.discrete.fromSTV $tv $kappa)
   (nuPLN.fromSTVWithKappa $tv $kappa))

(= (xiPLN.discrete.Revision $tv1 $tv2)
   (nuPLN.RevisionWithKappa $tv1 $tv2 (xiPLN.defaultKappa)))
(= (xiPLN.discrete.Revision $tv1 $tv2 $kappa)
   (nuPLN.RevisionWithKappa $tv1 $tv2 $kappa))

;;; Exact tensor-strength NB posterior bridge.
;;; This is the canonical xiPLN default and matches the current theoremic story.
(= (xiPLN.discrete.NBPosteriorSTVExact $priorFactor $factors)
   (nuPLN.NBPosteriorSTVWithKappa
     $priorFactor
     $factors
     (xiPLN.defaultKappa)))

(= (xiPLN.discrete.NBPosteriorSTVExact $priorFactor $factors $kappa)
   (nuPLN.NBPosteriorSTVWithKappa $priorFactor $factors $kappa))

(= (xiPLN.discrete.NBPosteriorSTV $priorFactor $factors)
   (xiPLN.discrete.NBPosteriorSTVExact $priorFactor $factors))

(= (xiPLN.discrete.NBPosteriorSTV $priorFactor $factors $kappa)
   (xiPLN.discrete.NBPosteriorSTVExact $priorFactor $factors $kappa))

;;; Explicit operational layer: globally regraded evidence product before STV
;;; projection. Useful for selector/control policies, not the exact NB bridge.
(= (xiPLN.operational.NBPosteriorSTVRegraded $priorFactor $factors)
   (xiPLN.operational.NBPosteriorSTVRegraded
     $priorFactor
     $factors
     (xiPLN.defaultGlobalWeight)
     (xiPLN.defaultKappa)))

(= (xiPLN.operational.NBPosteriorSTVRegraded $priorFactor $factors $globalWeight $kappa)
   (nuPLN.NBPosteriorSTVRegraded $priorFactor $factors $globalWeight $kappa))

;;; Discoverability alias mirroring the discrete namespace.
(= (xiPLN.discrete.NBPosteriorSTVRegraded $priorFactor $factors)
   (xiPLN.operational.NBPosteriorSTVRegraded $priorFactor $factors))

(= (xiPLN.discrete.NBPosteriorSTVRegraded $priorFactor $factors $globalWeight $kappa)
   (xiPLN.operational.NBPosteriorSTVRegraded $priorFactor $factors $globalWeight $kappa))

;;; ============================================================================
;;; Exact rule aliases
;;; ============================================================================
;;;
;;; These stay close to the exact evidence/state story.

;;; Contextual prior revision: global prior revised with local/contextual prior.
(= (xiPLN.Rule.ContextualPriorRevision $tvGlobal $tvLocal)
   (xiPLN.discrete.Revision $tvGlobal $tvLocal))
(= (xiPLN.Rule.ContextualPriorRevision $tvGlobal $tvLocal $kappa)
   (xiPLN.discrete.Revision $tvGlobal $tvLocal $kappa))

;;; Prior-likelihood tensor at evidence level, projected back to STV.
(= (xiPLN.Rule.PriorLikelihoodTensorSTV $priorEvidence $likelihoodEvidence)
   (xiPLN.discrete.toSTV
     (xiPLN.discrete.tensor $priorEvidence $likelihoodEvidence)))
(= (xiPLN.Rule.PriorLikelihoodTensorSTV $priorEvidence $likelihoodEvidence $kappa)
   (xiPLN.discrete.toSTV
     (xiPLN.discrete.tensor $priorEvidence $likelihoodEvidence)
     $kappa))

;;; Preferred exact namespace.
(= (xiPLN.Rule.Exact.ContextualPriorRevision $tvGlobal $tvLocal)
   (xiPLN.Rule.ContextualPriorRevision $tvGlobal $tvLocal))
(= (xiPLN.Rule.Exact.ContextualPriorRevision $tvGlobal $tvLocal $kappa)
   (xiPLN.Rule.ContextualPriorRevision $tvGlobal $tvLocal $kappa))

(= (xiPLN.Rule.Exact.PriorLikelihoodTensorSTV $priorEvidence $likelihoodEvidence)
   (xiPLN.Rule.PriorLikelihoodTensorSTV $priorEvidence $likelihoodEvidence))
(= (xiPLN.Rule.Exact.PriorLikelihoodTensorSTV $priorEvidence $likelihoodEvidence $kappa)
   (xiPLN.Rule.PriorLikelihoodTensorSTV $priorEvidence $likelihoodEvidence $kappa))

;;; ============================================================================
;;; Operational / selector aliases
;;; ============================================================================
;;;
;;; These are useful control-layer helpers, but they are not the exact NB bridge
;;; or the canonical exact rewrite story from the current book.

;;; Normalized/regraduated prior-likelihood tensor:
;;; scale prior and likelihood evidence by explicit weights, then tensor-compose.
(= (xiPLN.Rule.Operational.NormalizedPriorLikelihoodTensor $priorEvidence $likelihoodEvidence
                                                           $priorWeight $likelihoodWeight)
   (xiPLN.discrete.toSTV
     (xiPLN.discrete.tensor
       (xiPLN.discrete.power $priorEvidence $priorWeight)
       (xiPLN.discrete.power $likelihoodEvidence $likelihoodWeight))))
(= (xiPLN.Rule.Operational.NormalizedPriorLikelihoodTensor $priorEvidence $likelihoodEvidence
                                                           $priorWeight $likelihoodWeight $kappa)
   (xiPLN.discrete.toSTV
     (xiPLN.discrete.tensor
       (xiPLN.discrete.power $priorEvidence $priorWeight)
       (xiPLN.discrete.power $likelihoodEvidence $likelihoodWeight))
     $kappa))

;;; Weak-negative safe update: add epsilon negative evidence via revision.
(= (xiPLN.Rule.Operational.WeakNegativeSafeUpdate $evidence $epsilon)
   (xiPLN.discrete.hplus $evidence (xiPLN.discrete.Evidence 0 $epsilon)))

;;; Regraduated evidence rule alias.
(= (xiPLN.Rule.Operational.RegraduatedEvidence $evidence $weight)
   (xiPLN.discrete.power $evidence $weight))

;;; Backward-compatible aliases for existing demos/tests.
(= (xiPLN.Rule.NormalizedPriorLikelihoodTensor $priorEvidence $likelihoodEvidence
                                               $priorWeight $likelihoodWeight)
   (xiPLN.Rule.Operational.NormalizedPriorLikelihoodTensor
     $priorEvidence
     $likelihoodEvidence
     $priorWeight
     $likelihoodWeight))
(= (xiPLN.Rule.NormalizedPriorLikelihoodTensor $priorEvidence $likelihoodEvidence
                                               $priorWeight $likelihoodWeight $kappa)
   (xiPLN.Rule.Operational.NormalizedPriorLikelihoodTensor
     $priorEvidence
     $likelihoodEvidence
     $priorWeight
     $likelihoodWeight
     $kappa))

(= (xiPLN.Rule.WeakNegativeSafeUpdate $evidence $epsilon)
   (xiPLN.Rule.Operational.WeakNegativeSafeUpdate $evidence $epsilon))

(= (xiPLN.Rule.RegraduatedEvidence $evidence $weight)
   (xiPLN.Rule.Operational.RegraduatedEvidence $evidence $weight))

(= (xiPLN.Rule.LocalEvidenceRevision $tvGlobal $tvLocal)
   (xiPLN.Rule.ContextualPriorRevision $tvGlobal $tvLocal))

(= (xiPLN.Rule.LocalEvidenceRevision $tvGlobal $tvLocal $kappa)
   (xiPLN.Rule.ContextualPriorRevision $tvGlobal $tvLocal $kappa))

(= (xiPLN.Rule.NormalizedSequentialComposition $priorEvidence $likelihoodEvidence
                                               $priorWeight $likelihoodWeight)
   (xiPLN.Rule.NormalizedPriorLikelihoodTensor
     $priorEvidence
     $likelihoodEvidence
     $priorWeight
     $likelihoodWeight))

(= (xiPLN.Rule.NormalizedSequentialComposition $priorEvidence $likelihoodEvidence
                                               $priorWeight $likelihoodWeight $kappa)
   (xiPLN.Rule.NormalizedPriorLikelihoodTensor
     $priorEvidence
     $likelihoodEvidence
     $priorWeight
     $likelihoodWeight
     $kappa))

(= (xiPLN.Rule.EvidenceRegraduation $evidence $weight)
   (xiPLN.Rule.RegraduatedEvidence $evidence $weight))

;;; Bridge naming for tensor-strength NB equivalence (STV-level wrapper).
;;; The plain bridge is exact; the operational bridge is explicit.
(= (xiPLN.Bridge.TensorStrengthEqNBPosterior $priorFactor $factors)
   (xiPLN.discrete.NBPosteriorSTV $priorFactor $factors))
(= (xiPLN.Bridge.TensorStrengthEqNBPosterior $priorFactor $factors $kappa)
   (xiPLN.discrete.NBPosteriorSTV $priorFactor $factors $kappa))

(= (xiPLN.Bridge.TensorStrengthEqNBPosteriorOperational $priorFactor $factors)
   (xiPLN.operational.NBPosteriorSTVRegraded $priorFactor $factors))
(= (xiPLN.Bridge.TensorStrengthEqNBPosteriorOperational $priorFactor $factors $globalWeight $kappa)
   (xiPLN.operational.NBPosteriorSTVRegraded $priorFactor $factors $globalWeight $kappa))

;;; ============================================================================
;;; Continuous (Normal sufficient statistics carrier)
;;; ============================================================================

;;; Evidence is (n, sum_x, sum_x_sq) and context is (mu0, tau0_sq, sigma_sq).
(= (xiPLN.cont.Evidence $n $sum $sumSq) (cont-ev $n $sum $sumSq))
(= (xiPLN.cont.Context $mu0 $tau0sq $sigmaSq) (cont-ctx $mu0 $tau0sq $sigmaSq))

;;; Context-free aggregation (same hplus principle as discrete carriers).
(= (xiPLN.cont.hplus $e1 $e2) (hplus $e1 $e2))
(= (xiPLN.cont.zero) (evidence-zero))

(= (xiPLN.cont.observe $x) (observe $x))
(= (xiPLN.cont.observeAll $xs) (observe-all $xs))

;;; Context-dependent interpretation to STV.
(= (xiPLN.cont.toSTV $ev $ctx)
   (evidence-to-stv $ev $ctx (xiPLN.defaultKappa)))
(= (xiPLN.cont.toSTV $ev $ctx $kappa)
   (evidence-to-stv $ev $ctx $kappa))

;;; Probability-space STV view for downstream rules that assume strength in [0, 1].
;;; This keeps Normal evidence/context semantics and only changes the projection.
;;; Treat it as an operational view/projection, not a new carrier semantics.
(= (xiPLN.cont.toProbSTV $ev $ctx)
   (xiPLN.cont.toProbSTV $ev $ctx (xiPLN.defaultKappa)))

(= (xiPLN.cont.toProbSTV $ev $ctx $kappa)
   (let $tv (evidence-to-stv $ev $ctx $kappa)
     (let (stv $mean $conf) $tv
       (stv (mean-to-strength $mean) $conf))))

;;; Posterior summary helpers (Normal-Normal conjugacy).
(= (xiPLN.cont.posteriorMean $prior $evidence $sigmaSq)
   (normal-posterior-mean $prior $evidence $sigmaSq))
(= (xiPLN.cont.posteriorPrecision $prior $evidence $sigmaSq)
   (normal-posterior-precision $prior $evidence $sigmaSq))

;;; Precision-weighted revision/shrinkage.
(= (xiPLN.cont.precisionRevision $mu $precPrior $y $precObs)
   (precision-weighted-revision $mu $precPrior $y $precObs))

(= (xiPLN.cont.shrunkEstimate $y $mu $sigmaSq $tauSq)
   (shrunk-estimate $y $mu $sigmaSq $tauSq))
