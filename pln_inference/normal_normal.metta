; ============================================================================
; PLN-COMPLETE: Normal-Normal Conjugate Inference
; ============================================================================
;
; This implements Gaussian inference with known variance, extending PLN
; to continuous domains while maintaining full Bayesian correctness.
;
; Mathematical foundation (known variance σ²):
;   Prior: μ ~ Normal(μ₀, τ₀²)
;   Likelihood: x | μ ~ Normal(μ, σ²)
;   Posterior: μ | x₁...xₙ ~ Normal(μₙ, τₙ²)
;
;   where:
;     τₙ² = 1 / (1/τ₀² + n/σ²)
;     μₙ = τₙ² · (μ₀/τ₀² + (Σxᵢ)/σ²)
;
; Sufficient statistics: (n, sum_x, sum_x²)
;
; PLN connection:
;   - "Strength" = posterior mean μₙ (point estimate)
;   - "Confidence" can be derived from posterior precision
;   - PLN revision = combine sufficient statistics
;
; This is PLN-COMPLETE for Normal models:
;   - No approximations
;   - Full Bayesian update
;   - Analytically tractable
;
; ============================================================================

!(import! &self pln_complete)

; ----------------------------------------------------------------------------
; Normal Evidence Representation
; ----------------------------------------------------------------------------
; Sufficient statistics for Normal: (n, sum_x, sum_x_squared)
; With these, we can compute sample mean and sample variance

(: NormalEvidence (-> Number Number Number NormalEvidence))
(= (NormalEvidence $n $sum_x $sum_x_sq)
   (normal-evidence $n $sum_x $sum_x_sq))

; Accessors
(= (normal-evidence-n (normal-evidence $n $sum_x $sum_x_sq)) $n)
(= (normal-evidence-sum (normal-evidence $n $sum_x $sum_x_sq)) $sum_x)
(= (normal-evidence-sum-sq (normal-evidence $n $sum_x $sum_x_sq)) $sum_x_sq)

; Derived quantities
(= (normal-evidence-mean (normal-evidence $n $sum_x $sum_x_sq))
   (if (== $n 0)
       0
       (/ $sum_x $n)))

; Sample variance (unbiased estimator)
; Computes: (sum_x_sq - n * mean^2) / (n - 1)
(= (normal-evidence-variance (normal-evidence $n $sum_x $sum_x_sq))
   (if (<= $n 1)
       1  ; Default if not enough data
       (/ (- $sum_x_sq (* $n (/ $sum_x $n) (/ $sum_x $n)))
          (- $n 1))))

; ----------------------------------------------------------------------------
; Prior Specification
; ----------------------------------------------------------------------------
; Prior: Normal(μ₀, τ₀²)
; Represent as (μ₀, precision₀) where precision = 1/τ₀²

(: NormalPrior (-> Number Number NormalPrior))
(= (NormalPrior $mu0 $precision0) (normal-prior $mu0 $precision0))

; Standard vague prior: μ₀ = 0, precision₀ = 0 (very diffuse)
(= (vague-normal-prior) (normal-prior 0 0.001))

; Informative prior centered at $mu with precision $prec
(= (informative-normal-prior $mu $prec) (normal-prior $mu $prec))

; ----------------------------------------------------------------------------
; Normal-Normal Posterior Update
; ----------------------------------------------------------------------------
; Given:
;   Prior: Normal(μ₀, 1/precision₀)
;   Data: n observations with sum Σxᵢ
;   Known likelihood variance: σ²
;
; Posterior: Normal(μₙ, 1/precisionₙ)
;   precisionₙ = precision₀ + n/σ²
;   μₙ = (precision₀·μ₀ + (Σxᵢ)/σ²) / precisionₙ

; Posterior mean (point estimate of μ)
; mu_n = (prec0 * mu0 + sum_x/sigma_sq) / (prec0 + n/sigma_sq)
(= (normal-posterior-mean
     (normal-prior $mu0 $prec0)
     (normal-evidence $n $sum_x $sum_x_sq)
     $sigma_sq)
   (/ (+ (* $prec0 $mu0) (/ $sum_x $sigma_sq))
      (+ $prec0 (/ $n $sigma_sq))))

; Posterior precision (1/posterior variance of μ)
; prec_n = prec0 + n/sigma_sq
(= (normal-posterior-precision
     (normal-prior $mu0 $prec0)
     (normal-evidence $n $sum_x $sum_x_sq)
     $sigma_sq)
   (+ $prec0 (/ $n $sigma_sq)))

; Posterior parameters as tuple (for external use)
(= (normal-posterior-params $prior $evidence $sigma_sq)
   (list (normal-posterior-mean $prior $evidence $sigma_sq)
         (normal-posterior-precision $prior $evidence $sigma_sq)))

; Posterior variance = 1 / precision
(= (normal-posterior-variance $prior $evidence $sigma_sq)
   (/ 1 (normal-posterior-precision $prior $evidence $sigma_sq)))

; Posterior standard deviation = sqrt(variance)
(= (normal-posterior-std $prior $evidence $sigma_sq)
   (sqrt-math (normal-posterior-variance $prior $evidence $sigma_sq)))

; ----------------------------------------------------------------------------
; PLN-COMPLETE Revision Rule (Normal)
; ----------------------------------------------------------------------------
; Combine sufficient statistics from independent observations

(= (normal-revision
     (normal-evidence $n1 $sum1 $sumsq1)
     (normal-evidence $n2 $sum2 $sumsq2))
   (normal-evidence
     (+ $n1 $n2)
     (+ $sum1 $sum2)
     (+ $sumsq1 $sumsq2)))

; ----------------------------------------------------------------------------
; Observation to Normal Evidence
; ----------------------------------------------------------------------------

(= (observation-to-normal-evidence $x)
   (normal-evidence 1 $x (* $x $x)))

; Multiple observations
(= (observations-to-normal-evidence ())
   (normal-evidence 0 0 0))
(= (observations-to-normal-evidence ($x . $rest))
   (normal-revision
     (observation-to-normal-evidence $x)
     (observations-to-normal-evidence $rest)))

; ----------------------------------------------------------------------------
; PLN Truth Value Conversion
; ----------------------------------------------------------------------------
; For Normal distributions, we map to PLN format:
;   - "Strength" = normalized posterior mean (scaled to [0,1] range)
;   - Confidence = based on posterior precision relative to prior

; Convert posterior mean to [0,1] strength using logistic transform
; This handles unbounded means by squashing to [0,1]
(= (mean-to-strength $mu)
   (/ 1 (+ 1 (exp (- 0 $mu)))))  ; Logistic sigmoid

; Alternative: linear scaling if bounds known
; clamped = max(lo, min(hi, mu)), then scale to [0,1]
(= (mean-to-strength-bounded $mu $lo $hi)
   (/ (- (max $lo (min $hi $mu)) $lo) (- $hi $lo)))

; Confidence from precision
; confidence = precision / (precision + k) analogous to count-based
(= (precision-to-confidence $precision $k)
   (/ $precision (+ $precision $k)))

; Full truth value
(= (normal-evidence-to-tv $prior $evidence $sigma_sq)
   (tv (mean-to-strength (normal-posterior-mean $prior $evidence $sigma_sq))
       (precision-to-confidence (normal-posterior-precision $prior $evidence $sigma_sq) 1)))

; ----------------------------------------------------------------------------
; Log-Likelihood (for PPLBench evaluation)
; ----------------------------------------------------------------------------
; Natural log via log-math (base e)
(= (e) 2.718281828459045)
(= (ln $x) (log-math (e) $x))
(= (log-2-pi) 1.8378770664093453)  ; ln(2π)

; Log PDF of Normal distribution
; log N(x | μ, σ²) = -0.5 * (log(2π) + log(σ²) + (x-μ)²/σ²)
(= (normal-log-pdf $x $mu $sigma_sq)
   (* -0.5 (+ (log-2-pi)
              (+ (ln $sigma_sq)
                 (/ (* (- $x $mu) (- $x $mu)) $sigma_sq)))))

; Predictive log-likelihood using posterior mean
(= (normal-predictive-log-likelihood $x $prior $evidence $sigma_sq)
   (normal-log-pdf $x (normal-posterior-mean $prior $evidence $sigma_sq) $sigma_sq))

; Squared error for posterior predictive (alternative metric)
(= (normal-squared-error $x $prior $evidence $sigma_sq)
   (* (- $x (normal-posterior-mean $prior $evidence $sigma_sq))
      (- $x (normal-posterior-mean $prior $evidence $sigma_sq))))

; ----------------------------------------------------------------------------
; Example: Estimating school effect
; ----------------------------------------------------------------------------
;
; Scenario: Estimate the effect of a teaching method
;   - Prior belief: effect is around 0 (no effect), precision 0.1
;   - Known observation noise: σ² = 1
;   - Observations: [0.5, 1.2, 0.8, 1.1, 0.9]
;
; Posterior:
;   n = 5, sum = 4.5
;   precision_n = 0.1 + 5/1 = 5.1
;   μ_n = (0.1*0 + 4.5/1) / 5.1 = 4.5/5.1 ≈ 0.882

; Example test
; (= (test-obs) (0.5 1.2 0.8 1.1 0.9))
; (= (test-evidence) (observations-to-normal-evidence (test-obs)))
; (= (test-prior) (informative-normal-prior 0 0.1))
; !(normal-posterior-mean (test-prior) (test-evidence) 1)

; ============================================================================
; PRECISION-WEIGHTED REVISION (N-Schools Shrinkage)
; ============================================================================
;
; This implements the hierarchical PLN rule for combining:
;   - Prior (population mean μ, precision = 1/τ²)
;   - Observation (individual observation y, precision = 1/σ²)
;
; The posterior is a precision-weighted average:
;   θ̂ = (μ·τ⁻² + y·σ⁻²) / (τ⁻² + σ⁻²)
;     = (1-B)·y + B·μ   where B = σ²/(σ² + τ²)
;
; This IS the Bayesian shrinkage estimator!
; Verified in Lean: PLNHierarchicalRules.shrinkage_from_revision
;
; ============================================================================

; ----------------------------------------------------------------------------
; Precision-Weighted Revision: THE core shrinkage operation
;
; Parameters:
;   mu: prior/population mean
;   prec_prior: precision of prior (1/τ² = 1/between-group variance)
;   y: observation
;   prec_obs: precision of observation (1/σ² = 1/observation variance)
;
; Returns: (normal-posterior theta_hat prec_total)
; ----------------------------------------------------------------------------
(= (precision-weighted-revision $mu $prec_prior $y $prec_obs)
   (let* (($prec_total (+ $prec_prior $prec_obs))
          ($theta_hat (/ (+ (* $mu $prec_prior) (* $y $prec_obs)) $prec_total)))
         (normal-posterior $theta_hat $prec_total)))

; Just return the point estimate
(= (precision-weighted-mean $mu $prec_prior $y $prec_obs)
   (/ (+ (* $mu $prec_prior) (* $y $prec_obs))
      (+ $prec_prior $prec_obs)))

; ----------------------------------------------------------------------------
; Shrinkage Factor: B = σ²/(σ² + τ²)
;
; B ∈ [0, 1] measures how much we shrink toward the population mean:
;   - B = 0: no shrinkage, trust the observation completely
;   - B = 1: full shrinkage, ignore observation, use population mean
;   - B intermediate: compromise between observation and population
;
; Lean: PLNHierarchicalRules.shrinkageFactor
; ----------------------------------------------------------------------------
(= (shrinkage-factor $sigma_sq $tau_sq)
   (/ $sigma_sq (+ $sigma_sq $tau_sq)))

; Alternative: using precisions directly (precision = 1/variance)
(= (shrinkage-factor-prec $prec_obs $prec_prior)
   (/ $prec_prior (+ $prec_obs $prec_prior)))

; ----------------------------------------------------------------------------
; Shrunk Estimate: θ̂ = (1-B)·y + B·μ
;
; Given:
;   y: observed value
;   mu: population mean
;   sigma_sq: observation variance
;   tau_sq: between-group variance
;
; Returns: shrunk estimate
;
; Lean: PLNHierarchicalRules.shrinkage_from_revision proves this
;       equals precision-weighted revision!
; ----------------------------------------------------------------------------
(= (shrunk-estimate $y $mu $sigma_sq $tau_sq)
   (let $B (shrinkage-factor $sigma_sq $tau_sq)
        (+ (* (- 1 $B) $y) (* $B $mu))))

; Alternative via precision-weighted revision (should give same answer)
(= (shrunk-estimate-via-revision $y $mu $sigma_sq $tau_sq)
   (let* (($prec_prior (/ 1 $tau_sq))
          ($prec_obs (/ 1 $sigma_sq))
          ($result (precision-weighted-revision $mu $prec_prior $y $prec_obs)))
         (posterior-mean $result)))

; Extract mean from normal-posterior
(= (posterior-mean (normal-posterior $mu $prec)) $mu)
(= (posterior-precision (normal-posterior $mu $prec)) $prec)

; ----------------------------------------------------------------------------
; Pool Observations (PLN Induction)
;
; Combine normal evidence from multiple observations via revision
; Used for: pooling school observations → population estimate
; ----------------------------------------------------------------------------
(= (pool-observations ())
   (normal-evidence 0 0 0))
(= (pool-observations ($obs . $rest))
   (normal-revision
     (observation-to-normal-evidence $obs)
     (pool-observations $rest)))

; Pool with weights (for heteroscedastic observations)
(= (pool-weighted-observations ())
   (normal-evidence 0 0 0))
(= (pool-weighted-observations (($obs $weight) . $rest))
   (normal-revision
     (weighted-observation-to-normal-evidence $obs $weight)
     (pool-weighted-observations $rest)))

; Create weighted normal evidence
; weight = precision = 1/variance
(= (weighted-observation-to-normal-evidence $x $weight)
   (normal-evidence $weight (* $weight $x) (* $weight (* $x $x))))

; ----------------------------------------------------------------------------
; Pooled Mean (Simple average for known equal variance)
; ----------------------------------------------------------------------------
(= (pooled-mean $observations)
   (normal-evidence-mean (pool-observations $observations)))

; ----------------------------------------------------------------------------
; N-Schools Full Pipeline
;
; Given:
;   observations: list of (y_j, sigma_sq_j) pairs
;   tau_sq: between-school variance
;
; Returns: list of shrunk estimates
; ----------------------------------------------------------------------------
(= (n-schools-shrinkage $obs_with_var $tau_sq $mu_pop)
   (n-schools-shrinkage-helper $obs_with_var $tau_sq $mu_pop))

(= (n-schools-shrinkage-helper () $tau_sq $mu_pop)
   ())
(= (n-schools-shrinkage-helper (($y $sigma_sq) . $rest) $tau_sq $mu_pop)
   ((shrunk-estimate $y $mu_pop $sigma_sq $tau_sq) .
    (n-schools-shrinkage-helper $rest $tau_sq $mu_pop)))

; ============================================================================
; BATCH OPERATIONS (for PPLBench integration)
; ============================================================================

; Single-call shrinkage
(= (batch-shrunk-estimate $y $mu $sigma_sq $tau_sq)
   (shrunk-estimate-result
     (shrunk-estimate $y $mu $sigma_sq $tau_sq)
     (shrinkage-factor $sigma_sq $tau_sq)))

; Single-call precision-weighted revision
(= (batch-precision-revision $mu $prec_prior $y $prec_obs)
   (let* (($prec_total (+ $prec_prior $prec_obs))
          ($theta_hat (/ (+ (* $mu $prec_prior) (* $y $prec_obs)) $prec_total))
          ($conf (/ $prec_total (+ $prec_total 1))))
         (revision-result $theta_hat $prec_total $conf)))

; ============================================================================
; TESTS
; ============================================================================

; Test shrinkage factor
; !(println! "=== Shrinkage Factor ===")
; !(shrinkage-factor 1.0 1.0)  ; Should be 0.5
; !(shrinkage-factor 0.1 1.0)  ; Should be ~0.09 (little shrinkage)
; !(shrinkage-factor 10.0 1.0) ; Should be ~0.91 (much shrinkage)

; Test shrunk estimate
; !(println! "=== Shrunk Estimate ===")
; !(shrunk-estimate 5.0 0.0 1.0 1.0)  ; y=5, mu=0, equal variances → 2.5

; Test precision-weighted revision
; !(println! "=== Precision-Weighted Revision ===")
; !(precision-weighted-revision 0.0 1.0 5.0 1.0)  ; Same as above

; ============================================================================
