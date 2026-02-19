; =============================================================================
; PLN Continuous Evidence Type
; =============================================================================
;
; This module defines PLN evidence types for continuous (Normal) domains.
;
; The KEY PLN PRINCIPLE: Evidence is SEPARATE from interpretation
;   - Evidence: (n, Σx, Σx²) - context-free, aggregates via hplus
;   - Context: (μ₀, τ₀², σ²) - interpretation parameters
;   - Strength: requires context to compute
;
; This separation is what makes PLN a LOGIC, not just statistics:
;   - Evidence forms a commutative monoid under hplus
;   - Context is an explicit modal assumption
;   - Interpretation is a derived operation
;
; Reference: PLN Book Chapter 8 (Evidence and Truth Values)
;            Lean proof: PLNEvidence.lean, EvidenceNormalGamma.lean
;
; =============================================================================

!(import! &self ../lib/lib_pln)

; =============================================================================
; Type Declarations
; =============================================================================

; Continuous Evidence: sufficient statistics for Normal distribution
; (n, sum, sumSq) where:
;   n = sample size
;   sum = Σxᵢ
;   sumSq = Σxᵢ²
;
(: ContinuousEvidence Type)
(: cont-ev (-> Number Number Number ContinuousEvidence))

; Continuous Context: interpretation parameters
; (μ₀, τ₀², σ²) where:
;   μ₀ = prior mean
;   τ₀² = prior variance
;   σ² = likelihood variance (known)
;
(: ContinuousContext Type)
(: cont-ctx (-> Number Number Number ContinuousContext))

; Evidence Truth Value: evidence with explicit context
(: EvidenceTruthValue Type)
(: etv (-> ContinuousEvidence ContinuousContext EvidenceTruthValue))

; =============================================================================
; Evidence Accessors
; =============================================================================

(= (ev-n (cont-ev $n $sum $sumSq)) $n)
(= (ev-sum (cont-ev $n $sum $sumSq)) $sum)
(= (ev-sumSq (cont-ev $n $sum $sumSq)) $sumSq)

(= (ctx-mu0 (cont-ctx $mu0 $tau0_sq $sigma_sq)) $mu0)
(= (ctx-tau0-sq (cont-ctx $mu0 $tau0_sq $sigma_sq)) $tau0_sq)
(= (ctx-sigma-sq (cont-ctx $mu0 $tau0_sq $sigma_sq)) $sigma_sq)

; =============================================================================
; CORE PLN OPERATION: Evidence Aggregation (hplus)
; =============================================================================
;
; The hplus operation is CONTEXT-FREE. This is the fundamental PLN property:
; evidence combines independently of how it will be interpreted.
;
; Algebraic properties (proven in Lean: PLNEvidence.hplus_comm, hplus_assoc):
;   - Commutative: e₁ ⊕ e₂ = e₂ ⊕ e₁
;   - Associative: (e₁ ⊕ e₂) ⊕ e₃ = e₁ ⊕ (e₂ ⊕ e₃)
;   - Identity: e ⊕ (cont-ev 0 0 0) = e
;
; This makes (ContinuousEvidence, hplus, cont-ev 0 0 0) a commutative monoid.
;

(= (hplus (cont-ev $n1 $s1 $ss1) (cont-ev $n2 $s2 $ss2))
   (cont-ev (+ $n1 $n2) (+ $s1 $s2) (+ $ss1 $ss2)))

; Identity element
(= (evidence-zero) (cont-ev 0 0 0))

; =============================================================================
; OBSERVATION RULE: Data → Evidence
; =============================================================================
;
; Observing a value x creates unit evidence.
; This is the PLN way to encode "we observed x".
;
; PLN Book: Observation as evidence introduction rule
;

(= (observe $x)
   (cont-ev 1 $x (* $x $x)))

; Observe multiple values (fold with hplus)
(= (observe-all ()) (evidence-zero))
(= (observe-all ($x . $rest))
   (hplus (observe $x) (observe-all $rest)))

; =============================================================================
; DERIVED QUANTITIES FROM EVIDENCE
; =============================================================================
;
; These are computable from evidence alone (no context needed)
;

; Sample mean: x̄ = Σx / n
(= (ev-mean (cont-ev $n $sum $sumSq))
   (if (== $n 0) 0 (/ $sum $n)))

; Sample variance: s² = (Σx² - (Σx)²/n) / (n-1)
(= (ev-variance (cont-ev $n $sum $sumSq))
   (if (<= $n 1)
       0
       (/ (- $sumSq (/ (* $sum $sum) $n))
          (- $n 1))))

; Total count (for confidence calculation)
(= (ev-total (cont-ev $n $sum $sumSq)) $n)

; =============================================================================
; CONTEXT-DEPENDENT INTERPRETATION
; =============================================================================
;
; Converting evidence to a truth value REQUIRES context.
; This is the modal aspect of PLN: interpretation is context-relative.
;

; Posterior mean given context (Normal-Normal conjugate)
; Formula: (κ₀·μ₀ + n·x̄/σ²) / (κ₀ + n/σ²)  where κ₀ = 1/τ₀²
;
; Derivation: Normal-Normal conjugate posterior (PLN Book Section 8.3)
; Lean proof: EvidenceNormalGamma.posterior_mean
;
(= (posterior-mean (cont-ev $n $sum $sumSq) (cont-ctx $mu0 $tau0_sq $sigma_sq))
   (if (== $n 0)
       $mu0  ; No data → prior mean
       (let* (($prec0 (/ 1 (max 0.0001 $tau0_sq)))  ; prior precision
              ($prec_obs (/ $n $sigma_sq))          ; observation precision
              ($prec_total (+ $prec0 $prec_obs)))
             (/ (+ (* $prec0 $mu0) (/ $sum $sigma_sq))
                $prec_total))))

; Posterior precision (inverse variance)
(= (posterior-precision (cont-ev $n $sum $sumSq) (cont-ctx $mu0 $tau0_sq $sigma_sq))
   (let* (($prec0 (/ 1 (max 0.0001 $tau0_sq)))
          ($prec_obs (/ $n $sigma_sq)))
         (+ $prec0 $prec_obs)))

; Posterior variance
(= (posterior-variance $ev $ctx)
   (/ 1 (posterior-precision $ev $ctx)))

; =============================================================================
; EVIDENCE TO PLN TRUTH VALUE CONVERSION
; =============================================================================
;
; This converts evidence + context to a Simple Truth Value (stv).
;
; strength = posterior mean
; confidence = n / (n + κ) where κ is the lookahead parameter
;
; The confidence formula is the standard PLN form:
;   - At n=0: confidence = 0 (no evidence)
;   - As n→∞: confidence → 1 (certain)
;   - κ controls how quickly confidence grows
;

(= (evidence-to-stv (cont-ev $n $sum $sumSq) (cont-ctx $mu0 $tau0_sq $sigma_sq) $kappa)
   (let* (($mean (posterior-mean (cont-ev $n $sum $sumSq)
                                  (cont-ctx $mu0 $tau0_sq $sigma_sq)))
          ($conf (/ $n (+ $n $kappa))))
         (stv $mean $conf)))

; Default κ = 1 (standard PLN lookahead)
(= (evidence-to-stv $ev $ctx)
   (evidence-to-stv $ev $ctx 1))

; =============================================================================
; EVIDENCE TRUTH VALUE (ETV)
; =============================================================================
;
; An Evidence Truth Value bundles evidence with its context.
; This allows evidence to be manipulated as a truth value while
; preserving the separation between data and interpretation.
;

(= (make-etv $ev $ctx) (etv $ev $ctx))

(= (etv-evidence (etv $ev $ctx)) $ev)
(= (etv-context (etv $ev $ctx)) $ctx)

; Convert ETV to STV
(= (etv-to-stv (etv $ev $ctx))
   (evidence-to-stv $ev $ctx))

; hplus on ETVs (combines evidence, keeps shared context)
(= (etv-hplus (etv $ev1 $ctx) (etv $ev2 $ctx))
   (etv (hplus $ev1 $ev2) $ctx))

; =============================================================================
; PRECISION OPERATIONS
; =============================================================================
;
; Precision (inverse variance) is the natural weight in PLN for continuous data.
; Higher precision = more confident = more weight in revision.
;

; Observation precision: 1/(σ²/n) = n/σ²
(= (observation-precision (cont-ev $n $sum $sumSq) $sigma_sq)
   (/ $n $sigma_sq))

; Prior precision: 1/τ₀²
(= (prior-precision (cont-ctx $mu0 $tau0_sq $sigma_sq))
   (/ 1 (max 0.0001 $tau0_sq)))

; =============================================================================
; IMPROPER/VAGUE CONTEXTS
; =============================================================================
;
; Special contexts for when prior information is weak or absent.
;

; Vague context (very uncertain prior)
; τ₀² → ∞ means prior has no influence
(= (vague-context $sigma_sq)
   (cont-ctx 0 1000000 $sigma_sq))

; =============================================================================
; DEPRECATED: empirical-context for single-level inference
; =============================================================================
;
; ⚠️  WARNING: The formula τ₀² = s² - σ² is INCORRECT for single-level inference!
;
; For single-level Normal-Normal:
;   - Sample variance s² estimates σ² (observation noise)
;   - τ₀² (prior variance on μ) is NOT IDENTIFIABLE from data alone
;   - This formula gives τ₀² ≈ 0, producing SPURIOUSLY OVERCONFIDENT posteriors!
;
; THE THEORETICALLY CORRECT PLN APPROACH for single-level:
;   Use Hook B mixture over τ₀² hypotheses:
;   !(import! &self pln_hookb_mixture)
;   !(hookb-inference $ev $sigma_sq)
;
; This function is ONLY valid for HIERARCHICAL inference where you have
; multiple groups and between-group variance estimates τ₀² + σ²/n.
;
; Reference: MarkovHyperpriorMixture.lean (Hook B dominance theorem)
;

; DEPRECATED for single-level - use hookb-inference instead
(= (empirical-context (cont-ev $n $sum $sumSq) $sigma_sq)
   (let* (($mu0 (ev-mean (cont-ev $n $sum $sumSq)))
          ($sample-var (ev-variance (cont-ev $n $sum $sumSq)))
          ($tau0_sq (max 0.001 (- $sample-var $sigma_sq))))
         (cont-ctx $mu0 $tau0_sq $sigma_sq)))

; =============================================================================
; HIERARCHICAL CONTEXT (Valid for multi-group inference)
; =============================================================================
;
; When you have K groups with means ȳ₁, ..., ȳ_K:
;   τ̂₀² = Var(group_means) - mean(within_group_variance)
;
; This IS identifiable because between-group variance estimates τ₀² + σ²/n.
; Use this for hierarchical/meta-analysis settings only.
;
; (= (hierarchical-context $group_means $within_variances $sigma_sq)
;    (let* (($var_of_means (list-variance $group_means))
;           ($mean_within (list-mean $within_variances))
;           ($tau0_sq (max 0.001 (- $var_of_means $mean_within)))
;           ($mu0 (list-mean $group_means)))
;          (cont-ctx $mu0 $tau0_sq $sigma_sq)))

; =============================================================================
; CONSISTENCY CHECKS
; =============================================================================
;
; PLN requires consistency checks (analogous to Fréchet bounds for discrete).
;

; Check that evidence is valid
(= (valid-evidence? (cont-ev $n $sum $sumSq))
   (and (>= $n 0)
        (or (== $n 0)
            (>= $sumSq (/ (* $sum $sum) $n)))))  ; Variance must be non-negative

; Check that context is valid
(= (valid-context? (cont-ctx $mu0 $tau0_sq $sigma_sq))
   (and (> $tau0_sq 0)
        (> $sigma_sq 0)))

; =============================================================================
; Tests (disabled at import-time)
; =============================================================================
;
; NOTE:
; These examples were previously executed as runnable assertions at import-time.
; In current PeTTa runtime this can cause hard import failures for downstream
; modules. Keep them as reference examples and run explicitly when needed.
;
; ; Test: hplus is commutative
; !(assertEqual
;    (hplus (cont-ev 5 10 30) (cont-ev 3 6 15))
;    (hplus (cont-ev 3 6 15) (cont-ev 5 10 30)))
;
; ; Test: hplus with identity
; !(assertEqual
;    (hplus (cont-ev 5 10 30) (evidence-zero))
;    (cont-ev 5 10 30))
;
; ; Test: observe creates unit evidence
; !(assertEqual
;    (observe 3.0)
;    (cont-ev 1 3.0 9.0))
;
; ; Test: evidence mean
; !(assertEqual
;    (ev-mean (cont-ev 4 12 44))
;    3.0)
;
; ; Test: posterior mean with balanced precision
; !(let* (($ev (cont-ev 10 30 100))  ; n=10, mean=3
;         ($ctx (cont-ctx 0 1 1)))    ; prior mean=0, τ²=1, σ²=1
;        ; With n=10, σ²=1: prec_obs = 10
;        ; With τ²=1: prec_prior = 1
;        ; Posterior mean = (1*0 + 30/1) / (1 + 10) = 30/11 ≈ 2.73
;        (println! (Result "Posterior mean:" (posterior-mean $ev $ctx))))
