# PeTTa/MeTTa Debugging Guide

## Distinguishing Hanging from Silent Failure

When code appears to "timeout" or "hang", it could actually be:
1. **Hanging** - Actively running but stuck (infinite loop, exponential computation)
2. **Silent failure** - Code never executes or terminates without output

### Quick Diagnostic Method

**Step 1: Add checkpoint prints**
```metta
!(println! "=== CHECKPOINT 1: Before import ===")
!(import! &self mymodule)
!(println! "=== CHECKPOINT 2: After import ===")

!(println! "=== CHECKPOINT 3: Before function call ===")
!(my-expensive-function arg1 arg2)
!(println! "=== CHECKPOINT 4: After function call ===")
```

**Step 2: Run with timeout and observe**
```bash
timeout 5 ./run.sh script.metta --silent 2>&1 | grep "CHECKPOINT"
```

**Interpretation:**
- **None print**: Import failed or syntax error (silent failure)
- **1-2 print**: Import works, function call never executes (silent failure)
- **1-3 print**: Function is being called but not returning (HANGING)
- **All print**: Function completes (not a hang, check output handling)

### Method 2: Process Monitoring

```bash
# Run in background
./run.sh script.metta --silent 2>&1 &
PID=$!

# Wait and check if still running
sleep 3
if ps -p $PID > /dev/null; then
    echo "Process still running"
    # Check CPU usage
    ps -p $PID -o pid,%cpu,%mem,time,cmd
    # High %cpu → hanging (actively computing)
    # Low %cpu → stuck waiting or deadlock
else
    echo "Process terminated (silent failure or fast completion)"
fi
```

### Method 3: Gradual Bracketing

Add prints progressively inside nested code:

```metta
(= (debug-function $input)
   (let $_ (println! "DEBUG-A: Entered function")
     (let $processed (slow-operation $input)
       (let $_ (println! "DEBUG-B: After slow-operation")
         (let $result (another-operation $processed)
           (let $_ (println! "DEBUG-C: After another-operation")
             $result))))))
```

Run and note the last DEBUG-X printed → That's where execution stops.

### Common Causes

#### Silent Failure

1. **Import errors**
   ```metta
   !(import! &self nonexistent)  ; Fails silently, subsequent code doesn't run
   ```

2. **Type mismatches**
   ```metta
   (= (foo (Bar $x)) $x)
   !(foo 123)  ; Doesn't match (Bar $x) pattern, returns nothing
   ```

3. **Function never defined**
   ```metta
   ; Missing (= (my-func) ...)
   !(my-func)  ; No definition, evaluates to nothing
   ```

4. **Circular imports**
   ```metta
   ; a.metta imports b.metta, b.metta imports a.metta → Silent deadlock
   ```

#### Hanging

1. **Infinite recursion without base case**
   ```metta
   (= (loop $x) (loop (+ $x 1)))  ; Never terminates
   ```

2. **Non-deterministic explosion**
   ```metta
   (= (generate) (superpose (1 2 3)))
   (= (combine) (let $a (generate) (let $b (generate) (:: $a $b))))
   ; Creates 3×3=9 results, but collapse tries to enumerate ALL
   ```

3. **Expensive computation**
   ```metta
   (= (fibonacci $n)
      (if (<= $n 1)
          1
          (+ (fibonacci (- $n 1)) (fibonacci (- $n 2)))))
   !(fibonacci 50)  ; Exponential time, not truly hanging but very slow
   ```

4. **collapse on infinite non-determinism**
   ```metta
   (= (infinite-generator) (superpose (1 (infinite-generator))))
   !(collapse (infinite-generator))  ; Tries to collect infinite results
   ```

### Debugging Workflow

```
1. Add checkpoint before suspected code
   ↓
2. Run with timeout
   ↓
3. Check if checkpoint prints
   ↓
   ├─ NO → Silent failure (check imports, syntax, types)
   └─ YES → Hanging (add checkpoints inside function)
          ↓
          Add more internal checkpoints
          ↓
          Find exact line that hangs
          ↓
          Check for:
          - Infinite recursion
          - Expensive computation
          - collapse on non-determinism
```

### Prevention Tips

1. **Always add checkpoints when developing**
   ```metta
   !(println! "Module loaded successfully")  ; At end of file
   ```

2. **Test functions incrementally**
   ```metta
   ; Test with small input first
   !(my-function 1)  ; Works?
   !(my-function 10)  ; Still works?
   !(my-function 100)  ; Timeout here → exponential complexity
   ```

3. **Use deterministic tests before collapse**
   ```metta
   ; BAD: Jump straight to collapse
   !(collapse (complex-function))

   ; GOOD: Test non-determinism first
   !(complex-function)  ; See how many results
   ; If manageable (< 100), then:
   !(collapse (complex-function))
   ```

4. **Add iteration limits**
   ```metta
   (= (safe-loop $iter $max)
      (if (>= $iter $max)
          (LIMIT-REACHED)
          (... recurse with (+ $iter 1) ...)))
   ```

### Example: Debugging a Timeout

**Problem**: This times out:
```metta
!(prove $axioms (FIFO))
```

**Step 1**: Add checkpoint
```metta
!(println! "DEBUG: About to call prove")
!(prove $axioms (FIFO))
!(println! "DEBUG: prove returned")
```

**Result**: First prints, second doesn't → Hanging inside prove

**Step 2**: Add internal checkpoint
```metta
(= (prove $axioms $strategy)
   (let $_ (println! "DEBUG: prove entered")
     (prove-with-limit $axioms $strategy 1000)))
```

**Result**: Never prints → Silent failure (prove function never called or import failed)

**Step 3**: Check import
```metta
!(println! "DEBUG: Before import")
!(import! &self superposition)
!(println! "DEBUG: After import")
```

**Result**: First prints, second doesn't → Import is hanging!

**Conclusion**: The import itself is stuck, likely during function compilation. Check for circular dependencies or expensive compile-time evaluation.

---

**Summary**: Always add `!(println!)` checkpoints to distinguish hanging from silent failure. This saves hours of debugging!
