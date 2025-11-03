# Lexicographic Comparison Operators in PeTTa

PeTTa now supports Prolog's standard lexicographic (alphabetic) comparison operators for strings and atoms.

## Operators

- `@<` - Less than
- `@>` - Greater than
- `@=<` - Less than or equal
- `@>=` - Greater than or equal

## Usage

```metta
;; Basic string comparison
(@< "apple" "banana")    ; → true
(@< "zebra" "apple")     ; → false

;; Multi-character strings
(@< "hello" "world")     ; → true
(@< "metamath" "metta")  ; → true

;; Define a string< function
(: string< (-> String String Bool))
(= (string< $x $y) (@< $x $y))

!(string< "first" "second")  ; → true
```

## Examples

See `examples/at_lt_test.metta` for comprehensive tests.

Run with:
```bash
./run.sh examples/at_lt_test.metta
```

## Use Case: mmverify Cross-Platform Compatibility

These operators enable PeTTa to run MeTTa code that requires string comparison, such as the mmverify metamath proof verifier:

- HE (Hyperon-Experimental): Uses `py-dot` to call Python's `__lt__`
- PeTTa: Uses `@<` for native Prolog lexicographic comparison

Both implementations provide the same functionality for sorting and comparing strings.

## Implementation

Added to `src/metta.pl`:
```prolog
% Lexicographic (alphabetic) comparison for strings/atoms
'@<'(A,B,R) :- (A @< B -> R=true ; R=false).
'@>'(A,B,R) :- (A @> B -> R=true ; R=false).
'@=<'(A,B,R) :- (A @=< B -> R=true ; R=false).
'@>='(A,B,R) :- (A @>= B -> R=true ; R=false).
```

Registered in translator at line 222.
