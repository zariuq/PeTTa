# Parser fails on parentheses inside quoted strings

## Description

PeTTa's parser fails when trying to parse parentheses `(` or `)` inside string literals. This makes it incompatible with standard MeTTa code and prevents object languages (like Metamath) that use parentheses in their syntax.

## Example

This valid MeTTa code fails to parse:

```metta
!(println! "Test (")
```

Error:
```
Parse error: missing ')', starting at line 1:
println! "Test ("
```

## Expected Behavior

The parser should recognize that parentheses inside quoted strings are just string content, not structural delimiters. This works correctly in HE MeTTa (Hyperon Experimental).

## Comparison: HE MeTTa vs PeTTa

**HE MeTTa** ✅ Works:
```bash
$ metta test.metta
Test (
```

**PeTTa** ❌ Fails:
```bash
$ ./run.sh test.metta
Parse error: missing ')'
```

## Root Cause

The `grab_until_balanced` function in `src/filereader.pl` counts ALL parentheses when determining form boundaries, without checking if they're inside strings.

## Proposed Solution

Track string state while parsing:
- Add `InString` flag (are we inside a string literal?)
- Add `Escaped` flag (was previous char a backslash?)
- Only count `()` when `InString = false`

## Fix Available

I've implemented and tested a fix in branch `quotedparensfix`:
- Branch: https://github.com/zariuq/PeTTa/tree/quotedparensfix
- Single file changed: `src/filereader.pl`
- Fully backward compatible
- Comprehensive tests passing

## Test Cases Verified

✅ Basic parenthesis in string: `"Test (paren)"`
✅ Unmatched parens: `"Only open ("` and `"Only close )"`
✅ Multiple parens: `"Multiple ((( and )))"`
✅ Escaped quotes with parens: `"Quote \" with ( inside"`
✅ Real-world Metamath: `!(add_a kb "tpl" ("term" "(" "t" "+" "r" ")"))`
✅ Full integration: Complete Metamath proof verification

## Impact

This bug prevents PeTTa from being used with:
- Standard MeTTa examples that use parentheses in strings
- Object languages like Metamath that require parentheses in syntax
- Any code that needs to print or manipulate strings containing parens

## Workaround (not recommended)

Currently, users must use unicode delimiters (`⟨⟩` for strings, `⟦⟧` for parens) or avoid parentheses in strings entirely. The fix eliminates this limitation.
