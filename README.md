## PeTTa

Efficient MeTTa language implementation in Prolog.

Please check out the [Wiki](https://github.com/patham9/PeTTa/wiki) for more information.

### Dependencies

- SWI-Prolog >= 9.3.x
- Python 3.x (for janus Python interop)

### Usage

Example run:

`time sh run.sh ./examples/nars_tuffy.metta`

Several `.metta` files may be named, and they are loaded in exactly the order
given, followed by any flags:

`sh run.sh ./examples/a.metta ./examples/b.metta --warn-runtime-checks`

Load order is semantically significant — a declaration or a constructor that
arrives in a later file cannot retroactively inform code already compiled from
an earlier one.

### MORK and FAISS spaces

If MORK and FAISS is installed, execute `sh build.sh` to support MORK-based atom spaces and FAISS-based atom-vector spaces.

The following projects are cloned and built by build.sh:

**Repository:** [mork_ffi](https://github.com/patham9/mork_ffi) dependent on [trueagi-io/mork](https://github.com/trueagi-io/mork)

**Repository:** [faiss_ffi](https://github.com/patham9/faiss_ffi) dependent on [facebookresearch/faiss](https://github.com/facebookresearch/faiss)

### Extension libraries

Please check out [Extension libraries](https://github.com/trueagi-io/PeTTa/wiki/Extension-libraries) for a set of extension libraries that can be invoked from MeTTa files directly from the git repository.

### Types

A declaration `(: f (-> A1 .. An R))` is a contract: `f` takes arguments of
the types `A1 .. An` and returns results of the type `R`. PeTTa checks
contracts while it translates:

- a definite type error is reported at compile time, with the file, line and form;
- a check is compiled in only where a value's type is not known there, so fully
  typed code compiles to the same Prolog clauses as untyped code;
- a failing check raises a type error. Checks never remove answers: a run
  without type errors computes exactly what the program computes with its
  types erased.

```metta
(: inc (-> Number Number))
(= (inc $x) (+ $x 1))

!(inc "oops")   ; Type mismatch: got "oops" but expected Number
```

A type error in a definition stops the load; in a `!` expression it ends that
expression with an `(Error ...)` result, and the run exits with status 2.

**Types.** `Number`, `String` and `Bool`; type names declared by `(: red
Color)` or by a constructor `(: rgb (-> Number Number Number Color))`; `(List
T)`; tuple types `(T1 .. Tn)`, the type of a fixed-length expression such as
`(STV Number Number)` for `(STV 0.9 0.8)`; arrows `(-> A B)`; unions `(| A B)`;
type variables `$a`; and `%Undefined%`, `Atom` and `Expression`, which every
value has.

**Type names are closed.** The values of a declared name are the symbols and
constructor applications declared with it, so two names conflict unless an
atom is declared with both. A program that defines `get-type` rules of its own
(see `examples/types_dependent.metta`) can give any value any type: its type
names are then only checked at runtime.

**Polymorphism.** A type variable of the parameters is the caller's choice.
Inside the function it is a fixed, unknown type, so `(+ $x 1)` with `$x : $a`
is an error. A type variable that only the result mentions is the function's
own choice, unknown to its callers.

**Branches.** The value of an `if`, `case` or `superpose` has the type its
alternatives agree on, else the union of theirs, so every alternative must fit
where the value is used.

**Holding arguments.** A parameter declared `Atom` receives its argument
unevaluated, and a function declared to return `Atom` returns its body as data.

**Committing.** `(-[det]-> A B)` and `(-[semidet]-> A B)` are the contract
`(-> A B)` that also commits the function to the first clause whose head
matches.

**Overloads.** For a name with several declarations, each call is checked
against the declarations its arguments fit, and the result must fit one of
them.

**Ascription.** `(the T E)` checks `E` against `T`, at runtime where needed,
and gives the result the type `T`. It is how a union or a type variable is
narrowed.

**Trusted, not checked.** Builtins implemented in Prolog test their own
arguments. A polymorphic function's result is trusted to fit the caller's
instance. A function imported from Prolog has only a `Number`, `String` or
`Bool` result checked. Undeclared functions are not checked at all.

**Flags.** `--warn-runtime-checks` reports every runtime check compiled in;
`--oracle` and `--no-type-checks` are used by `examples/soundness_matrix.sh`.

[TYPES.md](TYPES.md) gives the rules, the code they generate and the argument
that they are sound.

## Notebooks, Servers, Browser

### Jupyter Notebook Support

A Jupyter kernel for PeTTa is available in a separate repository for interactive MeTTa development in notebooks.

**Repository:** [trueagi-io/jupyter-petta-kernel](https://github.com/trueagi-io/jupyter-petta-kernel)

Quick install:

```bash
# Set PETTA_PATH to this PeTTa installation
export PETTA_PATH=/path/to/PeTTa

# Clone and install the kernel
git clone https://github.com/trueagi-io/jupyter-petta-kernel.git
cd jupyter-petta-kernel
./install.sh
```

Please see the [jupyter-petta-kernel README](https://github.com/trueagi-io/jupyter-petta-kernel/blob/main/README.md) for detailed installation instructions and usage.

### MeTTa server

A HTTP server running MeTTa code is also available:

**Repository:** [MettaWamJam](https://github.com/trueagi-io/MettaWamJam)

Please see the [MettaWamJam README](https://github.com/trueagi-io/MettaWamJam/blob/main/README.md) for detailed installation instructions and usage.

### MeTTa in WASM

Since Swi-Prolog can be compiled to Web Assembly, one can embed PeTTa into websites.

Please see [Execution-in-browser](https://github.com/patham9/PeTTa/wiki/Execution-in-browser) for more information.
