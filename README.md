## PeTTa

Efficient MeTTa language implementation in Prolog.

Please check out the [Wiki](https://github.com/patham9/PeTTa/wiki) for more information.

### Dependencies

- SWI-Prolog >= 9.3.x
- Python 3.x (for janus Python interop)

### Usage

Example run:

`time sh run.sh ./examples/nars_tuffy.metta`

### HE compatibility mode

PeTTa also provides a `--he` execution mode for Hyperon Experimental-facing
MeTTa workloads:

`time sh run.sh --he ./examples/he_translated/tilepuzzle_he.metta`

This mode is implemented as a PeTTa compatibility/backend layer rather than a
separate executable. Default PeTTa behavior without `--he` is unchanged.

The exact scope of `--he` is documented here:

- `specs/petta-he-compatibility-profile.md`
- `specs/he-native-backend-contracts.md`
- `src/he/DIVERGENCES.md`
- `HE_MODE_TUTORIAL.md`

Those documents describe:

- what is treated as HE-core exact behavior
- what is supported as PeTTa HE compatibility or extension behavior
- which backend contracts are intentionally narrow
- where current divergences or support-more surfaces are tracked

The translated-example performance budget is:

`he_wall <= default_wall * 2.23 + 0.25s`

The survey writes budget margins to `.he-logs/he_translation_bench.tsv`; run
`tests/tools/summarize_he_translation_budget.awk` for a compact margin report.

### MORK and FAISS spaces

If MORK and FAISS is installed, execute `sh build.sh` to support MORK-based atom spaces and FAISS-based atom-vector spaces.

The following projects are cloned and built by build.sh:

**Repository:** [mork_ffi](https://github.com/patham9/mork_ffi) dependent on [trueagi-io/mork](https://github.com/trueagi-io/mork)

**Repository:** [faiss_ffi](https://github.com/patham9/faiss_ffi) dependent on [facebookresearch/faiss](https://github.com/facebookresearch/faiss)

### Extension libraries

Please check out [Extension libraries](https://github.com/trueagi-io/PeTTa/wiki/Extension-libraries) for a set of extension libraries that can be invoked from MeTTa files directly from the git repository.

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

**Repository:** [MettaWamJam](https://github.com/jazzbox35/MettaWamJam)

Please see the [MettaWamJam README](https://github.com/jazzbox35/MettaWamJam/blob/main/README.md) for detailed installation instructions and usage.

### MeTTa in WASM

Since Swi-Prolog can be compiled to Web Assembly, one can embed PeTTa into websites.

Please see [Execution-in-browser](https://github.com/patham9/PeTTa/wiki/Execution-in-browser) for more information.
