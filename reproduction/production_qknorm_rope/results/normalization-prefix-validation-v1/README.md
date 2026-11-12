This validates the partial normalization-prefix packet, not a complete kernel certificate.

The 95 archived source files match commit `8bf62f9b3c255212b95b10e70126abfafe2ba84d`. A second invocation of the frozen `check_execution_prefix.py` copied a fresh dependency closure into a new project with no seeded owned proof cache. Its PATH contained only symlinks to pinned Lean/Lake 4.19.0; Git was unavailable, and LEAN_PATH and PYTHONPATH were removed. All 245 library and 104 source-bound audits and the nine successful check records matched the first run.

To repeat, unpack `../normalization-prefix-v1/source.tar.gz` into a new directory, then run the included `reproduction/production_qknorm_rope/check_execution_prefix.py` with `--output` pointing outside that source directory and `--lean-bin` pointing to pinned Lean 4.19.0. The runner copies source files only and constructs the project proof cache afresh.
