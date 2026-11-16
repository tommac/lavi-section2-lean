#!/usr/bin/env bash
# Independent kernel check of the final theorems.
#
# Exports the dependency closure of the final theorems (including Mathlib and RealRooted)
# with the toolchain's `leanexport`, then checks the export with `nanoda_bin`, an
# independent Lean type checker written in Rust, permitting only Lean's three standard
# axioms: any other axiom in the export is a hard error.  Unlike `#print axioms`, this does
# not rely on axiom lists recorded in the compiled files.
#
# Run from the repository root after `lake build`.  The export is about 400 MB and is
# deleted afterwards.
set -euo pipefail

PREFIX="$(lake env lean --print-prefix)"
for tool in leanexport nanoda_bin; do
  if [ ! -x "$PREFIX/bin/$tool" ]; then
    echo "missing $PREFIX/bin/$tool (expected in the Lean toolchain)" >&2
    exit 1
  fi
done

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

DECLS=(
  LaviSection2.foregger_conjecture
  LaviSection2.foregger_bound
  LaviSection2.lavi_theorem_1_1_unconditional
  LaviSection2.lavi_theorem_1_1_moreover_unconditional
  LaviSection2.foreggerSharpAt_all
  LaviSection2.gurvitsCapacityInequality
)

lake env "$PREFIX/bin/leanexport" LaviSection2.LaviTheorem11Unconditional -- "${DECLS[@]}" \
  > "$WORK/export.ndjson"
echo "exported $(wc -c < "$WORK/export.ndjson") bytes"

# nanoda prints the checked statements of DECLS back, so the log shows what was checked.
PP_DECLS="$(printf '"%s", ' "${DECLS[@]}")"
PP_DECLS="[${PP_DECLS%, }]"

cat > "$WORK/nanoda.json" <<EOF
{
  "export_file_path": "$WORK/export.ndjson",
  "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true,
  "nat_extension": true,
  "string_extension": true,
  "pp_declars": $PP_DECLS,
  "pp_to_stdout": true,
  "pp_options": {"explicit": false, "proofs": false, "indent": 2, "width": 100},
  "print_success_message": true
}
EOF

"$PREFIX/bin/nanoda_bin" "$WORK/nanoda.json"
