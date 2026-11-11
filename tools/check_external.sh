#!/usr/bin/env bash
# Re-check the main theorems with the external checkers that ship with the
# Lean 4.35.0 toolchain (lean4export + nanoda, con-leche, con-ron) and with
# the kernel replay tool leanchecker.  Run from the repository root after
# `lake build`.
#
#   Problem 1 (4x4): only the three standard axioms are permitted.
#   Problem 2 (6x6): additionally the three axioms recording the results of
#                    compiled computations (two searches, one SAT certificate).
#   Problem 3 (8x8): additionally the axiom takizawa_results (the published
#                    table of "Othello is Solved") and the two axioms recording
#                    the searches of the first ten plies.
set -euo pipefail
out=$(mktemp -d)

echo "== leanchecker (kernel replay) =="
lake env leanchecker Othello.Four

echo "== export =="
lake env leanexport Othello.Four -- Othello.white_wins_4x4 Othello.othello_4x4 > "$out/four.ndjson"
lake env leanexport Othello.Six -- Othello.othello_6x6 > "$out/six.ndjson"
lake env leanexport Othello.Eight -- Othello.othello_8x8 Othello.othello_8x8_of_table > "$out/eight.ndjson"

cat > "$out/four.json" <<JSON
{ "export_file_path": "$out/four.ndjson",
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true,
  "nat_extension": true, "string_extension": true,
  "pp_declars": ["Othello.white_wins_4x4", "Othello.othello_4x4"], "pp_to_stdout": true,
  "print_success_message": true }
JSON
cat > "$out/six.json" <<JSON
{ "export_file_path": "$out/six.ndjson",
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound",
    "Othello.search_black6._native.native_decide.ax_1_1",
    "Othello.search_white6._native.native_decide.ax_1_1",
    "Othello.popcount_eq_cntBits6._native.bv_decide.ax_1_8"],
  "unpermitted_axiom_hard_error": true,
  "nat_extension": true, "string_extension": true,
  "pp_declars": ["Othello.othello_6x6"], "pp_to_stdout": true,
  "print_success_message": true }
JSON

cat > "$out/eight.json" <<JSON
{ "export_file_path": "$out/eight.ndjson",
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound",
    "Othello.takizawa_results",
    "Othello.search8_black._native.native_decide.ax_1_1",
    "Othello.search8_white._native.native_decide.ax_1_1"],
  "unpermitted_axiom_hard_error": true,
  "nat_extension": true, "string_extension": true,
  "pp_declars": ["Othello.othello_8x8_of_table", "Othello.othello_8x8", "Othello.takizawa_results"],
  "pp_to_stdout": true,
  "print_success_message": true }
JSON

echo "== nanoda: Problem 1 =="
nanoda_bin "$out/four.json"
echo "== nanoda: Problem 2 (modulo the three native-computation axioms) =="
nanoda_bin "$out/six.json"

echo "== nanoda: Problem 3 (modulo takizawa_results and the two native-computation axioms) =="
nanoda_bin "$out/eight.json"

if command -v con-leche > /dev/null; then
  echo "== con-leche: Problem 1 =="
  con-leche "$out/four.ndjson"
fi
if command -v con-ron > /dev/null; then
  echo "== con-ron: Problem 1 =="
  con-ron "$out/four.ndjson"
fi
rm -rf "$out"
