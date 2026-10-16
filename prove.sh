#!/usr/bin/env bash
# moon-algebra — formal proof runner (moon prove + Why3 + Z3/cvc5)
#
# Ingredients (all checked into this repository):
#   prelude/moonbit_builtin_prelude.mlw  custom proof prelude: minimal
#     truncated-division theory + Div_exact/Mod_exact one-step rules
#     (the stdlib Computer* axiom set makes z3 blow up on these VCs)
#   why3-user.conf                       strategy: Z3 quick passes, then
#     split_vc, then Z3, then cvc5 (which closes the remaining goals)
#
# Requirements: why3, z3, cvc5 on PATH; MoonBit toolchain in ~/.moon.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.moon/bin:$PATH"
export MOON_PROVE_PRELUDE_OVERRIDE="$PWD/prelude"
exec moon prove verify --why3-config "$PWD/why3-user.conf" "$@"
