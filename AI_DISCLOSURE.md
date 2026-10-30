<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# AI usage and limitations

gX proofs is developed with AI assistance. This page explains what that means
and what it does not guarantee.

## What AI is used for

AI coding assistants, including OpenCode and the configured models, have been
used for proof drafting, refactoring, documentation, and audit tooling.
AI-assisted changes are marked in the source with `--ai:` or the legacy
`--opencode:` marker where practical. The project policy is the same as the
engine: the author owns the final decision and the review.

## Review is risk reduction, not proof

The author reviews the proof sources, and the kernel/audit gates check
reachability and trust dependencies. Those checks reduce risk, but they do not
prove that the formal model matches the C implementation, that the
specification is the right one, or that a proof is free of mistakes.

AI tools can make mistakes. They can produce incorrect, incomplete, or
misleading proofs and comments; they can miss edge cases; and they can state
things with more confidence than the evidence supports. Reviewers can miss
those problems too.

## Disclaimer

The proof sources are provided **"as is"**, without warranty of any kind, under
the GNU General Public License v3.0 or later. Nothing in this repository is
legal, security, fitness-for-purpose, or professional advice. You are
responsible for reviewing the specifications, proofs, dependencies, and
licenses before relying on them.

The kernel audit establishes only what the Lean kernel checks under the stated
assumptions. It does not certify C translation, IEEE floating-point behavior,
GPU/driver behavior, or production runtime equivalence. See the engine's
[`docs/lean_proofs.md`](https://github.com/lanttusoft/gX/blob/main/docs/lean_proofs.md)
for the source-correspondence boundaries.

Report suspected security issues in the engine per the
[gX security policy](https://github.com/lanttusoft/gX/blob/main/SECURITY.md).
