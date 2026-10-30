<!-- SPDX-License-Identifier: GPL-3.0-or-later -->
# Security policy

This repository contains Lean 4 proof sources only; it does not ship an
executable, renderer, network service, or runtime component.

- For security issues in the gX engine or its tools, use the
  [gX security policy](https://github.com/lanttusoft/gX/blob/main/SECURITY.md).
- For a suspected soundness problem in a proof or specification, open an issue
  with the module name, theorem, and a minimal counterexample or failing
  `lake build` output. Do not include private engine data, credentials, or
  unpublished assets.

Do not open a public issue for a suspected engine vulnerability.
