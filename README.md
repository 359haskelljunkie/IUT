# IUT Lean Formalization Proposal — Version 0.1

This repository contains an independent research note and a skeletal Lean 4
implementation inspired by §4 of Shinichi Mochizuki's April 2026 preliminary
progress report.

## Files

- `article.txt` — plain-text research note.
- `IUTSketch.lean` — Lean 4 source file.

## Scope

This is not Mochizuki/RIMS/LANA code and is not a formal proof of IUT
Theorem 3.11, the intermediate label 3.11.5, or Corollary 3.12.

The code formalizes a category/mutation interface, a compositional HDD
interface, and a conditional arithmetic height inequality. It does not
derive the simultaneous comparison estimate from SHE, IPL, APT, descent,
or the hull-and-determinant construction.

## Build

Use a Lean 4 project with Mathlib installed, place `IUTSketch.lean` in the
project, and run:

    lake env lean IUTSketch.lean

For a public release, pin the exact Lean and Mathlib versions in
`lean-toolchain` and `lakefile.toml`, then record a successful build log.
