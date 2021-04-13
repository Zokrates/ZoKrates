# Changelog
All notable changes to this project will be documented in this file.

## [Unreleased]
https://github.com/Zokrates/ZoKrates/compare/latest...develop

## [0.7.0] - 2021-04-09

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.0

### Changes
- Re-export embed functions as stdlib modules, add field to uint casts to stdlib (#801, @dark64)
- Change left `<<` and right `>>` shifts to take `u32` as a second parameter (#783, @schaeff)
- Introduce u64 type, add keccak{256,384,512} and sha3{256,384,512} hash functions to stdlib (#772, @dark64)
- Add negative `-` and positive `+` unary operators, restricting accepted expressions in some places (exponent) to allow for better parsing (#762, @schaeff)
- Make embed functions generic, enabling unpacking to any width at minimal cost (#754, @schaeff)
- Add global `--verbose` flag to CLI for verbose logging, add `--ztf` flag to `compile` command, deprecate `--light` flag as its behaviour is now a default. (#751, @dark64)
- Introduce constant generics for `u32` values. Introduce literal inference (#695, @schaeff)

## [0.6.4] - 2021-03-19
### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.6.4

### Changes
- re-include embeds for a slightly cheaper sha256
- remove array ssa
- add flag to allow unconstrained variables
- better flattening of conjunctions
- put backends behind features
- accept any assignee in multidef
- minor performance and stability improvements

For older releases and changes, visit https://github.com/Zokrates/ZoKrates/releases.