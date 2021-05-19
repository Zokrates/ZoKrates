# Changelog
All notable changes to this project will be documented in this file.

## [Unreleased]
https://github.com/Zokrates/ZoKrates/compare/latest...develop

## [0.7.3] - 2021-05-19

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.3

### Changes
- Remove substitution in `one_liner.sh` script which caused `Bad substitution` error with `sh`/`dash` (#877, @dark64)
- Put branch isolator behind a compilation flag in the static analyzer (#877, @dark64)

## [0.7.2] - 2021-05-18

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.2

### Changes
- Isolate branch panics: only panic in a branch if it's being logically executed (#865, @schaeff)
- Support the use of constants in struct and function declarations (#864, @dark64)
- Relax ordering of symbol declarations (#863, @dark64)
- Update `one_liner.sh` script to support arm64 architecture (#861, @dark64)
- Fix crash when updating a constant struct member to another constant (#855, @schaeff)
- Fix treatment of uint subtraction involving constants (bug) (#852, @schaeff)
- Add uint to abi docs (#848, @schaeff)
- Remove side effects on complex types (bug) (#847, @schaeff)
- Fix crash on struct member type mismatch (#846, @schaeff)
- Fix nested struct access crash (#845, @schaeff)
- Make error formatting consistent (#843, @schaeff)

## [0.7.1] - 2021-04-30

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.1

### Changes
- Fix integer inference on repeat operators (#834, @schaeff)
- Introduce constant definitions to the language (`const` keyword) (#792, @dark64)
- Introduce constant range checks for checks of the form `x < c` where `p` is a compile-time constant, also for other comparison operators. This works for any `x` and `p`, unlike dynamic `x < y` comparison (#761, @schaeff)
- Handle errors more gracefully in propagation step where applicable (#832, @dark64)
- Add interactive prompt before overwriting existing files in the `one_liner.sh` script (#831, @dark64)
- Add a custom panic hook to handle internal compiler errors more gracefully (#829, @dark64)
- Make command line errors compatible with editor cmd+click (#828, @schaeff)
- Make function definitions more permissive, and move ambiguity checks to call sites and improve them (#826, @schaeff)
- Detect assertion failures at compile time on constant expressions (#823, @dark64)
- Make function selection stricter in function calls (#822, @schaeff)
- Add the ability to import multiple symbols in a single import statement (#809, @dark64)
- Add [poseidon](https://www.poseidon-hash.info/) zk-friendly hashing algorithm to stdlib (#806, @dark64)
- Allow optional underscore before type suffix (e.g. `42_u32`) (#800, @dark64)
- Accept explicit generic parameters outside of definitions (#798, @schaeff)

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