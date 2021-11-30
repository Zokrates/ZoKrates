# Changelog
All notable changes to this project will be documented in this file.

## [Unreleased]
https://github.com/Zokrates/ZoKrates/compare/latest...develop

## [0.7.8] - 2021-11-23

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.8 <!-- markdown-link-check-disable-line -->

### Changes
- Fix reduction of constants (#1050, @schaeff)
- Implement type aliasing (#982, @dark64)
- Remove confusing returns (#1037, @schaeff)
- Reduce cost of dynamic comparison (#1025, @schaeff)
- Fix false positives and false negatives in struct generic inference (#1016, @schaeff)
- Make field to uint casts truncate values bigger than uint max (#997, @dark64)
- Add Marlin proving scheme to the backend table in the book (#1034, @schaeff)
- Fail at compile time when complex types are known not to be equal (#1032, @schaeff)
- Allow more postfix expressions, exit gracefully when trying to call anything else than an identifier (#1030, @schaeff)
- Add optional message to assert statement (#1012, @dark64)
- Introduce ternary operator (#1010, @dark64)

## [0.7.7] - 2021-10-04

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.7 <!-- markdown-link-check-disable-line -->

### Changes
- Reduce the deployment cost of the g16 and pghr13 verifiers (#1008, @m1cm1c)
- Make operators table more clear in the book (#1017, @dark64)
- Allow calls in constant definitions (#975, @schaeff)
- Handle out of bound accesses gracefully (#1013, @schaeff)
- Improve error message on unconstrained variable detection (#1015, @dark64)
- Apply propagation in ZIR (#957, @dark64)
- Fail on mistyped constants (#974, @schaeff)
- Graceful error handling on unconstrained variable detection (#977, @dark64)
- Fix incorrect propagation of spreads (#987, @schaeff)
- Add range semantics to docs (#992, @dark64)
- Fix invalid cast to `usize` which caused wrong values in 32-bit environments (#998, @dark64)

## [0.7.6] - 2021-08-16

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.6 <!-- markdown-link-check-disable-line -->

### Changes
- Fix stack overflow when testing equality on large arrays (#969, @schaeff)
- Make the stdlib `unpack` function safe against overflows of bit decompositions for any size of output, introduce `unpack_unchecked` for cases that do not require determinism (#955, @schaeff)
- Add explicit function generic parameters to docs (#962, @schaeff)
- Add gm17 verifier to stdlib for bw6_761 (#948, @schaeff)
- Enable constant generics on structs (#945, @schaeff)
- Use constants in the standard library, make `mimcSponge` implementation generic (#942, @dark64)
- Fix constant range check in uint lt check (#954, @schaeff)
- Add compiler logs (#950, @schaeff)
- Fix state corruption in the constant inliner (#949, @schaeff)
- Fix abi encoder bug for struct values where the members are encoded in the wrong order (#947, @schaeff)
- Bump Solidity version to latest breaking release and use Solidity's ABI v2. This means that the `export-verifier` CLI flag to choose the ABI coder was removed. (#844, @leonardoalt)

## [0.7.5] - 2021-07-10

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.5 <!-- markdown-link-check-disable-line -->

### Changes
- Allow field inputs in hexadecimal form in case the abi specification is used (#932, @dark64)
- Add hints to runtime errors (#931, @schaeff)
- Reduce cost of variable memory access (#930, @schaeff)
- Add support for the Marlin proving scheme (#927, @schaeff)
- Add a CLI option `generate-smtlib2` to output the compiled IR as an SMT formula. (#919, @leonardoalt)
- Introduce the `snark_verify_bls12_377` embed for one-layer composition of SNARK proofs (over `BLS12-377`/`BW6-761` pair of curves where `BW6-761` is used as an outer curve to `BLS12-377`) (#918, @dark64)
- Add details to for-loop documentation (#924, @schaeff)

## [0.7.4] - 2021-06-17

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/0.7.4 <!-- markdown-link-check-disable-line -->

### Changes
- Add `FIELD_SIZE_IN_BITS`, `FIELD_MIN` and `FIELD_MAX` constants to `field` stdlib module (#917, @dark64)
- Fix crash on import of functions containing constants (#913, @schaeff)
- Change endianness in keccak, sha3 and blake2s hash algorithms to big endian (#906, @dark64)
- Documentation improvements, move examples to a separate section, remove deprecated `--light` flag used in a rng tutorial, add a simple file system resolver example to zokrates.js docs (#914, @dark64)
- Fixed deserialization logic in the zokrates.js that caused issues on cli-compiled binaries (#912, @dark64)
- Reduce the cost of conditionals (#907, @schaeff)
- Improve propagation on if-else expressions when consequence and alternative are equal (#905, @schaeff)
- Fix access to constant in local function call (#910, @schaeff)
- Fix parsing of the left hand side of definitions (#896, @schaeff)
- Fix variable write remover when isolating branches (#904, @schaeff)
- Introduce a limit of 2**20 for for-loop sizes (#902, @schaeff)
- Run compilation test on RNG tutorial and fix bugs (#881, @axic)

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