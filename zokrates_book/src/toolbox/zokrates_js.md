# zokrates.js

JavaScript bindings for [ZoKrates](https://github.com/Zokrates/ZoKrates).

```bash
npm install zokrates-js
```

## Importing

##### Bundlers
**Note:** As this library uses a model where the wasm module itself is natively an ES module, you will need a bundler of some form. 
Currently the only known bundler known to be fully compatible with `zokrates-js` is [Webpack](https://webpack.js.org/) (`experiments.syncWebAssembly` must be enabled). 
The choice of this default was done to reflect the trends of the JS ecosystem.
```js
import { initialize } from 'zokrates-js';
```

##### Node
```js
const { initialize } = require('zokrates-js')
```

## Example
```js
initialize().then((zokratesProvider) => {
    const source = "def main(private field a) -> field { return a * a; }";

    // compilation
    const artifacts = zokratesProvider.compile(source);

    // computation
    const { witness, output } = zokratesProvider.computeWitness(artifacts, ["2"]);

    // run setup
    const keypair = zokratesProvider.setup(artifacts.program);

    // generate proof
    const proof = zokratesProvider.generateProof(artifacts.program, witness, keypair.pk);

    // export solidity verifier
    const verifier = zokratesProvider.exportSolidityVerifier(keypair.vk);
    
    // or verify off-chain
    const isVerified = zokratesProvider.verify(keypair.vk, proof);
});
```

## API

##### initialize()
Returns an initialized `ZoKratesProvider` as a promise.

```js
initialize().then((zokratesProvider) => { 
    // call api functions here
});
```

Returns: `Promise<ZoKratesProvider>`

##### withOptions(options)
Returns a `ZoKratesProvider` configured with given options.

```js
initialize().then((defaultProvider) => { 
    let zokratesProvider = defaultProvider.withOptions({ 
        backend: "ark",
        curve: "bls12_381",
        scheme: "g16"
    });
    // ...
});
```

Options:
* `backend` - Backend (options: `ark` | `bellman`, default: `ark`)
* `curve` - Elliptic curve (options: `bn128` | `bls12_381` | `bls12_377` | `bw6_761`, default: `bn128`)
* `scheme` - Proving scheme (options: `g16` | `gm17` | `marlin`, default: `g16`)

Returns: `ZoKratesProvider`

##### compile(source[, options])
Compiles source code into ZoKrates internal representation of arithmetic circuits.

Parameters:
* `source` - Source code to compile
* `options` - Compilation options

Returns: `CompilationArtifacts`

**Examples:**

Compilation:
```js
const artifacts = zokratesProvider.compile("def main() { return; }");
```

Compilation with custom options:
```js
const source = "...";
const options = {
    location: "main.zok", // location of the root module
    resolveCallback: (currentLocation, importLocation) => {
        console.log(currentLocation + ' is importing ' + importLocation);
        return { 
            source: "def main() { return; }", 
            location: importLocation 
        };
    }
};
const artifacts = zokratesProvider.compile(source, options);
```

**Note:** The `resolveCallback` function is used to resolve dependencies. 
This callback receives the current module location and the import location of the module which is being imported. 
The callback must synchronously return either an error, `null` or a valid `ResolverResult` object like shown in the example above. 
A simple file system resolver for a node environment can be implemented as follows:

```js
const fs = require("fs");
const path = require("path");

const fileSystemResolver = (from, to) => {
  const location = path.resolve(path.dirname(path.resolve(from)), to);
  const source = fs.readFileSync(location).toString();
  return { source, location };
};
```

##### computeWitness(artifacts, args[, options])
Computes a valid assignment of the variables, which include the results of the computation.

Parameters:
* `artifacts` - Compilation artifacts
* `args` - Array of arguments (eg. `["1", "2", true]`)
* `options` - Computation options

Returns: `ComputationResult`

**Example:**

```js
const code = 'def main(private field a) -> field { return a * a; }';
const artifacts = zokratesProvider.compile(code);

const { witness, output } = zokratesProvider.computeWitness(artifacts, ["2"]);

console.log(witness); // Resulting witness which can be used to generate a proof
console.log(output); // Computation output: "4"
```

##### setup(program)
Generates a trusted setup for the compiled program.

Parameters:
* `program` - Compiled program

Returns: `SetupKeypair`

##### universalSetup(size)
Performs the universal phase of a trusted setup. Only available for the `marlin` scheme.

Parameters:
* `size` - Size of the trusted setup passed as an exponent. For example, `8` for `2**8`.

Returns: `Uint8Array`

##### setupWithSrs(srs, program)
Generates a trusted setup with universal public parameters for the compiled program. Only available for `marlin` scheme.

Parameters:
* `srs` - Universal public parameters from the universal setup phase
* `program` - Compiled program

Returns: `SetupKeypair`

##### generateProof(program, witness, provingKey)
Generates a proof for a computation of the compiled program.

Parameters:
* `program` - Compiled program
* `witness` - Witness (valid assignment of the variables) from the computation result
* `provingKey` - Proving key from the setup keypair

Returns: `Proof`

##### verify(verificationKey, proof)
Verifies the generated proof.

Parameters:
* `verificationKey` - Verification key from the setup keypair
* `proof` - Generated proof

Returns: `boolean`

##### exportSolidityVerifier(verificationKey)
Generates a Solidity contract which contains the generated verification key and a public function to verify proofs of computation of the compiled program.

Parameters:
* `verificationKey` - Verification key from the setup keypair

Returns: `string`
