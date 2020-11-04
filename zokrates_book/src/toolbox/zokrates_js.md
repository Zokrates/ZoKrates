# zokrates.js

JavaScript bindings for [ZoKrates](https://github.com/Zokrates/ZoKrates).

```bash
npm install zokrates-js
```

## Importing

##### Bundlers
**Note:** As this library uses a model where the wasm module itself is natively an ES module, you will need a bundler of some form. 
Currently the only known bundler known to be fully compatible with `zokrates-js` is [Webpack](https://webpack.js.org/). 
The choice of this default was done to reflect the trends of the JS ecosystem.
```js
import { initialize } from 'zokrates-js';
```

##### Node
```js
const { initialize } = require('zokrates-js/node');
```

## Example
```js
initialize().then((zokratesProvider) => {
    const source = "def main(private field a) -> field: return a * a";

    // compilation
    const artifacts = zokratesProvider.compile(source);

    // computation
    const { witness, output } = zokratesProvider.computeWitness(artifacts, ["2"]);

    // run setup
    const keypair = zokratesProvider.setup(artifacts.program);

    // generate proof
    const proof = zokratesProvider.generateProof(artifacts.program, witness, keypair.pk);

    // export solidity verifier
    const verifier = zokratesProvider.exportSolidityVerifier(keypair.vk, "v1");
});
```

## API

##### initialize()
Returns an initialized `ZoKratesProvider` as a promise.

```js
initialize().then(zokratesProvider => { 
    // call api functions here
});
```

Returns: `Promise<ZoKratesProvider>`

##### compile(source[, options])
Compiles source code into ZoKrates internal representation of arithmetic circuits.

Parameters:
* `source` - Source code to compile
* `options` - Compilation options

Returns: `CompilationArtifacts`

**Examples:**

Compilation:
```js
const artifacts = zokratesProvider.compile("def main() -> (): return");
```

Compilation with custom options:
```js
const source = "...";
const options = {
    location: "main.zok", // location of the root module
    resolveCallback: (currentLocation, importLocation) => {
        console.log(currentLocation + ' is importing ' + importLocation);
        return { 
            source: "def main() -> (): return", 
            location: importLocation 
        };
    }
};
const artifacts = zokratesProvider.compile(source, options);
```

**Note:** The `resolveCallback` function is used to resolve dependencies. 
This callback receives the current module location and the import location of the module which is being imported. 
The callback must synchronously return either an error, `null` or a valid `ResolverResult` object like shown in the example above.

##### computeWitness(artifacts, args)
Computes a valid assignment of the variables, which include the results of the computation.

Parameters:
* `artifacts` - Compilation artifacts
* `args` - Array of arguments (eg. `["1", "2", true]`)

Returns: `ComputationResult`

**Example:**

```js
const code = 'def main(private field a) -> (field): return a * a';
const artifacts = zokratesProvider.compile(code);

const { witness, output } = zokratesProvider.computeWitness(artifacts, ["2"]);

console.log(witness); // Resulting witness which can be used to generate a proof
console.log(output); // Computation output: ["4"]
```

##### setup(program)
Generates a trusted setup for the compiled program.

Parameters:
* `program` - Compiled program

Returns: `SetupKeypair`

##### exportSolidityVerifier(verificationKey, abi)
Generates a Solidity contract which contains the generated verification key and a public function to verify proofs of computation of the compiled program.

Parameters:
* `verificationKey` - Verification key from the setup keypair
* `abi` - Abi version (`"v1"` | `"v2"`)

Returns: `string`

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
