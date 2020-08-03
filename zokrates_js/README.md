# zokrates.js

JavaScript bindings for [ZoKrates](https://github.com/Zokrates/ZoKrates) project.

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
function importResolver(currentLocation, importLocation) {
  console.log(currentLocation + ' is importing ' + importLocation);
  // implement your resolving logic here
  return {
    source: "def main() -> (): return",
    location: importLocation
  };
}

initialize().then((zokratesProvider) => {
    const source = "def main(private field a) -> (field): return a * a";

    // compilation
    const artifacts = zokratesProvider.compile(source, "main", importResolver);

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
Loads binding wasm module and returns a promise with ZoKrates provider.

Returns: `Promise<ZoKratesProvider>`

##### compile(source, location, resolveCallback[, config])
Compiles source code into ZoKrates internal representation of arithmetic circuits.

Parameters:
* `source` - Source code to compile
* `location` - Root location of the module which is being compiled
* `resolveCallback` - User-defined callback used to resolve imports
* `config` - Compilation config

Returns: `CompilationArtifacts`

##### computeWitness(artifacts, args)
Computes a valid assignment of the variables, which include the results of the computation.

Parameters:
* `artifacts` - Compilation artifacts
* `args` - Array of arguments (eg. `["1", "2", true]`)

Returns: `ComputationResult`

##### setup(program)
Generates a trusted setup for the compiled program.

Parameters:
* `program` - Compiled program

Returns: `SetupKeypair`

##### exportSolidityVerifier(verificationKey, abi)
Generates a Solidity contract which contains the generated verification key and a public function to verify a solution to the compiled program.

Parameters:
* `verificationKey` - Verification key from the setup keypair
* `abi` - Abi version (`"v1"` | `"v2"`)

Returns: `string`

##### generateProof(program, witness, provingKey)
Generates a proof for a computation of the compiled program.

Parameters:
* `program` - Compiled program
* `witness` - Witness (valid assignment of the variables)
* `provingKey` - Proving key from the setup keypair

Returns: `Proof`