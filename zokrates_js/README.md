# zokrates.js

JavaScript bindings for [ZoKrates](https://github.com/Zokrates/ZoKrates) project.

```bash
npm install zokrates-js
```

## API

| Function | Description |
| ------ | ------ |
| initialize | Loads binding wasm module and returns a promise with ZoKrates provider |
| compile | Compiles source code into ZoKrates internal representation of arithmetic circuits |
| computeWitness | Computes a valid assignment of the variables, which include the results of the computation |
| setup | Generates a trusted setup for the compiled program |
| exportSolidityVerifier | Generates a Solidity contract which contains the generated verification key and a public function to verify a solution to the compiled program |
| generateProof | Generates a proof for a computation of the compiled program |

## Usage

### Importing

Bundlers
```js
import { initialize } from 'zokrates-js';
```

Node
```js
const { initialize } = require('zokrates-js/node');
```

### Example
```js
function importResolver(currentLocation, importLocation) {
  // implement your resolving logic here
  return {
    source: "def main() -> (): return",
    location: importLocation
  };
}

initialize().then((zokratesProvider) => {
    // compilation
    const artifacts = zokratesProvider.compile("def main(private field a) -> (field): return a * a", "main", importResolver);

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