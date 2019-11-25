# zokrates.js

You can get JavaScript bindings for ZoKrates by running

```bash
npm install zokrates-js
```

## API

| Function | Description |
| ------ | ------ |
| initialize | Loads binding wasm module and sets necessary callbacks |
| compile | Compiles source code into ZoKrates internal representation of arithmetic circuits |
| computeWitness | Computes a valid assignment of the variables, which include the results of the computation |
| setup | Generates a trusted setup for the compiled program |
| exportSolidityVerifier | Generates a Solidity contract which contains the generated verification key and a public function to verify a solution to the compiled program |
| generateProof | Generates a proof for a computation of the compiled program |

## Usage

```js
import * as zokrates from 'zokrates-js'

function importResolver(location, path) {
  // implement your resolving logic here
  return { 
    source: "def main() -> (): return", 
    location: path 
  };
}

zokrates.initialize(importResolver).then(() => {
    // we have to initialize wasm module before calling api functions
    zokrates.compile("def main(private field a) -> (field): return a", "main")
});
```
