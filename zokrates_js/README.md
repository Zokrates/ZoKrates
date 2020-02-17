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

```js
import { initialize } from 'zokrates-js';

function importResolver(location, path) {
  // implement your resolving logic here
  return { 
    source: "def main() -> (): return", 
    location: path 
  };
}

initialize().then((zokratesProvider) => {
    // we have to initialize the wasm module before calling api functions
    zokratesProvider.compile("def main(private field a) -> (field): return a", "main", importResolver)
});
```
