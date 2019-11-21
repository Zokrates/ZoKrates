# zokrates-js
JavaScript bindings for [ZoKrates](https://github.com/Zokrates/ZoKrates) project. The goal of this project is to provide ZoKrates JavaScript API supporting both node.js and the web. ZoKrates is a toolbox for zkSNARKs on Ethereum that helps you use verifiable computation in your DApp, from the specification of your program in a high level language to generating proofs of computation and verifying those proofs in Solidity.

[![CircleCI](https://circleci.com/gh/Zokrates/zokrates-js/tree/master.svg?style=svg)](https://circleci.com/gh/Zokrates/zokrates-js/tree/master)

## Package
Install zokrates-js with [npm](https://www.npmjs.com/package/zokrates-js):

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

### Usage
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

## Installation
Install rustup and wasm-pack:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
```

In order to compile this project you need the *nightly* version of Rust. You can install all of this by running:

```bash
rustup install nightly
rustup target add wasm32-unknown-unknown --toolchain nightly
rustup default nightly
```

## Development
Anyone is welcome to help progress and improve this library. Tasks and issues can be found in the [issues tab](https://github.com/Zokrates/ZoKrates/issues). If your problem/task is not in the tasks, feel free to create a new issue explaining your problem/task.