import { appendExtension, getAbsolutePath } from './utils';
import stdlib from './stdlib.json';

const initialize = async () => {

  // load web assembly module
  const zokrates = await import('./pkg/index.js');

  const resolveFromStdlib = (currentLocation, importLocation) => {
    let key = appendExtension(getAbsolutePath(currentLocation, importLocation), '.zok');
    let source = stdlib[key];
    return source ? { source, location: key } : null;
  }

  return {
    compile: (source, location, callback, config) => {
        let importCallback = (currentLocation, importLocation) => {
            return resolveFromStdlib(currentLocation, importLocation) || callback(currentLocation, importLocation);
        };
        const { program, abi } = zokrates.compile(source, location, importCallback, config);
        return {
            program: Array.from(program),
            abi
        }
    },
    setup: (program) => {
      const { vk, pk } = zokrates.setup(program);
      return { 
        vk,
        pk: Array.from(pk)
      };
    },
    computeWitness: (artifacts, args) => {
      return zokrates.compute_witness(artifacts, JSON.stringify(Array.from(args)));
    },
    exportSolidityVerifier: (verifyingKey, abiVersion) => {
      return zokrates.export_solidity_verifier(verifyingKey, abiVersion);
    },
    generateProof: (program, witness, provingKey) => {
      return zokrates.generate_proof(program, witness, provingKey);
    }
  }
}

export { initialize };