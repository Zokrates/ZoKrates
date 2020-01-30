import { appendExtension, getAbsolutePath } from './utils';
import stdlib from './stdlib.json';

const initialize = async () => {

  const EXTENSION_ZOK  = '.zok';
  const RESERVED_PATHS = [
    'ecc/',
    'signature/',
    'hashes/',
    'utils/'
  ];

  // load web assembly module
  const zokrates = await import('./pkg/index.js');

  const resolveModule = (location, path, callback) => {
    if (isReserved(location) || isReserved(path)) {
        return resolveFromStandardLibrary(location, path);
    }
    return callback(location, path);
  }

  const isReserved = (path) => RESERVED_PATHS.some(p => path.startsWith(p));

  const resolveFromStandardLibrary = (location, path) => {
    let key = appendExtension(getAbsolutePath(location, path), EXTENSION_ZOK);
    let source = stdlib[key];
    return source ? { source, location: key } : null;
  }

  return {
    compile: (source, location, callback) => {
        let result = zokrates.compile(source, location, (location, path) => 
          resolveModule(location, path, callback)
        );
        return {
            program: Array.from(result.program),
            abi: result.abi
        }
    },
    setup: (program) => {
      let result = zokrates.setup(program);
      return { 
        vk: result.vk,
        pk: Array.from(result.pk)
      };
    },
    computeWitness: (artifacts, args) => {
      return zokrates.compute_witness(artifacts, JSON.stringify(Array.from(args)));
    },
    exportSolidityVerifier: (verifyingKey, isAbiv2) => {
      return zokrates.export_solidity_verifier(verifyingKey, isAbiv2);
    },
    generateProof: (program, witness, provingKey) => {
      return zokrates.generate_proof(program, witness, provingKey);
    }
  }
}

export { initialize };