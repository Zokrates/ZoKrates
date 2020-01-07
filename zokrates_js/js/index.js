import { appendExtension, getAbsolutePath } from './utils';
import stdlib from '../stdlib.json';

const initialize = async () => {

  const EXTENSION_ZOK  = '.zok';
  const RESERVED_PATHS = [
    'ecc/',
    'signature/',
    'hashes/', 
    'utils/'
  ];

  // load web assembly module
  const zokrates = await import('../pkg/index.js');

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
      return Uint8Array.from(
        zokrates.compile(source, location, (location, path) => resolveModule(location, path, callback))
      );
    },
    setup: (program) => {
      let result = zokrates.setup(Array.from(program));
      return { 
        vk: result.vk, 
        pk: Uint8Array.from(result.pk) 
      };
    },
    computeWitness: (program, args) => {
      const input = JSON.stringify(Array.from(args));
      return zokrates.compute_witness(Array.from(program), input);
    },
    exportSolidityVerifier: (verifyingKey, isAbiv2) => {
      return zokrates.export_solidity_verifier(verifyingKey, isAbiv2);
    },
    generateProof: (program, witness, provingKey) => {
      return zokrates.generate_proof(Array.from(program), witness, Array.from(provingKey));
    }
  }
}

export { initialize }