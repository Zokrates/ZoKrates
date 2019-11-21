import { getAbsolutePath, appendExtension } from './utils';
import stdlib from '../stdlib.json';

const __extension = '.zok';
const __reserved  = ['ecc/', 'signature/', 'hashes/', 'utils/'];
var   __state = {};

export async function initialize(callback) {
  let zokrates = await import('../pkg/index.js');
  __state.zokrates = zokrates;

  window.resolve = function (location, path) {
    return __resolve(location, path, callback);
  }
} 

function __isReservedPath(path) {
  return __reserved.some(function (p) { return path.startsWith(p) || path.startsWith(p) })
}

function __resolve(location, path, callback) {
  let result;
  if(__isReservedPath(location)) {
    result = resolveFromStdlib(location, path);
  } else {
    result = callback(location, path);
  } 
  if (!result) return null;
  return __state.zokrates.ResolverResult.new(result.source, result.location);
}

export function resolveFromStdlib(location, path) {
  let key = appendExtension(getAbsolutePath(location, path), __extension);
  let source = stdlib[key];
  return source ? { source, location: key } : null;
}

export function getStdLib() {
  return stdlib;
}

export function compile(source, location) {
  if (typeof __state.zokrates === 'undefined') {
    throw new Error("You must call initialize() before calling this method")
  }
  return Uint8Array.from(__state.zokrates.compile(source, location));
}

export function computeWitness(program, args) {
  const input = JSON.stringify(Array.from(args));
  return __state.zokrates.compute_witness(Array.from(program), input);
}

export function setup(program) {
  let result = __state.zokrates.setup(Array.from(program));
  return { 
    vk: result.vk, 
    pk: Uint8Array.from(result.pk) 
  };
}

export function exportSolidityVerifier(verifyingKey, isAbiv2) {
  return __state.zokrates.export_solidity_verifier(verifyingKey, isAbiv2);
}

export function generateProof(program, witness, provingKey) {
  return __state.zokrates.generate_proof(Array.from(program), witness, Array.from(provingKey));
}